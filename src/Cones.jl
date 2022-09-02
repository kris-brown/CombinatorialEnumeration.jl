using Catlab.WiringDiagrams
using ..Sketches: add_id
using ..Models: frozen_hom

# Limits
########

function propagate_cones!(S::Sketch, J::SketchModel, f::CSetTransformation, ch::Change)
  # vcat([propagate_cone!(S, J, f, i, ch) for i in 1:length(S.cones)]...)
  verbose = false
  res = Change[]
  for (i,c) in enumerate(S.cones)
    legcond = any(l->!is_surjective(f[l]), vcat(elabel(c),vlabel(c)))
    if legcond || !([c.apex,vlabel(c)...]⊆J.frozen[1] && ((last.(c.legs) ∪ elabel(c)) ⊆ J.frozen[2]))
      append!(res, propagate_cone!(S, J, f, i, ch))
    else
      if verbose println("skipping cone $i w/ frozen $(J.frozen)") end
    end
  end
  res
end



"""
Propagate info related to a cone.

For example: a cone object D over a cospan B -> A <- C (i.e. a pullback)

Imagine all sets have three elements. If b₁ and b₂ are mapped to a₁ and c₁ and
c₂ are mapped to a₁ and a₂ (with c₃'s maps unknown), then a conjunctive query
looking for instances of the diagram should return:

QueryRes A  B  C
----------------
    1    a₁ b₁ c₁
    2    a₁ b₂ c₁

Because the functions are partial in the premodel, there may be limit objects
that will be discovered to exist (by merging elements or adding new connections)
So the query result is a *lower* bound on the number of elements in the apex.

This means we expect there to be at least two objects in the limit object D.
If an element already exists with the same legs, then we are good. Otherwise we
need to add a new element.

It would be great to search for patterns incrementally. However, even a basic
version of this (i.e. search for limits in a region that has 'changed') requires
*incremental graph pattern matching*, which is not yet implemented in Catlab. It
seems likely that there are even smarter kinds of search one can do depending on
whether it was a merge or an addition, but this has yet to be worked out.


If we merge together two apex elements, then we must merge together the
corresponding leg values.
---
If we merge together two cone diagram elements, then we may have to merge
together two apex elements. We may also create new limits (and have to create
new apex elements).
---
If we add an apex element, we need to determine if (including the rest of the
addition) it is possible for more limits to appear. If we really kept track of
all possible limits (given an uncertain diagram), then we could set the legs
(if there were exactly one), fail (if there were zero), otherwise do nothing.
A conservative approach now is to say that there are zero remaining possible
cones if the diagram is fully determinate (all FKs are known).
---
If we add *diagram* elements, new cones apex elements may be induced.
---

Unfortunately we do not use the fact we know the incremental change between
models to do this more intelligently.

If the apex and diagram objects/maps are frozen but not the legs, our query
results should match up one-to-one with apex elements. However, we may not know
how they should be matched, so the cone can actually generate a list of
possibilities to branch on (in addition to changes that must be executed).
- This isn't yet supported and will fail.

"""
function propagate_cone!(S::Sketch, J_::SketchModel, m::CSetTransformation,
                         ci::Int, ch::Change)
  res = Change[]
  cone_ = S.cones[ci]
  ap = cone_.apex
  idap = add_id(ap)
  J, M0 = J_.model, dom(m) # new / old model
  verbose = false

  if verbose
    println("updating cone $ap with m[apex] $(collect(m[ap]))")
    show(stdout,"text/plain", J)
    println(J_.eqs)
  end

  if (vlabel(cone_) ∪ [ap]) ⊆ J_.frozen[1] && elabel(cone_) ⊆ J_.frozen[2] && last.(cone_.legs) ⊈ J_.frozen[2]
    msg = "Frozen $(J_.frozen) apex $ap vs $(vlabel(cone_)) es $(elabel(cone_))"
    error("Cones w/ frozen apex + diagram but unfrozen legs unsupported\n$msg")
  end

  # Merged cone elements induced merged values along their legs
  cones = DefaultDict{Vector{Int},Vector{Int}}(()->Int[])
  for c in parts(J_.model, ap)
    pre = preimage(m[ap], c)
    if length(pre) > 1
      for legedge in filter(!=(idap),cone_.ulegs)
        tgttab = tgt(S, legedge)
        legvals = Set([find_root!(J_.eqs[tgttab], m[tgttab](fk(S,M0, legedge,p)))
                      for p in pre])
        if length(legvals) > 1
          str = "merging leg ($ap -> $legedge -> $tgttab) vals  $legvals"
          if verbose  println(str) end
          push!(res, Merge(S,J_,Dict([tgttab=>[legvals]])))
        end
      end
    end
    quot_legs = map(last.(cone_.legs)) do x
      y = x == idap ? c : fk(S,J_,x,c)
      return isnothing(y) ? nothing : find_root!(J_.eqs[tgt(S,x)],y)
    end
    if !any(isnothing, quot_legs)
      push!(cones[quot_legs], c)
    end
  end

  # Merged leg values induced merged cone elements
  for quot_cones in filter(x->length(x)>1, collect(values(cones)))
    eqcs = collect(Set([find_root!(J_.eqs[ap],x) for x in quot_cones]))
    if length(eqcs) > 1
      if verbose println("Merging cone apexes $eqcs") end
      push!(res, Merge(S,J_, Dict([ap=>[eqcs]])))
    end
  end

  # UNDERESTIMATE of cones in the new model
  if nv(cone_.d) == 0
    length(cones)==1 || throw(ModelException("Wrong number of 1 objects"))
    return res
  end

  sums = Addition[]
  query_res = nv(cone_.d) == 0 ? () : query(J, cone_.uwd)

  mult_legs = collect(filter(x->length(x) > 1, collect(values(cone_.leg_inds))))

  new_cones = Dict{Vector{Int},Union{Nothing,Int}}()
  for qres_ in unique(collect.(zip(query_res...)))
    skip = false
    qres = [find_root!(J_.eqs[tgt(S,l)], qres_[i]) for (i,l) in cone_.legs]
    if verbose println("qres_ $qres_ qres $qres") end

    mult_leg_viol = [vs for vs in mult_legs if length(unique(qres_[vs])) > 1]
    if !isempty(mult_leg_viol)
      skip |= true
      if all(l->frozen_hom(S,J_,l), last.(cone_.legs)) && !haskey(cones,qres)
        ls = last.([first(cone_.legs[vs]) for vs in mult_leg_viol])
        throw(ModelException("Identical legs $ls should point to same element: qres_ $qres_"))
      end
    end

    if skip continue end
    # Add a new cone if not seen before
    if !haskey(cones, qres)
      I, L = S.crel(), S.crel()
      IJd, ILd = [DefaultDict(()->Int[]) for _ in 1:2]
      add_part!(L, ap)
      lrmap = Dict{Pair{Symbol, Int}, Int}()
      for (res_v, l) in filter(x->x[2]!=idap,collect(zip(qres, last.(cone_.legs))))
        ls, lt = add_srctgt(l)
        legtab = tgt(S,l)
        lr = legtab=>res_v
        if haskey(lrmap, lr)
          tr = lrmap[lr]
        else
          add_part!(I, legtab)
          tr = add_part!(L, legtab)
          push!(IJd[legtab], res_v)
          push!(ILd[legtab], tr)
          lrmap[lr] = tr
        end
        add_part!(L, l; Dict([ls=>1,lt=>tr])...)
      end
      IJ = ACSetTransformation(I, J; IJd...)
      IL = ACSetTransformation(I, L; ILd...)
      if verbose println("Adding a new cone with legs $qres") end
      push!(sums, Addition(S, J_, IL, IJ))
      new_cones[qres] = nothing
    end
  end
  if !isempty(sums)
    push!(res, merge(S,J_, sums))
  end
  res
end
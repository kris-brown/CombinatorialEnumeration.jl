using Catlab.WiringDiagrams

# Limits
########

propagate_cones!(S::Sketch, J::SketchModel, f::CSetTransformation, ch::Change) =
  vcat([propagate_cone!(S, J, f, i, ch) for i in 1:length(S.cones)]...)



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

Things to think about:
- is it better to put all the generate cones in one big Addition or to break it
  up into smaller Additions?
"""
function propagate_cone!(S::Sketch, J_::SketchModel, m::CSetTransformation,
                         ci::Int, ch::Change)
  res = Change[]
  cone_ = S.cones[ci]
  ap = cone_.apex
  J, M0 = J_.model, dom(m) # new / old model
  verbose = false
  # Short circuit if change does not merge/add anything in the cone diagram
  if all(v->nparts(apex(ch), v)==nparts(codom(ch.l), v),
         unique([ap, last.(cone_.legs)...,elabel(cone_)...,vlabel(cone_)...]))
    if verbose
      println("short circuiting cone $ap w/ change $ch ($(components(ch.l)))")
    end
    return res
  end

  if verbose
    println("updating cone $ap with m[apex] $(collect(m[ap]))")
    show(stdout,"text/plain", crel_to_cset(S,J)[1])
    println(J_.eqs)
  end

  # Merged cone elements induced merged values along their legs
  cones = DefaultDict{Vector{Int},Vector{Int}}(()->Int[])
  for c in parts(J_.model, ap)
    pre = preimage(m[ap], c)
    if length(pre) > 1
      for legedge in unique(last.(cone_.legs))
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
    quot_legs = map(unique(last.(cone_.legs))) do x
      y = fk(S,J_,x,c)
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
    length(cones)==1 || error()
    return res
  end

  sums = Addition[]
  query_res = nv(cone_.d) == 0 ? () : query(J, cone_.uwd)

  new_cones = Dict{Vector{Int},Union{Nothing,Int}}()
  for qres_ in unique(collect.(zip(query_res...)))
    qres = [find_root!(J_.eqs[tgt(S,l)],y)
            for (y,l) in zip(qres_, unique(last.(cone_.legs)))]
    if verbose println("qres_ $qres_ qres $qres") end
    # Add a new cone if not seen before
    if !haskey(cones, qres)
      I, R = S.crel(), S.crel()
      IJd, IRd = [DefaultDict(()->Int[]) for _ in 1:2]
      add_part!(R, ap)
      lrmap = Dict{Pair{Symbol, Int}, Int}()
      for (res_v, l) in zip(qres, unique(last.(cone_.legs)))
        ls, lt = add_srctgt(l)
        legtab = tgt(S,l)
        lr = legtab=>res_v
        if haskey(lrmap, lr)
          tr = lrmap[lr]
        else
          add_part!(I, legtab)
          tr = add_part!(R, legtab)
          push!(IJd[legtab], res_v)
          push!(IRd[legtab], tr)
          lrmap[lr] = tr
        end
        add_part!(R, l; Dict([ls=>1,lt=>tr])...)
      end
      IJ = ACSetTransformation(I, J; IJd...)
      IR = ACSetTransformation(I, R; IRd...)
      if verbose println("Adding a new cone with legs $qres") end
      push!(sums, Addition(S, J_, IR, IJ))
      new_cones[qres] = nothing
    end
  end
  if !isempty(sums)
    push!(res, merge(S,J_, sums))
  end
  res
end
using Catlab

using Catlab.Programs.RelationalPrograms: parse_relation_context, parse_relation_call, parse_relation_diagram
using Catlab.WiringDiagrams
using DataStructures
using IterTools

include(joinpath(@__DIR__, "../../CSetAutomorphisms.jl/src/CSetAutomorphisms.jl"))
include(joinpath(@__DIR__, "FLS.jl"))
include(joinpath(@__DIR__, "DB.jl"))



"""
Initialize a relation on a schema from either a model or a dict of cardinalities
for each object.
"""
function initrel(F::FLS,
               I::Union{Nothing, Dict{Symbol, Int}, StructACSet}=nothing,
               )::StructACSet
  if !(I isa StructACSet)
    dic = I
    I = grph_to_cset(F.name, F.schema)
    for (k, v) in (dic === nothing ? [] : collect(dic))
      add_parts!(I, k, v)
    end
  end
  J = grph_to_crel(F.name, F.schema)
  # Initialize data in J from I
  for o in F.schema[:vlabel]
    add_parts!(J, o, nparts(I, o))
  end
  for d in F.schema[:elabel]
    hs, ht = add_srctgt(d)
    for (i, v) in filter(x->x[2]!=0, collect(enumerate(I[d])))
      n = add_part!(J, d)
    set_subpart!(J, n, hs, i)
    set_subpart!(J, n, ht, v)
    end
  end
  return J
end

const EqClass = Dict{Symbol, IntDisjointSets}

"""
Do a chase step: TGDs, then cones + EGDs for each branch
"""
function chasestep(F::FLS, J::StructACSet)::Vector{StructACSet}
  res = []
  for x in apply_tgds(F, J) # could be done in parallel
    e = apply_cones!(F,x)
    apply_egds!(F,x,e)
    merge!(F, x, e)
    push!(res, x)
  end
  return res
end

"""
# Action α: add new elements when a function is dangling

Fire TGDs in all possible ways (plus the 'free' way which uses fresh variables).
This produces new premodels to chase.
"""
function apply_tgds(F::FLS, J::StructACSet)::Vector{StructACSet}
  res = StructACSet[]
  srcs, tgts = [F.schema[:vlabel][F.schema[x]] for x in [:src, :tgt]]
  # Calculate how many missing things we need of each type
  needs = [(d, nparts(J, dtgt),
            collect(setdiff(parts(J, ddom), J[add_srctgt(d)[1]])))
           for (d, ddom, dtgt) in zip(F.schema[:elabel], srcs, tgts)]
  lens = [length(x) for (_,_,x) in needs]
  csum = Dict(zip(F.schema[:elabel],zip(lens,vcat([0],cumsum(lens)[1:end-1]))))
  # branch on cartesian product of possibilities. 0 means fresh.
  for choice in IterTools.product(vcat([repeat([0:n], length(x))
                                        for (_, n, x) in needs]...)...)
    Jc = deepcopy(J)
    for (e, src, tgt, (_,_,eneed)) in zip(F.schema[:elabel], srcs, tgts, needs)
      esrc, etgt = add_srctgt(e)
      len, offset = csum[e]
      echoices = len == 0 ? [] : choice[1+offset:offset+len]
      for (x, echoice) in zip(eneed, echoices)
        if echoice == 0
          gx = add_part!(Jc, tgt) # add a fresh symbol
          add_part!(Jc, e; Dict([esrc=>x, etgt=>gx])...)
        else
          add_part!(Jc, e; Dict([esrc=>x, etgt=>echoice])...)
        end
      end
    end
    push!(res, Jc)
  end
  return res
end


"""
Query that returns all instances of the base pattern. External variables
are labeled by the legs of the cone.
"""
function cone_query(c::Cone)::StructACSet
  vars = [Symbol("x$i") for i in nparts(c.d, :V)]
  typs = ["$x(_id=x$i)" for (i, x) in enumerate(c.d[:vlabel])]
  bodstr = vcat(["begin"], typs)
  for (e, s, t) in zip(c.d[:elabel], c.d[:src], c.d[:tgt])
    push!(bodstr, "$e(src_$e=x$s, tgt_$e=x$t)")
  end
  push!(bodstr, "end")
  exstr = "($(join(["$v=x$k" for vs in values(vars) for (k,v) in c.legs],",") ))"
  ctxstr = "($(join(vcat(["x$i::$x" for (i, x) in enumerate(c.d[:vlabel])],),",")))"
  ex  = Meta.parse(exstr)
  ctx = Meta.parse(ctxstr)
  hed = Expr(:where, ex, ctx)
  bod = Meta.parse(join(bodstr, "\n"))
  # println("ex $exstr\n ctx $ctxstr\n bod $(join(bodstr, "\n"))")
  res = parse_relation_diagram(hed, bod)
  return res
end

"""
Action αlim: add new elements OR quotient due to cones. Modifies J.
"""
function apply_cones!(F::FLS, J::StructACSet)::EqClass
  eqclasses = EqClass([o=>IntDisjointSets(nparts(J, o))
                      for o in F.schema[:vlabel]])

  newstuff = []
  for cone in F.cones # could be done in parallel
    cones = Dict()
    # precompute existing cones
    for i in parts(J, cone.apex)
      v = [only(incident(J, i, add_srctgt(e)[1])) for e in values(cone.legs)]
      if haskey(cones, v)
        union!(eqclasses[cone.apex], i, cones[v])
      else
        cones[v] = i
      end
    end

    # look for instances of the pattern (TODO cached version / only considered 'added' information)
    for res in query(J, cone_query(cone)) # rely on order by same as order when precomputing
      if !haskey(collect(res), cones)
        newapex = add_part!(J, cone.apex)
        push!(eqclasses[cone.apex])
        for (val, e) in zip(res,values(cone.legs))
          s,t = add_srctgt(e)
          push!(newstuff, e=>Dict([s=>newapex, t=>val]))
        end
      end
    end
  end
  for (e, d) in newstuff
    add_part!(J, e; d...)
  end
  return eqclasses
end


function eval_path(pth::Vector{Symbol}, J::StructACSet, xs::Set{Int})::Set{Int}
  # Iteratively update X to Y by searching through all (x,y) in R ⊆ X×Y
  for m in pth
    msrc, mtgt = add_srctgt(m)
    if isempty(xs)
      return xs
    else
      newxs = Set{Int}()
      for (jx, jy) in zip(J[msrc], J[mtgt])
        if jx ∈ xs
          push!(newxs, jy)
        end
      end
      xs = newxs
    end
  end
  return xs
end

"""Modifies eq"""
function apply_egds!(F::FLS, J::StructACSet, eqclasses::EqClass)
  verbose = true
  # Action βd: add all coincidences induced by D (i.e. fire EGDs)
  for (p, q) in F.eqs # could be done in parallel
    root = F.schema[:vlabel][F.schema[:src][
      only(incident(F.schema, p[1], :elabel))]]
    tail = F.schema[:vlabel][F.schema[:tgt][
        only(incident(F.schema, p[end], :elabel))]]
    for x in parts(J, root)
      for px in eval_path(p, J, Set([x]))
        for qx in (isempty(q) ? [x] : eval_path(q, J, Set([x])))
          union!(eqclasses[tail], px, qx)
          if verbose && px != qx
            println("βF: $p=$q MERGED $tail $px = $qx")
          end
        end
      end
    end
  end

  # Action δ: add all coincidences induced by functionality
  srcs, tgts = [F.schema[:vlabel][F.schema[x]] for x in [:src, :tgt]]

  for (d, ddom, dcodom) in zip(F.schema[:elabel], srcs, tgts) # could be done in parallel
    dsrc, dtgt = add_srctgt(d)
    for x in parts(J, ddom)
      eq_ys = collect(Set(J[dtgt][incident(J, x, dsrc)]))
      for (y1, y2) in zip(eq_ys, eq_ys[2:end])
        union!(eqclasses[dcodom], y1, y2)
        if verbose
          println("δ: $d($ddom#$x) MERGED $dcodom $y1 = $y2")
        end
      end
    end
  end
end

"""
Action γ: merge coincidentally equal elements. Modifies J.
"""
function merge!(F::FLS, J::StructACSet, eqclasses::EqClass)::Nothing
  verbose=true
  μ = Dict{Symbol, Vector{Pair{Int,Int}}}([o=>Pair{Int,Int}[] for o in F.schema[:vlabel]])
  delob = Dict{Symbol, Vector{Int}}([o=>Int[] for o in F.schema[:vlabel]])
  for (o, eq) in pairs(eqclasses)
    eqsets = Dict{Int,Set{Int}}()
    # Recover the equivalence classes from the union-find structure
    for x in parts(J, o)
    eqrep = find_root(eq, x)
    if haskey(eqsets, eqrep)
      push!(eqsets[eqrep], x)
    else
      eqsets[eqrep] = Set([x])
    end
    end
    if verbose
      println("eqset $o $(values(eqsets))")
    end
    # Minimum element is the representative
    for vs in values(eqsets)
    m = minimum(vs)
    delete!(vs, m)
    append!(μ[o], [v=>m for v in vs])
    append!(delob[o], collect(vs))
    end
  end
  # Replace all instances of a class with its representative in J
  srcs, tgts = [F.schema[:vlabel][F.schema[x]] for x in [:src, :tgt]]

  for (d, ddom, dcodom) in zip(F.schema[:elabel], srcs, tgts) # could be done in parallel
    dsrc, dtgt = add_srctgt(d)
    isempty(μ[ddom]) || set_subpart!(J, dsrc, replace(J[dsrc], μ[ddom]...))
    isempty(μ[dcodom]) || set_subpart!(J, dtgt, replace(J[dtgt], μ[dcodom]...))
    # remove redundant duplicate relation rows
    seen = Set()
    for (i, st) in enumerate(zip(J[dsrc], J[dtgt]))
    if st ∈ seen
      rem_part!(J, d, i)
    else
      push!(seen, st)
    end
    end
  end
  for (o, vs) in collect(delob)
    isempty(vs) || rem_parts!(J, o, sort(vs))
  end
end


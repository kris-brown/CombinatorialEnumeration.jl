using Catlab

using Catlab.Programs.RelationalPrograms: parse_relation_context, parse_relation_call, parse_relation_diagram
using Catlab.WiringDiagrams
using DataStructures
using IterTools
using Combinatorics

include(joinpath(@__DIR__, "FLS.jl"))
include(joinpath(@__DIR__, "DB.jl"))

const EqClass = Dict{Symbol, IntDisjointSets}
const ACDict = Dict{UInt64, StructACSet}

"""
Do a chase step: TGDs, then cones + EGDs for each branch
"""
function chasestep(F::FLS, J::StructACSet)::Pair{ACDict, ACDict}
  res, completed, srcs = ACDict(), ACDict(), F.schema[:vlabel][F.schema[:src]]
  for x in apply_tgds(F, J) # could be done in parallel
    e, changed = apply_cones!(F,x)
    changed |= apply_egds!(F,x,e)
    if changed || any([nparts(x, src)!=nparts(x,e) for (e, src) in
                       zip(F.schema[:elabel], srcs)])
      merge!(F, x, e)
      xhsh = canonical_hash(x)
      res[xhsh] = x
    else
      completed[canonical_hash(x)] = x
    end
  end
  return res => completed
end

"""Take a premodel from the DB and generate a set of models and premodels
Insert these results into the DB
"""
function chasestep_db(db::SQLite.DB, F::FLS, i::Int
                     )::Pair{Vector{Int}, Vector{Int}}
  # check if we've already chased before
  if Bool(SQLite.getvalue(execute(db, "SELECT fired FROM Premodel WHERE Premodel_id=?",
                             [i]),1,Int))
    println("ALREADY CHASED!")
    children = (execute(db, "SELECT child FROM Parent WHERE parent=?",[i]
                        ) |> DataFrame)[!,:child]
    modelchildren = (execute(db, """SELECT Premodel_id FROM Premodel JOIN Model
      USING (Premodel_id) WHERE Premodel_id IN ($(join(children, ",")))"""
      ) |> DataFrame)[!,:Premodel_id]
    return setdiff(children, modelchildren) => modelchildren
  end
  m, I = get_premodel(db, i)
  xs, ys = chasestep(m, I)
  pminds, minds = Int[], Int[]
  for (xhsh, x) in xs
    push!(pminds, add_premodel(db, F, x, i, xhsh))
  end
  for (yhsh, y) in ys
    push!(minds, add_model(db, F, y, i, yhsh))
  end
  execute(db, "UPDATE Premodel SET fired = true WHERE Premodel_id = ?", [i])
  return pminds => minds
end

"""
1. Enumerate elements of ℕᵏ for an underlying graph with k nodes.
2. For each of these: (c₁, ..., cₖ) create a term model with that many constants

Do the first enumeration by incrementing n_nonzero and finding partitions so
that ∑(c₁,...) = n_nonzero

In the future, this function will write results to a database
that hashes the FLS as well as the set of constants that generated the model.

Also crucial is to decompose FLS into subparts that can be efficiently solved
and have solutions stitched together.
"""
function combos_below(m::Int, n::Int)::Vector{Vector{Int}}
  res = Set{Vector{Int}}([zeros(Int,m)])
  n_const = 0 # total number of constants across all sets
  for n_const in 1:n
    for n_nonzero in 1:m
      # values we'll assign to nodes
      c_parts = partitions(n_const, n_nonzero)
      # Which nodes we'll assign them to
      indices = permutations(1:m,n_nonzero)
      for c_partition in c_parts
        for index_assignment in indices
          v = zeros(Int, m)
          v[index_assignment] = vcat(c_partition...)
          push!(res, v)
        end
      end
    end
  end
  return sort(collect(res))
end


"""
Find all models below a certain cardinality.
"""
function chase_below(db::SQLite.DB, F::FLS, n::Int,
                     nmax::Union{Nothing, Int}=nothing)
  unchased, res, nmax  = Set{Int}(), Set{Int}(), nmax===nothing ? n + 10 : n
  m = length(realobs(F))
  for combo in combos_below(m, n)
    push!(unchased, init_premodel(db, F, combo))
  end
  seen = get_seen(db, F)
  while !isempty(unchased)
    println("# unchased: $(length(unchased))")
    mdl = pop!(unchased)
    msize = SQLite.getvalue(execute(db,
      "SELECT size FROM Premodel WHERE Premodel_id=?",[mdl]), 1, Int)
    println("chasing $mdl with size $msize")
    Ks, Ms = chasestep_db(db, F, mdl)
    function getidsize(x::Int)::Pair{UInt64, Int}
      z = execute(db, "SELECT hash,size FROM Premodel WHERE Premodel_id=?",[x])
      return SQLite.getvalue(z,1,Int) => SQLite.getvalue(z,2,Int)
    end
    filter!(k->let (i,s)=getidsize(k); i ∉ seen && (s < nmax) end, Ks)

    union!(seen, Ks)
    union!(unchased, Ks)
    union!(res, Ms)
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
  exstr = "($(join(["$(v)_$i=x$k" for vs in values(vars) for (i, (k,v)) in enumerate(c.legs)],",") ))"
  ctxstr = "($(join(vcat(["x$i::$x" for (i, x) in enumerate(c.d[:vlabel])],),",")))"
  ex  = Meta.parse(exstr)
  ctx = Meta.parse(ctxstr)
  hed = Expr(:where, ex, ctx)
  bod = Meta.parse(join(bodstr, "\n"))
  # println("ex $exstr\n ctx $ctxstr\n bod $(join(bodstr, "\n"))")
  res = parse_relation_diagram(hed, bod)
  return res
end

"""Add new elements OR quotient due to cones. Modifies J."""
function apply_cones!(F::FLS, J::StructACSet)::Pair{EqClass, Bool}
  eqclasses = EqClass([o=>IntDisjointSets(nparts(J, o))
                      for o in F.schema[:vlabel]])
  changed, verbose = false, false
  newstuff = []
  for cone in F.cones # could be done in parallel
    cones = Dict{Vector{Int},Int}()
    ltgts = [J[add_srctgt(e)[2]] for (_, e) in cone.legs]
    length(Set(collect(map(length, ltgts)))) == 1 || error(ltgts)
    # precompute existing cones
    for (i, v) in enumerate(map(collect,zip(ltgts...)))
      if haskey(cones, v)
        changed = true
        union!(eqclasses[cone.apex], i, cones[v])
      elseif minimum(v) > 0
        cones[v] = i
      end
    end
    if verbose && !isempty(cones) println("preexisting cones $(cones)") end
    # look for instances of the pattern (TODO cached version / only considered 'added' information)
    for res in query(J, cone_query(cone)) # rely on order by same as order when precomputing
      resv = Vector{Int}(collect(res))
      if verbose println("res $resv $(collect(keys(cones)))") end
      if !haskey(cones, resv)
        if verbose println("is new") end
        changed = true
        newapex = add_part!(J, cone.apex)
        push!(eqclasses[cone.apex])
        for (val, (_, e)) in zip(res,cone.legs)
          s,t = add_srctgt(e)
          push!(newstuff, e=>Dict([s=>newapex, t=>val]))
        end
      end
    end
  end
  for (e, d) in newstuff
    if minimum(values(d)) == 0 println(newstuff ,J ) end
    add_part!(J, e; d...)
  end
  return eqclasses => changed
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
function apply_egds!(F::FLS, J::StructACSet, eqclasses::EqClass)::Bool
  verbose,changed = false, false
  # Path equalities
  for (p, q) in F.eqs # could be done in parallel
    root = F.schema[:vlabel][F.schema[:src][
      only(incident(F.schema, p[1], :elabel))]]
    tail = F.schema[:vlabel][F.schema[:tgt][
        only(incident(F.schema, p[end], :elabel))]]
    for x in parts(J, root)
      for px in eval_path(p, J, Set([x]))
        for qx in (isempty(q) ? [x] : eval_path(q, J, Set([x])))
          union!(eqclasses[tail], px, qx)
          changed |= px != qx
          if verbose && px != qx
            println("βF: $p=$q MERGED $tail $px = $qx")
          end
        end
      end
    end
  end

  # Functionality
  srcs, tgts = [F.schema[:vlabel][F.schema[x]] for x in [:src, :tgt]]

  for (d, ddom, dcodom) in zip(F.schema[:elabel], srcs, tgts) # could be done in parallel
    dsrc, dtgt = add_srctgt(d)
    for x in parts(J, ddom)
      eq_ys = collect(Set(J[dtgt][incident(J, x, dsrc)]))
      for (y1, y2) in zip(eq_ys, eq_ys[2:end])
        changed |= true
        union!(eqclasses[dcodom], y1, y2)
        if verbose
          println("δ: $d($ddom#$x) MERGED $dcodom $y1 = $y2")
        end
      end
    end
  end
  return changed
end

"""Use equivalence class data to reduce size of model"""
function merge!(F::FLS, J::StructACSet, eqclasses::EqClass)::Nothing
  verbose=false
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
    filter!(p->length(last(p))>1, eqsets)
    if verbose && !isempty(eqsets)
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


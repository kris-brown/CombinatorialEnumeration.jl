include(joinpath(@__DIR__, "Sketch.jl"))
using DataStructures
using AutoHashEquals

"""Functions for the manipulation of models/premodels"""
const EqClass = Dict{Symbol, IntDisjointSets}
const NewStuff = DefaultDict{Symbol, Int}
const UpdateStuff = Tuple{Symbol, Int, Int}
const MergeStuff = Tuple{Symbol, Int, Int}
const IType = Union{Nothing, Vector{Pair{Symbol, Int}}, StructACSet}

# Modify
########
@auto_hash_equals mutable struct Modify
  newstuff::NewStuff
  update::Vector{UpdateStuff}
  #merge::Vector{MergeStuff}
end
function Modify()
  return Modify(NewStuff(()->0), UpdateStuff[])
end

Base.isempty(m::Modify)::Bool = sum(values(m.newstuff))==0 && isempty(m.update)
function Base.union(S::Sketch, J::StructACSet, xs::Vector{Modify})::Modify
  if length(xs) == 0 return Modify()
  elseif length(xs) == 1 return only(xs)
  else
    m = union(S,J,xs[1],xs[2])
    for m_next in xs[3:end]
      m = union(S, J, m, m_next)
    end
  return m
  end
end

function Base.union(S::Sketch, J::StructACSet, x::Modify, y::Modify)::Modify
  res = deepcopy(x)
  for (key, yval) in pairs(y.newstuff)
    res.newstuff[key]+= yval
  end
  # UPDATE THE REFERENCES IN Y.UPDATE THAT POINT TO Y.NEWSTUFF
  for u in y.update
    (f, i, j) = u
    mk_new(tab::Symbol, ind::Int) = ind + (
      ind > nparts(J, tab) ? x.newstuff[tab] : 0)
    push!(res.update, (f, mk_new(src(S, f), i), mk_new(tgt(S, f), j)))
  end
  return res
end

"""
Factor modify information into that which extends the ACSet and that which does
not.
"""
function split_modify(S::Sketch, J::StructACSet, m::Modify
                     )::Pair{Modify, Modify}
  new_m, old_m = Modify(m.newstuff, UpdateStuff[]), Modify()
  for u in m.update
    (f, i, j) = u
    if  i > nparts(J, src(S, f)) || j > nparts(J, tgt(S, f))
      push!(new_m.update, u)
    else
      push!(old_m.update, u)
    end
  end
  return new_m => old_m
end
# Generic helpers
#################
function mk_pairs(v::Vector{Tuple{T1,T2}})::Vector{Pair{T1,T2}} where {T1,T2}
  [a=>b for (a,b) in v]
end
# Helper for IntDisjointSets
############################
"""
Get the equivalence classes out of an equivalence relation. Pick the lowest
value as the canonical representative. By default, filter to remove singletons.
"""
function eq_sets(eq::IntDisjointSets; remove_singles::Bool=false)::Set{Set{Int}}
  eqsets = DefaultDict{Int,Set{Int}}(Set{Int})
  for i in 1:length(eq)
    push!(eqsets[find_root!(eq, i)], i)
  end
  filt = v -> !(remove_singles && length(v)==1)
  return Set(filter(filt, collect(values(eqsets))))
end

"""
Pick root element from each equivalence class
Possible alternative: use `minimum` instead
"""
eq_reps(eq::IntDisjointSets)::Vector{Int} =
  [find_root!(eq, first(s)) for s in eq_sets(eq; remove_singles=false)]

"""Union more than two elements, pairwise. Return the pairs used."""
function unions!(eq::IntDisjointSets, vs::Vector{Int})::Vector{Pair{Int,Int}}
  ps = length(vs) > 1 ? [x=>y for (x,y) in zip(vs, vs[2:end])] : Pair{Int,Int}[]
  for (v1, v2) in ps
    union!(eq, v1, v2)
  end
  return ps
end

ids_eq(e1::IntDisjointSets, e2::IntDisjointSets)::Bool =
  eq_sets(e1) == eq_sets(e2)

eqclass_eq(e1::EqClass, e2::EqClass)::Bool =
  Set(keys(e1))==Set(keys(e2)) && all([ids_eq(e1[k],e2[k]) for k in keys(e1)])


"""Apply table-indexed equivalence relation to a vector of values (with an
equal-length vector of tables)"""
function eq_vec(eqclass::EqClass, tabs::Vector{Symbol}, inds::Vector{Int})
  length(tabs) == length(inds) || error("eq_vec needs equal length tabs/inds")
  [find_root!(eqclass[t], i) for (t, i) in zip(tabs, inds)]
end

"""Initialize equivalence classes for a premodel"""
function init_eq(S::Sketch, J::StructACSet)::EqClass
  EqClass([o=>IntDisjointSets(nparts(J, o)) for o in S.schema[:vlabel]])
end

# Premodel/Model conversion
###########################
"""
Convert a premodel (C-Rel) to a model C-Set.
Elements that are not mapped by a relation are given a target value of 0.
If this happens at all, an output bool will be true
If the same element is mapped to multiple outputs, an error is thrown.
"""
function crel_to_cset(S::Sketch, J::StructACSet)::Pair{StructACSet, Bool}
  res = S.cset() # grph_to_cset(S.name, S.schema)
  for o in S.schema[:vlabel]
    add_parts!(res, o, nparts(J, o))
  end
  partial = false
  for m in S.schema[:elabel]
    msrc, mtgt = add_srctgt(m)
    length(J[msrc]) == length(Set(J[msrc])) || error("nonfunctional $J")
    partial |= length(J[msrc]) != nparts(J, src(S, m))
    for (domval, codomval) in zip(J[msrc], J[mtgt])
      set_subpart!(res, domval, m, codomval)
    end
  end
  return res => partial
end

"""
Create a premodel (C-Rel) from either
 - a model
 - a dict of cardinalities for each object (all map tables empty)
 - nothing (empty C-Rel result)
"""
function create_premodel(S::Sketch, I::IType=nothing)::StructACSet
  if !(I isa StructACSet)
    dic = deepcopy(I)
    I = S.cset()
    for (k, v) in (dic === nothing ? [] : dic)
      add_parts!(I, k, v)
    end
  end
  J = S.crel() # grph_to_crel(S.name, S.schema)
  # Initialize data in J from I
  for o in S.schema[:vlabel]
    add_parts!(J, o, nparts(I, o))
  end
  for d in S.schema[:elabel]
    hs, ht = add_srctgt(d)
    for (i, v) in filter(x->x[2]!=0, collect(enumerate(I[d])))
      n = add_part!(J, d)
    set_subpart!(J, n, hs, i)
    set_subpart!(J, n, ht, v)
    end
  end
  return J
end

# Modifying CSets
##################
"""Use equivalence class data to reduce size of a premodel"""
function merge!(S::Sketch, J::StructACSet, eqclasses::EqClass)::Nothing
  verbose = false
  # Initialize a function mapping values to their new (quotiented) value
  μ = Dict{Symbol, Vector{Pair{Int,Int}}}([
    o=>Pair{Int,Int}[] for o in S.schema[:vlabel]])

  # Initialize a record of which values are to be deleted
  delob = DefaultDict{Symbol, Vector{Int}}(Vector{Int})

  # Populate `μ` and `delob` from `eqclasses`
  for (o, eq) in pairs(eqclasses)
    eqsets = eq_sets(eq; remove_singles=true)
    # Minimum element is the representative
    for vs in map(collect,collect(values(eqsets)))
      m = minimum(vs)
      vs_ = [v for v in vs if v!=m]
      append!(μ[o], [v=>m for v in vs_])
      append!(delob[o], collect(vs_))
    end
  end

  # Replace all instances of a class with its representative in J
  for d in S.schema[:elabel] # could be done in parallel
    dsrc, dtgt = add_srctgt(d)
    μsrc, μtgt = μ[src(S, d)], μ[tgt(S, d)]
    isempty(μsrc) || set_subpart!(J, dsrc, replace(J[dsrc], μsrc...))
    isempty(μtgt) || set_subpart!(J, dtgt, replace(J[dtgt], μtgt...))
  end

  # Detect redundant duplicate relation rows
  for d in S.schema[:elabel] # could be done in parallel
    dsrc, dtgt = add_srctgt(d)
    seen = Set{Tuple{Int,Int}}()
    for (i, st) in enumerate(zip(J[dsrc], J[dtgt]))
      if st ∈ seen
        push!(delob[d], i)
      else
        push!(seen, st)
      end
    end
  end
  # Remove redundant duplicate relation rows
  for (o, vs) in collect(delob)
    isempty(vs) || rem_parts!(J, o, sort(vs))
  end
end


"""
Apply the additions updates specified in a Modify to a CSet (creates a copy)

Because some updates may refer to indices that only exist with the additions,
we do the additions first."""
function update_crel(J::StructACSet, modify::Modify)::StructACSet
  nw, up = modify.newstuff, modify.update
  J_ = deepcopy(J)
  for (ob, i) in pairs(nw)
      add_parts!(J_, ob, i)
  end
  for (homname, s, t) in up
    # println("adding $homname: $s => $t")
    hsrc, htgt = add_srctgt(homname)
    add_part!(J_, homname; Dict([hsrc=>s,htgt=>t])...)
  end
  return J_
end

add_rel!(J::StructACSet, f::Symbol, i::Int, j::Int) =
  add_part!(J, f; Dict(zip(add_srctgt(f), [i,j]))...)


# Querying CRel
################
function has_map(J::StructACSet, f::Symbol, x::Int, y::Int)::Bool
  from_map, to_map = add_srctgt(f)
  return (x,y) ∈ collect(zip(J[from_map], J[to_map]))
end
"""Check for map, modulo equivalence"""
function has_map(S::Sketch, J::StructACSet, f::Symbol, x::Int, y::Int,
                 eq::EqClass)::Bool
  from_map, to_map = add_srctgt(f)
  s, t = src(S, f), tgt(S, f)
  s_eq = i -> find_root!(eq[s], i)
  t_eq = i -> find_root!(eq[t], i)
  st = (s_eq(x), t_eq(y))
  return st ∈ collect(zip(s_eq.(J[from_map]), t_eq.(J[to_map])))
end
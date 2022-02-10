
module Models
export EqClass, NewElem, NewStuff, Modify, mk_pairs, eq_sets, eq_dicts, eq_reps,
       update_crel!, has_map, create_premodel, crel_to_cset, init_eq,
       add_rel!, unions!, init_defined, update_defined!

"""
Functions for the manipulation of models/premodels
"""

using ..Sketches

using Catlab.CategoricalAlgebra
using DataStructures
using AutoHashEquals

import Base: merge!, show

# Data structures
#################
const EqClass = Dict{Symbol, IntDisjointSets}

mutable struct NewElem
  map_in  :: DefaultDict{Symbol, Vector{Int}}
  map_out :: Dict{Symbol, Int}
  function NewElem()
    return new(DefaultDict{Symbol, Vector{Int}}(()->Int[]), Dict{Symbol, Int}())
  end
end

function Base.show(io::IO, ne::NewElem)
  ins = collect(filter(kv->!isempty(kv[2]), pairs(ne.map_in)))
  outs = collect(pairs(ne.map_out))
  print(io, "NE(")
  if !isempty(ins)
      print(io, "{")
    for (k,v) in ins
      print(io, "$k:$v,")
    end
    print(io, "},")
  end
  if !isempty(outs)
    print(io, "{")
    for (k,v) in outs
      print(io, "$k:$v,")
    end
    print(io, "\b})")
  end
print(io, ")")
end

mutable struct NewStuff
  ns::DefaultDict{Symbol, Dict{Any, NewElem}}
  function NewStuff()
    return new(DefaultDict{Symbol, Dict{Any, NewElem}}(
                 ()->Dict{Any, NewElem}()))
  end
end

function Base.show(io::IO, ns::NewStuff)
  print(io, "NS("*(isempty(ns.ns) ? " " : ""))
  for (k,v) in filter(kv->!isempty(kv[2]), pairs(ns.ns))
    print(io, "$k:$v,")
  end
  print(io, "\b)")
end

const IType = Union{Nothing, Vector{Pair{Symbol, Int}}, StructACSet}

# Modify
########
@auto_hash_equals mutable struct Modify
  newstuff::NewStuff
  update::Set{Tuple{Symbol, Int, Int}}
end

function Modify()
  return Modify(NewStuff(), Set{Tuple{Symbol, Int, Int}}())
end

"""Mergy `y` into `x`"""
function Base.union!(x::NewStuff, y::NewStuff)
  for (tab, new_elems) in pairs(y.ns)
    for (k, ne) in pairs(new_elems)
      if haskey(x[tab], k)
        err = """Can't merge $x and $y because of $tab: $key
                 ... or should we merge the new elems???"""
        ne == x[tab][k] || error(err)
      else
        x[tab][k] = ne
      end
    end
  end
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
Get a function which maps an ACSet part to the minimum element of its eq class
"""
function eq_dicts(eq::EqClass)::Dict{Symbol, Dict{Int,Int}}
  res = Dict{Symbol, Dict{Int,Int}}()
  for (k, v) in pairs(eq)
    d = Dict{Int, Int}()
    for es in eq_sets(v)
      m = minimum(es)
      for e in es
        d[e] = m
      end
    end
    res[k] = d
  end
  return res
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
  init_eq([o=>nparts(J, o) for o in S.schema[:vlabel]])
end

function init_eq(v::Vector{Pair{Symbol, Int}})::EqClass
  EqClass([o=>IntDisjointSets(n) for (o, n) in v])
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
function merge!(S::Sketch, J::StructACSet, eqclasses::EqClass
               )::Dict{Symbol, Dict{Int,Int}}
  verbose = false
  # Initialize a function mapping values to their new (quotiented) value
  μ = eq_dicts(eqclasses)

  # Initialize a record of which values are to be deleted
  delob = DefaultDict{Symbol, Vector{Int}}(Vector{Int})

  # Populate `delob` from `eqclasses`
  for (o, eq) in pairs(eqclasses)
    eqsets = eq_sets(eq; remove_singles=true)
    # Minimum element is the representative
    for vs in map(collect,collect(values(eqsets)))
      m = minimum(vs)
      vs_ = [v for v in vs if v!=m]
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
  return μ
end


"""
Apply the additions updates specified in a NewStuff to a CSet
"""
function update_crel!(J::StructACSet, nw::NewStuff)
  for (ob, vs) in pairs(nw.ns)
    for n_e in values(vs)
      add_newelem!(J, ob, n_e)
    end
  end
end

function add_newelem!(J::StructACSet, ob::Symbol, n_e::NewElem)
  new_id = add_part!(J, ob)
  for (mo, moval) in pairs(n_e.map_out)
    d = Dict(zip(add_srctgt(mo), [new_id, moval]))
    add_part!(J, mo; d...)
  end
  for (mi, mivals) in pairs(n_e.map_in)
    for mival in mivals
      d = Dict(zip(add_srctgt(mi), [mival, new_id]))
      add_part!(J, mi; d...)
    end
  end
end


function update_crel!(S::Sketch, J::StructACSet, d::Defined, m::Modify)
  update_crel!(J, m.newstuff)
  for (k, i, j) in m.update
    add_rel!(S, J, d, k , i, j)
  end
end

function add_rel!(S::Sketch, J::StructACSet, d::Defined, f::Symbol, i::Int, j::Int)
  add_part!(J, f; Dict(zip(add_srctgt(f), [i,j]))...)
  update_defined!(S, J, d, f)
end

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
# Defined
#########
function init_defined(S::Sketch, J::StructACSet)::Defined
  d = free_obs(S) => Set{Symbol}()
  update_defined!(S, J, d)
  return d
end
"""
Return a new Defined object with updates:
- A hom that has a value for all elements of its domain
- A limit object that has all objects AND homs in its diagram defined
  (but only right after compute_cone! or compute_cocone! is run, so we do not
   handle that here)
Return whether a change was made or not
"""
function update_defined!(S::Sketch, J::StructACSet, d::Defined,
                         f::Union{Symbol,Nothing}=nothing)::Bool
  _, dhom = d
  changed = false
  for h in setdiff(isnothing(f) ? S.schema[:elabel] : [f], dhom)
    s = src(S,h)
    if s ∈ d[1] && isempty(setdiff(parts(J, s), J[add_srctgt(h)[1]]))
      push!(dhom, h)
      # println("$h is now defined! ")
      # show(stdout, "text/plain", crel_to_cset(S, J)[1])
      changed |= true
    end
  end
  return changed
end
end # module
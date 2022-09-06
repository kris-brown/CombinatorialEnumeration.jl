module DB
export init_db, init_premodel, add_premodel, get_model, EnumState, Prop,
       MergeEdge,AddEdge, Init, Branch
import ..Sketches: show_lg

"""
Interact an in-memory datastore

We formerly supported a postgres backend when the scale is beyond computer
memory (or we want to serialize results to be used much later).

This could be reimplemented if needed.
"""

using ..Sketches
using ..Models

using Catlab.CategoricalAlgebra
using CSetAutomorphisms


#############################

abstract type EdgeChange end
"""
No change is done to the input: these are just the additional changes that were
discovered while propagating an add/merge change
"""
struct MergeEdge  <: EdgeChange
  merge::Merge
  queued::Addition
  m::ACSetTransformation
end
struct AddEdge  <: EdgeChange
  add::Addition
  m::ACSetTransformation
end
struct Branch  <: EdgeChange
  add::Addition
  m::ACSetTransformation
end
struct Init <: EdgeChange
  add::Addition
  m::ACSetTransformation
end


to_symbol(::Init) = :I
to_symbol(::AddEdge) = :A
to_symbol(::MergeEdge) = :M
to_symbol(::Branch) = :B



# DB alternative: local memory
"""
grph - relation between models. Edges are either branch, add, or merge
premodels - partially filled out models, seen so far, indexed by their hash
pk - vector of hash values for each model seen so far
prop - vector of data that is generated from propagating constraints on a premodel
ms - a morphism for each edge
fail - subset of premodels which fail
models - subset of premodels which are complete. This can be less efficiently
         computed on the fly as models which
(to be used in the future)
fired - subset of *edges* which have been processed
to_branch - propagating constraints may give us something to branch on that's
            better than the generic 'pick a FK undefined for a particular input'
"""
mutable struct EnumState
  grph::LabeledGraph
  premodels::Vector{SketchModel}
  ms::Vector{EdgeChange}
  pk::Vector{String}
  fail::Set{Int}
  models::Set{Int}
  prop::Vector{Union{Nothing,Tuple{AuxData, Addition, Merge}}}
  # to_branch::Vector{Any}
  function EnumState()
    return new(LabeledGraph(),SketchModel[], EdgeChange[], String[],
               Set{Int}(), Set{Int}(), Any[])
  end
end

show_lg(es::EnumState) = show_lg(es.grph)
Base.length(es::EnumState) = length(es.premodels)
Base.getindex(es::EnumState, i::Int) = es.premodels[i]
Base.getindex(es::EnumState, i::String) = es.premodels[findfirst(==(i), es.pk)]

function add_premodel(es::EnumState, S::Sketch, J::SketchModel;
                      parent::Union{Nothing,Pair{Int,E}}=nothing)::Int where {E <: EdgeChange}

  naut = call_nauty(J.model)

  found = findfirst(==(naut.hsh), es.pk)
  if !isnothing(found)
    new_v = found
  else
    push!(es.premodels, J)
    push!(es.prop, nothing)
    push!(es.pk, naut.hsh)
    new_v = add_part!(es.grph, :V; vlabel=Symbol(string(length(es.pk))))
  end

  if !isnothing(parent)
    p_i, p_e = parent
    add_part!(es.grph, :E; src=p_i, tgt=new_v, elabel=to_symbol(p_e))
    push!(es.ms, p_e)
  end

  return new_v
end

init_premodel(S::Sketch, ch::StructACSet, freeze=Symbol[]) = init_premodel(EnumState(), S, ch, freeze)

function init_premodel(es::EnumState, S::Sketch, ch::StructACSet, freeze=Symbol[])
  for o in [c.apex for c in S.cones if nv(c.d)==0 && nparts(ch, c.apex) == 0]
    add_part!(ch, o)
  end
  J = create_premodel(S, Dict(), freeze)
  i = add_premodel(es, S, J)
  ch = cset_to_crel(S, ch)
  ad = Addition(S, J, homomorphism(J.model,ch;monic=true), id(J.model))
  m = exec_change(S, J.model, ad)
  J.model = codom(m)
  J.aux.frozen = (J.aux.frozen[1] ∪ freeze) => J.aux.frozen[2]
  add_premodel(es, S, J; parent=i=>Init(ad,m))
  return es
end

get_model(es::EnumState, S::Sketch, i::Int)::StructACSet = first(crel_to_cset(S, es[i]))

end  # module
module DB
export init_db, get_premodel, add_model,
       add_premodel, add_sketch, get_model, get_models, get_model_ids, set_failed,
       add_branch, EnumState, DBLike, start_premodel, set_fired, EnumState

"""
Interact an in-memory datastore

We formerly supported a postgres backend when the scale is beyond computer
memory (or we want to serialize results to be used much later).

This could be reimplemented if needed.
"""

using ..Sketches
using ..Models

using Catlab.CategoricalAlgebra, Catlab.Present
using CSetAutomorphisms
using DataStructures


#############################
abstract type DBLike end

# DB alternative: local memory
"""
premodels - partially filled out models, seen so far, indexed by their hash
pk - vector of hash values for each model seen so far
models - subset of premodels which are complete
sizes - size of each premodel
fired - subset of premodels which have been branched on already
branch - relation showing which premodel branched into which other premodel
to_branch - propagating constraints gives us something to branch on that's
            better than the generic 'pick a FK undefined for a particular input'
"""
mutable struct EnumState <: DBLike
  premodels::Dict{String, SketchModel}
  pk::Vector{String}
  models::Set{Int}
  sizes::Vector{Int}
  fired::Set{Int}
  branch::DefaultDict{Int, Vector{Pair{Int, String}}}
  to_branch::Vector{Any}
  function EnumState()
    return new(
      Dict{String, SketchModel}(),String[],
      Set{Int}(),Int[], Set{Int}(),
      DefaultDict{Int, Vector{Pair{Int, String}}}(
        ()->Pair{Int, String}[]),[])
  end
end

Base.length(es::EnumState) = length(es.premodels)
Base.getindex(es::EnumState, i::Int) = es.premodels[es.pk[i]]

function add_premodel(es::EnumState, S::Sketch, J::SketchModel;
                      parent::Union{Int, Nothing}=nothing,
                      chash::Union{String, Nothing}=nothing)::Int
  chash = isnothing(chash) ? call_nauty(J.model).hsh : chash


  if haskey(es.premodels, chash)
    return findfirst(==(chash), es.pk)
  end


  push!(es.pk, chash)
  es.premodels[chash] = J

  if !isnothing(parent)
    push!(es.branch[parent], length(es.pk)=>"")
  end

  push!(es.sizes, sum([nparts(J.model, v) for v in vlabel(S)]))
  return length(es.pk)
end

function get_premodel_id(es::EnumState, crel::SketchModel,
  crel_pres::Presentation)::Union{Nothing, Int}
  hsh = call_nauty(crel.model).hsh
  return findfirst(==(hsh), es.pk)
end

function set_fired(es::EnumState, m::Int)
  es.fired[m] = m
end

function get_model_ids(es::EnumState, S::Sketch; maxsize::Int=0)::Vector{Int}
    is = [i for (i, s) in enumerate(es.sizes) if maxsize == 0 || s < maxsize]
    return collect(is ∩ es.models)
end

get_model(es::EnumState, S::Sketch, i::Int)::StructACSet = first(crel_to_cset(S, es[i]))


get_premodel(es::EnumState, S::Sketch, i::Int) = es.premodels[es.pk[i]]

function add_branch(es::EnumState, S::Sketch, choice::String,
                    chased_premodel_id::Int, chosen_premodel::StructACSet)::Int
  new_id = add_premodel(es, S, chosen_premodel, d)
  push!(es.branch[chased_premodel_id], new_id=>choice)
  return new_id
end


function add_model(es::EnumState, S::Sketch, J::SketchModel;
                   parent::Union{Nothing,Int}=nothing,
                   relm_hsh::Union{String, Nothing}=nothing)::Int
  !last(crel_to_cset(S, J.model)) || error("adding a partial model")
  pid = add_premodel(es, S, J; parent=parent, chash=relm_hsh)
  push!(es.models, pid)
  return pid
end

end  # module
module Propagate
export propagate!

using ..Sketches, ..Models
using Catlab.CategoricalAlgebra, Catlab.WiringDiagrams, Catlab.Theories
using DataStructures
using ..Models: EQ, fk_in, is_total, is_injective, eq_sets, merge_eq
using ..Sketches: project

include(joinpath(@__DIR__, "Functionality.jl"))
include(joinpath(@__DIR__, "Cones.jl"))
include(joinpath(@__DIR__, "Cocones.jl"))
include(joinpath(@__DIR__, "PathEqs.jl"))

"""
Code to take a premodel and propagate information using (co)-limits and path
equations, where "propagating" info means one of:
- Adding a foreign key relation
- Quotienting an equivalence class
- Updating (co)cone data
- Reducing possibilities for foreign key relations via path equalities

The general interface of a propagator then is to take a
change and return a list of changes that are implied. We
decouple producing these changes from executing them for
efficiency.
"""


function eq_reps(eq::IntDisjointSets)::Set{Int}
  Set([find_root!(eq, i) for i in 1:length(eq)])
end

"""
When we take a change and apply it, we need to update the (co)cone data and
path equation possibilities in addition to checking for new merges/additions
that need to be made.
"""
function propagate!(S::Sketch, J::SketchModel{Sc}, c::Change{Sc}) where Sc
  m = exec_change(S, J.model, c)
  verbose = false
  if verbose println("m[:A] $(collect(m[:A])) m[:B] $(collect(m[:B]))") end
  # update model
  J.model = codom(m)
  # show(stdout, "text/plain", J.model)

  update_eqs!(J,m)
  update_frozen!(S,J,m,c)
  if verbose println("\t\t\tnew frozen $(J.frozen)") end
  update_patheqs!(S, J, m)
  update_cocones!(S,J,m,c)

  # update (co)cones patheqs and quotient by functionality
  m=>vcat(quotient_functions!(S,J,m,c), propagate_cones!(S,J,m,c),
       propagate_cocones!(S,J,m,c),propagate_patheqs!(S,J,m,c))
end


function update_eqs!(J::SketchModel,m::ACSetTransformation)
  J.eqs = Dict(map(collect(J.eqs)) do (v, eq)
    new_eq = IntDisjointSets(nparts(J.model, v))
    for eqset in collect.(eq_sets(eq; remove_singles=true))
      eq1, eqrest... = eqset
      [union!(new_eq, m[v](eq1), m[v](i)) for i in eqrest]
    end
    return v=>new_eq
  end)
end

"""
Update homs when their src/tgt are frozen and are fully identified.
Update limit objects when their diagrams are frozen.
TODO: do this incrementally based on change data
"""
function update_frozen!(S::Sketch,J::SketchModel,m,ch::Change)
  fobs, fhoms = J.frozen
  chng = false
  for e in elabel(S)
    if src(S,e) ∈ fobs && is_total(S,J,e) && e ∉ fhoms
      push!(fhoms,e); chng |= true
    end
  end
  for c in S.cones
    if c.apex ∉ fobs && all(v->v∈fobs, vlabel(c.d)) && all(e->e∈fhoms, elabel(c.d)) && all(
      l->is_total(S,J,l), unique(last.(c.legs))) &&
      if nparts(codom(ch.l), c.apex) == nparts(apex(ch), c.apex)
        push!(fobs, c.apex); chng |= true
      end
    end
  end
  for (c,(cdata,cdict)) in zip(S.cocones,J.cocones)
    if c.apex ∉ fobs && all(v->v∈fobs, vlabel(c.d)) && all(e->e∈fhoms, elabel(c.d)) && all(
      l->is_total(S,J,l), unique(last.(c.legs)))
      if [c.apex=>i for i in parts(J.model, c.apex)] ⊆ collect(keys(cdict))
        push!(fobs, c.apex); chng |= true
      end
    end
  end
  J.frozen = fobs => fhoms
  if chng update_frozen!(S,J,m,ch) end
end




end # module
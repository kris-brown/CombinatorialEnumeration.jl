module Propagate
export propagate!

using ..Sketches, ..Models
using Catlab.CategoricalAlgebra, Catlab.Theories
using DataStructures
using ..Models: EQ, fk_in, is_total, is_injective, eq_sets, merge_eq, is_surjective
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

We may be propagating a change while there is already an addition queued.
"""
function propagate!(S::Sketch, J::SketchModel{Sc}, c::Change{Sc},
                    queued=nothing) where Sc
  if isnothing(queued) queued = Addition(S,J) end
  m = exec_change(S, J.model, c)
  verbose = false
  # update model
  J.model = codom(m)
  # show(stdout, "text/plain", J.model)

  update_eqs!(J,m)
  if verbose println("\t\told frozen $(J.frozen)") end
  update_frozen!(S,J,m,c,queued)
  if verbose println("\t\tnew frozen $(J.frozen)") end
  update_patheqs!(S, J, m)
  update_cocones!(S,J,m,c)

  # update (co)cones patheqs and quotient by functionality
  updates = vcat(
    set_terminal(S,J),
    quotient_functions!(S,J,m,c), propagate_cones!(S,J,m,c),
    propagate_cocones!(S,J,m,c), propagate_patheqs!(S,J,m,c))
  m_update = merge(S,J,Merge[u for u in updates if u isa Merge])
  a_update = merge(S,J,Addition[u for u in updates if u isa Addition])
  (m, m_update, a_update)
end

"""
All maps into frozen objects of cardinality 1 are determined
"""
function set_terminal(S::Sketch,J::SketchModel)
  verbose = false
  res = Addition[]
  for v in J.frozen[1]
    if nparts(J.model, v) == 1 # all maps into this obj must be 1
      for e in hom_in(S,v)
        e_s, e_t = add_srctgt(e)
        for u in setdiff(parts(J.model, src(S,e)), J.model[e_s])
          if verbose println("SET TERMINAL ADDING $e:#$u->1") end
          push!(res, add_fk(S,J,e,u,1))
        end
      end
    end
  end
  return res
end

"""
Modify union find structures given a model update
"""
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
Update (co)limit objects when their diagrams are frozen.
TODO: do this incrementally based on change data
TODO this assumes that each object is the apex of at most one (co)cone.
"""
function update_frozen!(S::Sketch,J::SketchModel,m, ch::Change, queued::Addition)
  fobs, fhoms = J.frozen
  chng = false
  is_iso(x) = is_injective(ch.l[x]) && is_surjective(ch.l[x])
  is_isoq(x) = is_injective(queued.l[x]) && is_surjective(queued.l[x])
  for e in elabel(S)
    if src(S,e) ∈ fobs && is_total(S,J,e) && e ∉ fhoms && is_isoq(e)
      push!(fhoms,e); chng |= true
    end
  end
  for c in S.cones
    if c.apex ∉ fobs && all(v->v∈fobs, vlabel(c.d)) && all(e->e∈fhoms, elabel(c.d)) && all(
      l->is_total(S,J,l), unique(last.(c.legs))) && is_iso(c.apex) && all(is_iso, vcat(vlabel(c), elabel(c)))
      if all(is_iso, [c.apex,last.(c.legs)...])
        push!(fobs, c.apex); chng |= true
      end
    end
  end
  for (c,(cdata,cdict)) in zip(S.cocones,J.cocones)
    if c.apex ∉ fobs && all(v->v∈fobs, vlabel(c.d)) && all(e->e∈fhoms, elabel(c.d)) && all(
      l->is_total(S,J,l), unique(last.(c.legs))) && is_iso(c.apex)
      push!(fobs, c.apex); chng |= true # do we need to check that cdict isn't missing something?
    end
  end
  J.frozen = fobs => fhoms
  if chng update_frozen!(S,J,m,ch, queued) end
end




end # module
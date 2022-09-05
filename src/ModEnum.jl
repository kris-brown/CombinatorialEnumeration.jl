module ModEnum
export chase_db, test_models, init_db

using ..Sketches
using ..Models
using ..DB
using ..Propagate
using ..Models: eq_sets, is_total

using Catlab.CategoricalAlgebra, Catlab.Theories
using CSetAutomorphisms

using Test
using Combinatorics


"""
Add, then apply merges (while accumulating future adds to make) until fixpoint

We pass in the pending additions into propagate! so that we avoid infinite loops
(otherwise we keep trying to add something that needs to be added, even though
we've already queued it up to be added.)
"""
function prop(es::EnumState, S::Sketch, e::Int, ec::Union{Init,AddEdge,Branch})
  verbose = false
  t = tgt(es.grph, e)
  J = deepcopy(es[t])
  m_change, a_change = propagate!(S, J, ec.add, ec.m)
  es.prop[t] = (J.aux, a_change, m_change) # record the result of prop
  if all(is_no_op,[a_change,m_change]) && !last(crel_to_cset(S,J.model))
    push!(es.models,t) # found a model
  end
  return nothing
end

function prop(es::EnumState, S::Sketch, e::Int, ec::MergeEdge)
  verbose = false
  t = tgt(es.grph, e)
  ec = es.ms[e]
  queued, ch = ec.queued, ec.merge

  J = deepcopy(es[t])
  queued_ = update_change(S,J,ec.m, queued)
  m_change, a_change = propagate!(S, J, ch, ec.m; queued=queued_)
  codom(queued_.r) == codom(a_change.r) || error("HERE")
  es.prop[t] = (J.aux, merge(S,J, queued_, a_change), m_change) # record the result of prop
  if all(is_no_op,[a_change,m_change]) && !last(crel_to_cset(S,J.model))
    push!(es.models,t) # found a model
  end
  return nothing
end


"""
Run additions until there's nothing to add or merge.
I.e. go as far as you can w/o branching.

Initialize loop with an Addition edge that has not yet been propagated.

(unknown if this will enter an infinite loop and that we have to branch)
"""
function add!(es::EnumState, S::Sketch, e::Int; force=false)
  verbose = false
  while true
    e_next = add_merge!(es, S, e)
    if e == e_next break end
    e = e_next
  end
  return e
end

"""
Pick a FK + source element to branch on, if any.

This has some loose heuristics for which morphism to choose. It favors
morphisms between frozen objects over morphisms with unfrozen objects.
We should probably bias cocone legs over cone legs (which get derived
automatically from the data in their diagram).

No heuristic is currently used to pick which element (of the ones without the FK
defined) gets branched on.
"""
function find_branch_fk(S::Sketch, J::SketchModel)::Union{Nothing, Pair{Symbol,Int}}
  score(f) = sum([src(S,f)∈J.aux.frozen[1], tgt(S,f)∈J.aux.frozen[1]]) +
                  (any(c->f ∈ last.(c.legs), S.cones) ? -0.5 : 0)
  fs = map(setdiff(elabel(S), J.aux.frozen[2])) do f
    for p in parts(J.model, src(S,f))
      if isempty(incident(J.model, p, add_src(f)))
        return f => p
      end
    end
    return nothing
  end

  dangling = [score(fi[1])=>fi for fi in fs if !isnothing(fi)]
  return last(last(sort(dangling)))
end


"""
Get a list of changes to branch on, corresponding to possible assignments of a
FK.
We should not be branching on things that have nontrivial equivalences in
J.eqs.
"""
function branch_fk(es, S::Sketch, i::Int)
  aux = es.prop[i][1]
  J = SketchModel(es[i].model, aux)
  branch_m, branch_val = find_branch_fk(S, J)
  !isnothing(branch_m) || error("Do not yet support branching on anything but FKs")
  ttab = tgt(S,branch_m)
  for t in vcat(ttab ∉ J.aux.frozen[1] ? [0] : [], parts(J.model, ttab))
    c = add_fk(S,J,branch_m,branch_val,t)
    J_ = deepcopy(J)
    m = exec_change(S, J.model, c)
    J_.model = codom(m)
    add_premodel(es, S, J_, parent=i=>Branch(c, m))
  end
end

# """
# Pick a premodel and apply all branches, storing result back in the db.
# Return the premodel ids that result. Return nothing if already fired.

# Optionally force branching on a particular FK.
# """
function chase_db_step!(S::Sketch, es::EnumState, e::Int)
  verbose = false
  change = false
  s, t = src(es.grph, e), tgt(es.grph, e)
  if isempty(incident(es.grph, t, :src))
    if t ∉ es.fail ∪ es.models
      change |= true
      if isnothing(es.prop[t])
        if verbose println("propagating target $t") end
        try
          prop(es,S,e, es.ms[e])
        catch a_ModelException
          if a_ModelException isa ModelException
            push!(es.fail, t)
            if verbose println("\tMODELEXCEPTION: $(a_ModelException.msg)")
            end
          else
            println("ERROR AT $t")
            throw(a_ModelException)
          end
        end
      else
        aux, ad, mrg = es.prop[t]
        J = SketchModel(es[t].model, aux)
        if is_no_op(mrg)
          if is_no_op(ad) # we branch b/c no more constraints to propagate
            if verbose println("branching target $t") end
            branch_fk(es, S, t)
          else # we have additions to propagate
            if verbose println("$t has addition to propagate (nv $(nv(es.grph)))") end

            J_ = deepcopy(J)
            m = exec_change(S, J.model, ad)
            J_.model = codom(m)

            add_premodel(es,S,J_; parent=t=>AddEdge(ad,m))
          end
        else # we have merges to propagate
          if verbose println("$t has merge to propagate (nv $(nv(es.grph)))") end
          J_ = deepcopy(J)
          m = exec_change(S, J.model, mrg)
          J_.model = codom(m)
          add_premodel(es,S,J_; parent=t=>MergeEdge(mrg, ad, m))

        end
      end
    end
  end
  return change
end


"""
Continually apply chase_db_step! while there is work remaining to be done.
"""
function chase_db(S::Sketch, es::EnumState, n=-1)
  verbose = true
  change = true
  while n!=0 && change
    n -= 1
    change = false
    for e in edges(es.grph)
      change |= chase_db_step!(S,es,e)
    end
  end
end

"""
Enumerate elements of ℕᵏ

Do the first enumeration by incrementing n_nonzero and finding partitions so
that ∑(c₁,...) = n_nonzero
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
We can reason what are the models that should come out, but not which order
they are in, so we make sure canonical hashes match up.
"""
function test_models(db::EnumState, S::Sketch, expected; f=identity, include_one=false)
  Set(call_nauty(e).hsh for e in expected) == Set(
      call_nauty(f(get_model(db,S,m))).hsh for m in db.models if include_one || m > 1)
end

end # module

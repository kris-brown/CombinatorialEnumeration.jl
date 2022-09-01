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
Take a mix of Additions and Merges and execute the Merges until there are
only Additions left.

We may need to pass in the pending additions into propagate! so that we avoid
infinite loops (we keep trying to add something that needs to be added, even
though we've already queued it up to be added.)
"""
function add_merge!(S::Sketch, J::SketchModel, ch::Addition)
  verbose = false
  if verbose println("\tadd_merge! addition $ch ") end
  m, m_change, a_change = propagate!(S, J, ch)
  new_a_change = a_change
  while !(is_no_op(m_change) || is_no_op(new_a_change)) # or any SketchModel change, really?
    if verbose println("\t\tadd_merge! starting while loop w/ $ch (remaining: $a_change)") end
    m′, m_change, new_a_change = propagate!(S, J, ch, a_change)
    println("propagate produced m_change $m_change new_a_change $new_a_change")
    a_change = update_changes(S,J,m′,[a_change, new_a_change])
    m = m ⋅ m′
  end
  if verbose println("\t add_merge! generated $a_change") end
  return m => a_change
end

"""
Run additions until there's nothing to add or merge. I.e. go as far as you can w/o branching.
(unknown if this will enter an infinite loop and that we have to branch)
"""
function add!(S::Sketch, J::SketchModel, ch::Addition; force=false)
  J = deepcopy(J)
  verbose = false
  m = id(J.model)
  while force || !is_no_op(ch)
    force = false
    if verbose println("starting add! with $ch") end
    m′, ch = add_merge!(S, J, ch)
    m = m⋅m′
  end
  return m => J
end

"""initialise a sketch model and propagate"""
function add!(S::Sketch, ch::StructACSet, freeze=Symbol[])
  for o in [c.apex for c in S.cones if nv(c.d)==0]
    if nparts(ch, o) == 0 add_part!(ch, o) end
  end
  J=create_premodel(S, Dict(v=>nparts(ch,v) for v in vlabel(S)), freeze)
  ch = cset_to_crel(S, ch)
  ad = Addition(S, J, homomorphism(J.model, ch; monic=true), id(J.model))
  _, J = add!(S, J, ad; force=true) # run it even if ad is a no op
  return J
end

"""
Take a premodel and branch on a FK (favor FKs between 'frozen' objects).
(potentially a smarter algorithm can determine where would be best to branch).
For each branch, saturate with `add!`.

We should probably bias cocone legs over cone legs (which get derived
automatically from the data in their diagram)

TODO: branching should only consider distinct *orbits* in codomain
      so we should be storing the Nauty res in the db
"""
function branch(S::Sketch, J::SketchModel; force=nothing)::Vector{Addition}
  verbose = false
  if verbose
    println("entering branch w/ frozen $(J.frozen) and model ");
    show(stdout, "text/plain", first(crel_to_cset(S,J.model)))
  end
  if isnothing(force)
    score(f) = sum([src(S,f)∈J.frozen[1], tgt(S,f)∈J.frozen[1]]) +
      (any(c->f ∈ last.(c.legs), S.cones) ? -0.5 : 0)
    dangling = [score(f)=>f for f in setdiff(elabel(S), J.frozen[2]) if !is_total(S,J,f)]
    branch_m = last(last(sort(dangling)))
  else
    branch_m = force ∈ J.frozen[2] ? error("cannot force $force") : force
  end
  bsrc, btgt = add_srctgt(branch_m)
  for eqs in collect.(eq_sets(J.eqs[src(S,branch_m)]))
    if isempty(vcat(incident(J.model, eqs, bsrc)...))
      val = first(eqs)
      fresh = tgt(S,branch_m) ∈ J.frozen[1] ? [] : [add_fk(S,J,branch_m,val,0)]
      return vcat(fresh,[add_fk(S,J,branch_m,val,i)
              for i in first.(collect.(eq_sets(J.eqs[tgt(S,branch_m)])))])
    end
  end
  error("$branch_m should be in frozen: $(J.frozen)")
end

"""
Pick a premodel and apply all branches, storing result back in the db.
Return the premodel ids that result. Return nothing if already fired.
"""
function chase_db_step!(S::Sketch, db::EnumState, i::Int; brnch=nothing)
  verbose = false

  pk = db.pk[i]
  if i ∈ db.fired || i ∈ db.models return Int[] end
  J = deepcopy(db.premodels[pk])
  push!(db.fired, i)
  return filter(x->!isnothing(x), map(branch(S,J; force=brnch)) do b
    if verbose println("\n\n\n*****\npremodel $i branching on $b") end
    try
      _, Jres = add!(S,J,b)
      _, bad = crel_to_cset(S,Jres.model)
      if !bad # NEW MODEL
        return add_model(db, S, Jres; parent=i)
      else
        return add_premodel(db, S, Jres; parent=i)
      end
    catch a_ModelException
      if !(a_ModelException isa ModelException)
        println("ERROR AT $i")
        delete!(db.fired, i)
        throw(a_ModelException)
      end
    end
  end)
end

"""
Continually apply chase_db_step! while there is work remaining to be done.
"""
function chase_db(S::Sketch, db::EnumState)
  # existing unfired premodels
  queue = collect(setdiff(1:length(db), db.fired ∪ db.models))
  while !isempty(queue)
    append!(queue, chase_db_step!(S,db,pop!(queue)))
  end
end

"""
Initialize an EnumState with a structACSet. This is the one chance to add parts
that are frozen.
"""
function init_db(S::Sketch, ad::StructACSet, freeze=Symbol[])
  es = EnumState()
  J = add!(S, ad, freeze)
  _, bad = crel_to_cset(S,J.model)
  if !bad # NEW MODEL
    add_model(es, S, J)
  else
    add_premodel(es, S, J)
  end
  return es
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
function test_models(db::EnumState, S::Sketch, expected; f=identity)
  Set(call_nauty(e).hsh for e in expected) == Set(
      call_nauty(f(get_model(db,S,m))).hsh for m in db.models)
end

end # module

module ModEnum
export chase_db
using ..Sketches
using ..Models
using ..DB
using ..Propagate
using ..Models: eq_sets
using Catlab.CategoricalAlgebra, Catlab.Theories
using Combinatorics

"""
Applying some changes makes other changes redundant. This detects when we
can ignore a change
"""
is_no_op(ch::Change) = all(f->dom(f)==codom(f) && isperm(collect(f)),
                             collect(components(ch.l)))


"""
Take a mix of additions and merges and execute the merges until there are
only additions left.
"""
function add_merge!(S::Sketch, J::SketchModel, ch::Addition)
  verbose = false
  if verbose println("\tadd_merge! addition $ch ") end
  m, changes = propagate!(S, J, ch)
  while !all(c->c isa Addition, changes)
    c = popat!(changes, findfirst(c->c isa Merge, changes))
    if is_no_op(c) println("no op!"); continue end
    if verbose println("\t\tadd_merge! starting while loop w/ $c (remaining: $(Vector{Any}(changes))") end
    m′, cs = propagate!(S, J, c) # do we want to do something with this morphism?
    changes = update_changes(S,J,m′,changes) # update existing matches
    m = m ⋅ m′
    append!(changes, cs)
  end
  if verbose println("\t add_merge! generated $(length(changes)) new changes: $changes") end
  return m => Vector{Addition}(changes)
end

"""
Run additions until there's nothing to add or merge. I.e. go as far as you can w/o branching.
(unknown if this will enter an infinite loop and that we have to branch)
"""
function add!(S::Sketch, J::SketchModel, ch::Addition)
  J = deepcopy(J)
  verbose = false
  changes = Addition[ch]
  m = id(J.model)
  while !isempty(changes)
    c = pop!(changes)
    if is_no_op(c) && verbose println("no op!"); continue end

    if verbose println("starting add! while loop with $c (remaining: $(Vector{Any}(changes)))") end
    codom(c.r) == J.model || error("unpropagated ch $c")
    m′, cs = add_merge!(S, J, c)
    for c in cs
      codom(c.r) == J.model || error("new change not updated $c")
    end
    changes = update_changes(S,J,m′,changes) # update existing matches
    for chng in changes
      codom(chng.r) == J.model || error("a change not updated $chng")
    end
    m = m⋅m′
    append!(changes, cs)
  end
  return m => J
end

"""initialise a sketch model and propagate"""
function add!(S::Sketch, ch::StructACSet)
  for one_ob in [c.apex for c in S.cones if nv(c.d)==0]
    if nparts(ch, one_ob) == 0 add_part!(ch, one_ob)
    elseif nparts(ch, one_ob) > 1 rem_parts!(ch, one_ob, 1:nparts(ch, one_ob)-1)
    end
  end
  for zero_ob in [c.apex for c in S.cocones if nv(c.d)==0]
    rem_parts!(ch, zero_ob, 1:nparts(ch, zero_ob))
  end

  J=create_premodel(S)
  ch = cset_to_crel(S, ch)
  freeze = J.frozen
  J.frozen = Set{Symbol}()=>Set{Symbol}()
  ad = Addition(S, J, only(homomorphisms(J.model, ch)), id(J.model))
  J.frozen = freeze
  _, J = add!(S, J, ad)
  return J
end

"""
Take a premodel and branch on a FK (favor FKs between 'frozen' objects).
(potentially a smarter algorithm can determine where would be best to branch).
For each branch, saturate with `add!`.

To do: branching should only consider distinct *orbits* in codomain
"""
function branch(S::Sketch, J::SketchModel; force=nothing)::Vector{Addition}
  verbose = false
  if verbose println("entering branch w/ frzoen $(J.frozen)") end
  if isnothing(force)
    score(f) = sum([src(S,f)∈J.frozen[1], tgt(S,f)∈J.frozen[1]])
    dangling = [score(f)=>f for f in setdiff(elabel(S), J.frozen[2])]
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

function init_db(S::Sketch, ad::StructACSet)
  es = EnumState()
  J = add!(S, ad)
  add_premodel(es,S,J)
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

end # module

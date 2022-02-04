module ModEnum
export chase_step, chase_step_db, chase_set

using ..Sketches
using ..DB
using ..Models
using ..Limits

using Catlab.WiringDiagrams, Catlab.CategoricalAlgebra
using Catlab.Programs.RelationalPrograms: parse_relation_diagram
using Combinatorics
using DataStructures
using LibPQ, Tables

"""
parallelize by adding Threads.@threads before a for loop. Hard to do w/o
creating bugs.
"""

"""
rigid: model exploration is forced to maintain the cardinalities of NON-limit
objects.

1. When branching, don't add a free option if the codom is non-limit
2. When merging (due to funeq or patheq), fail if two non-limit items are merged
"""
const rigid = true

# Type synonyms
###############
const Poss = Tuple{Symbol, Int, Modify}
struct Branch
  branch::Symbol     # either a morphism or a cocone apex
  val::Int           # index of the src element index or the cocone
  poss::Vector{Poss} # Modifications: possible ways of branching
end
const b_success = Branch(Symbol(),0,[])

# Toplevel functions
####################
"""
Take a sketch and a premodel and perform one chase step.

1. Build up equivalence classes using path equalities
2. Compute cones and cocones
3. Consider all TGDs (foreign keys that point to nowhere).
  - Pick one and return the possible decisions for branching on it
"""
function chase_step(S::Sketch, J::StructACSet
                    )::Union{Nothing,Pair{StructACSet,Branch}}
  # Initialize variables
  verbose = false
  fail, J = handle_zero_one(S, J) # doesn't modify J
  if fail return nothing end

  ns, lc, w = NewStuff(), LoneCones(), Weights(() -> 0)

  # this loop might not be necessary. If one pass is basically all that's
  # needed, then this loop forces us to run 2x loops
  for cnt in Iterators.countfrom()
    if cnt > 1 println("\tchase step iter #$cnt") end
    if cnt > 3 error("TOO MANY ITERATIONS") end
    changed, failed, J, ns, lc, w = propagate_info(S, J, ns)
    if failed return nothing end
    if !changed break end
  end

  # add new things that make J bigger
  update_crel!(J, ns)
  if verbose println("adding to J $J \n ns $ns") end
  crel_to_cset(S, J)
  if verbose
    println("J Res "); show(stdout, "text/plain", crel_to_cset(S, J)[1])
  end
  fail, J = handle_zero_one(S, J) # doesn't modify J
  if fail return nothing end
  free_poss, constr_poss, or_poss = get_possibilities(S, J, lc)
  lfree, lconstr, lor = length.([free_poss, constr_poss, or_poss])

  # Metric for undesirability of a branch
  #bf = b->w[b.branch => b.val]/(2*length(b.poss))
  bf = b->(length(b.poss), -w[b.branch => b.val])

  if verbose println("$(lfree) free, $lconstr constr, $lor or") end
  if (lfree + lconstr + lor) == 0
    return J => b_success
  elseif lfree > 0
    return J => first(sort(free_poss, by=bf))
  elseif lor > 0
    return J => first(sort(or_poss, by=bf))
  else
    return J => first(sort(constr_poss, by=bf))
  end
end

"""Set cardinalities of 0 and 1 objects correctly + maps into 1"""
function handle_zero_one(S::Sketch, J::StructACSet)::Pair{Bool,StructACSet}
  J = deepcopy(J)
  eq = init_eq(S, J)

  for t1 in one_ob(S)
    unions!(eq[t1], collect(parts(J, t1)))
    if nparts(J, t1) == 0
      add_part!(J, t1)
    end
    for e in filter(e->tgt(S,e)==t1, S.schema[:elabel])
      [add_rel!(J, e, i, 1) for i in parts(J, src(S, e))]
    end
  end
  merge!(S, J, eq)
  for t0 in zero_ob(S)
    if nparts(J, t0) > 0
      return true => J
    end
  end
  return false => J
end

"""
Use path equalities, functionality of FK relations, cone/cocone constraints to
generate new data and to quotient existing data. Separate information that can
be safely applied within a while loop (i.e. everything except for things
related to newly added elements).
"""
function propagate_info(S::Sketch, J::StructACSet, ns::NewStuff
          )::Tuple{Bool, Bool, StructACSet, NewStuff, LoneCones, Weights}
  verbose, changed = true, false
  eq = init_eq(S, J) # trivial equivalence classes
  w = Weights(()->.0) # initial weighting
  if verbose println("STARTING PROPAGATE INFO WITH NS $ns and $(eq[:I])")
    if verbose show(stdout, "text/plain", crel_to_cset(S, J)[1]) end
  end
  # Path Eqs
  pchanged, pfail = path_eqs!(S,J,eq,w)
  if verbose println("\tpchanged $pchanged: $(sizes(S, J)) $(eq[:I])") end
  changed |= pchanged
  if pfail return (changed, true, J, NewStuff(), LoneCones(), w) end

  # Cones
  cchanged, cfail = compute_cones!(S, J, eq, ns, w)
  if verbose println("\tcchanged $cchanged $(sizes(S, J)) $(eq[:I])") end
  changed |= cchanged
  if cfail return (changed, true, J, NewStuff(), LoneCones(), w) end
  if verbose println("ns $ns") end

  # Cocones
  cochanged, cfail, lone_cones = compute_cocones!(S, J, eq, ns, w)
  if verbose println("\tcochanged $cochanged: $(sizes(S, J)) $(eq[:I])") end
  changed |= cochanged
  if cfail return (changed, true, J, NewStuff(), LoneCones(), w) end

  # because this is at the end, chased premodels should be functional
  fchanged, ffail, ns = fun_eqs!(S, J, ns, eq)
  if verbose println("\tfchanged $fchanged: $(sizes(S, J))") end
  changed |= fchanged
  if ffail return (changed, true, J, NewStuff(), LoneCones(), w) end
  cs = crel_to_cset(S, J) # will trigger a fail if it's nonfunctional
  if verbose show(stdout, "text/plain", cs[1]) end
  if verbose println("\tENDING ns $(ns.ns[:II])") end

  return (changed, false, J, ns, lone_cones, w)
end

"""
For each unspecified FK, determine its possible outputs that don't IMMEDIATELY
violate a cone/cocone constraint. Additionally consider an option that the FK
points to a fresh element in the codomain table.

It may seem like, if many sets of possibilities has only one option, that we
could safely apply all of them at once. However, this is not true. If a₁ and a₂
map to B (which is empty), then branching on either of these has one
possibility; but the pair of them has two possibilities (both map to fresh b₁,
or map to fresh b₁ and b₂).
"""
function get_possibilities(S::Sketch, J::StructACSet, lc::LoneCones
                          )::Tuple{Vector{Branch},Vector{Branch},Vector{Branch}}
  free_poss, constr_poss, or_poss = [Branch[] for _ in 1:3]
  z1 = zero_ob(S) ∪ one_ob(S)
  # Dangling foreign keys ('tuple generating dependencies')
  for (e_list, poss_list) in [free_homs(S)=>free_poss,
                              constr_homs(S)=>constr_poss]
    for e in e_list
      src_tab, tgt_tab = src(S,e), tgt(S,e)
      esrc, _ = add_srctgt(e)
      unmatched = setdiff(parts(J,src_tab), J[esrc])
      for u in unmatched
        # possibilities of setting `u`'s value of FK `e`
        subres = Poss[]

        # First possibility: a `e` sends `u` to a fresh ID
        if tgt_tab ∉ z1 && !(rigid && tgt_tab ∈ free_obs(S))
          mu = Modify()
          mu.newstuff.ns[tgt_tab][(e, u)] = NewElem()
          push!(mu.newstuff.ns[tgt_tab][(e, u)].map_in[e], u)
          push!(subres, (e, 0, mu))
        end
        # Remaining possibilities (check satisfiability w/r/t cocones/cones)
        for p in 1:nparts(J,tgt_tab)
          m = Modify()
          push!(m.update, (e, u, p))
          push!(subres, (e, p, m))
        end
        push!(poss_list, Branch(e, u, subres))
      end
    end
  end
  # Orphan cocone apex elements.
  for (k, vs) in filter(x->!isempty(x[2]), pairs(lc))
    cocone = only([c for c in S.cocones if c.apex == k])
    val = first(vs) # They're all symmetric, so we just need one.
    subres = Poss[] # all possible ways to map to an element of this cocone
    for leg in last.(cocone.legs)
      srctab = src(S, leg)
      src_fk = add_srctgt(leg)[1]
      # Consider a new element being added and mapping along this leg
      if srctab ∉ z1 && !(rigid && srctab ∈ free_obs(S))
        fresh = Modify()
        fresh.newstuff.ns[srctab][(k, leg)] = NewElem()
        fresh.newstuff.ns[srctab][(k, leg)].map_out[leg] = val
        push!(subres, (leg, nparts(J, srctab) + 1, fresh))
      end
      # Consider existing elements for which this leg has not yet been set
      for u in setdiff(parts(J, srctab), J[src_fk])
        m = Modify()
        push!(m.update, (leg, u, val))
        push!(subres, (leg, u, m))
      end
    end
    push!(or_poss, Branch(cocone.apex, val, subres))
  end
  return free_poss, constr_poss, or_poss
end

# DB
####

"""Explore a premodel and add its results to the DB."""
function chase_step_db(db::LibPQ.Connection, premodel_id::Int; redo::Bool=false
                       )::Pair{Bool, Vector{Int}}
  verbose = true
  # Check if already done
  if !redo
    z = columntable(execute(db, """SELECT 1 FROM Premodel WHERE
      Premodel_id=\$1 AND failed IS NULL""", [premodel_id]))
    if isempty(z)
      z = columntable(execute(db, """SELECT Model_id FROM Model
                                     WHERE Premodel_id=\$1""", [premodel_id]))
      if !isempty(z)
        return true => [only(z[:premodel_id])]
      else
        z = columntable(execute(db, """SELECT Choice.child FROM Fired JOIN
        Choice ON Fired.child=Choice.parent WHERE Fired.parent=\$1""", [premodel_id]))
        return false => collect(z[:child])
      end
    end
  end

  S, J_ = get_premodel(db, premodel_id)
  if verbose println("CHASING PREMODEL #$premodel_id: $(sizes(S, J_))") end
  # show(stdout, "text/plain", crel_to_cset(S, J_)[1])
  cs_res = chase_step(S, create_premodel(S, J_))

  # Failure
  if isnothing(cs_res)
    set_failed(db, premodel_id, true)
    return false => Int[]
  end

  # Success
  set_failed(db, premodel_id, false)

  J, branch = cs_res
  # println("\tChased premodel: $(sizes(S, J))")
  # show(stdout, "text/plain", crel_to_cset(S, J)[1])
  chased_id = add_premodel(db, S, J; parent=premodel_id)

  # Check we have a real model
  if branch == b_success
    println("\t\tFOUND MODEL")
    return true => [add_model(db, S, J, chased_id)]
  else
    println("\tBranching on $branch")
    res = Int[]
    for (e,i,mod) in branch.poss
      J__ = deepcopy(J)
      update_crel!(J__, mod)
      bstr = string((branch.branch, branch.val, e, i))
      push!(res, add_branch(db, S, bstr, chased_id, J__))
    end
    return false => res
  end
end

"""
Find all models below a certain cardinality. Sometimes this exploration process
generates models *larger* than what we start off with, yet these are eventually
condensed to a small size.
`extra` controls how much bigger than the initial cardinality we are willing to
explore intermediate models.
`ignore_seen` skips checking things in the database that were already chased.
If true, the final list of models may be incomplete, but it could be more
efficient if the goal of calling this function is merely to make sure all models
are in the database itself.
"""
function chase_below(db::LibPQ.Connection, S::Sketch, n::Int; extra::Int=3,
                     filt::Function=(x->true))::Nothing
  ms = []
  for combo in combos_below(length(free_obs(S)), n)
    ps = mk_pairs(collect(zip(free_obs(S), combo)))
    if filt(Dict(ps))
      premod = create_premodel(S, ps)
      push!(ms,premod)
    end
  end
  chase_set(db, S, ms, n+extra)
end

"""Keep processing until none remain"""
function chase_set(db::LibPQ.Connection,S::Sketch,v::Vector{StructACSet},
                   n::Int)::Nothing
  for m in v
    add_premodel(db, S, m)
  end
  while true
    todo = get_premodel_ids(db, S; unchased=true, maxsize=n)
    if isempty(todo)
      break
    else
      for mdl in todo # Threads.@threads?
        chase_step_db(db, mdl)
      end
    end
  end
end

# Equalities
############

"""
Note which elements are equal due to relations actually representing functions

a₁  -> b₁
a₂  -> b₂
a₁  -> b₃
a₃  -> b₄

Because a₁ is mapped to b₁ and b₃, we deduce b₁=b₃. If the equivalence relation
has it such that a₂=a₃, then we'd likewise conclude b₂=b₄

Subtlety: this could equate an existing object with a proposed object in a
Modify. Or it could equate two new objects with each other.

Updates `eqclass` - returns a new `m` to replace the old
"""
function fun_eqs!(S::Sketch, J::StructACSet, m::NewStuff, eqclass::EqClass
                  )::Tuple{Bool, Bool, NewStuff}
  changed = false
  J_cardinalities = Dict([v=>nparts(J,v) for v in S.schema[:vlabel]])
  update_crel!(J, m)
  [[push!(eqclass[v]) for _ in J_cardinalities[v]:(nparts(J, v)-1)]
    for v in S.schema[:vlabel]]
  fchanged, ffail = fun_eqs!(S, J, eqclass)
  if ffail return changed, true, m end  # possibly fail
  changed |= fchanged
  merge!(S, J, eqclass) # apply the quotient

  # show(stdout, "text/plain", crel_to_cset(S, J)[1])

  ns = NewStuff()
  for (ti, tab) in enumerate(S.schema[:vlabel])
    #println("tab $tab $((J_cardinalities[tab]+1):nparts(J, tab)))")
    for (ns_ind, J_ind) in enumerate((J_cardinalities[tab]+1):nparts(J, tab))
      #println("ns_ind $ns_ind J_ind $J_ind")
      ns.ns[tab][ns_ind] = NewElem()
      # get maps in
      for e in S.schema[incident(S.schema, ti, :tgt), :elabel]
        s, t = add_srctgt(e)
        #println("CHECKING map in $e ($(J[incident(J, J_ind, t), s]))")
        for val_in in J[incident(J, J_ind, t), s]
          push!(ns.ns[tab][ns_ind].map_in[e], val_in)
        end
      end
      # get maps out
      for e in S.schema[incident(S.schema, ti, :src), :elabel]
        s, t = add_srctgt(e)
        #println("CHECKING map in $e ($(J[incident(J, J_ind, s), t]))")
        for val_out in J[incident(J, J_ind, s), t]
          if length(val_out) == 1
            ns.ns[tab][ns_ind].map_out[e] = only(val_out)
          elseif length(val_out) > 1
            error("We just quotiented by functionality")
          end
        end
      end
    end
  end
  # Delete the purely new stuff
  [rem_parts!(J, tab, (c+1):nparts(J, tab)) for (tab, c) in
   pairs(J_cardinalities)]
  for e in S.schema[:elabel]
    cols = zip([J[z] for z in add_srctgt(e)]...)
    del_parts = [i for (i, (x,y)) in enumerate(cols) if x == 0 || y == 0]
    rem_parts!(J, e, del_parts)
  end
  new_J_cards = Dict([v=>nparts(J,v) for v in S.schema[:vlabel]])
  for v in S.schema[:vlabel]
    new_J_cards[v] <= J_cardinalities[v] || error("Extra $v in $J")
  end

  return changed, false, ns
end

"""
Return whether it changes the eqclass or fails.
"""
function fun_eqs!(S::Sketch, J::StructACSet, eqclass::EqClass)::Pair{Bool,Bool}
  # println([k=>(nparts(J,k),length(v)) for (k,v) in pairs(eqclass)])
  cols = [:elabel, [:src, :vlabel], [:tgt, :vlabel]]
  changed = false
  for (d, srcobj, tgtobj) in collect(zip([S.schema[x] for x in cols]...))
    dsrc, dtgt = add_srctgt(d)
    srcobj, tgtobj = src(S, d), tgt(S,d)
    for src_eqset in collect.(eq_sets(eqclass[srcobj]; remove_singles=false))
      tgtvals = Set(J[vcat(incident(J, src_eqset, dsrc)...), dtgt])
      if length(tgtvals) > 1
        if rigid && tgtobj ∈ free_obs(S)
          println("Fun Eq of $d (src: $src_eqset) merges $tgtobj: $tgtvals")
          show(stdout, "text/plain", J)
          return changed => true
        else
          for (i,j) in Iterators.product(tgtvals, tgtvals)
            if !in_same_set(eqclass[tgtobj], i, j)
              changed = true
              union!(eqclass[tgtobj], i, j)
            end
          end
        end
      end
    end
  end
  return changed => false
end

"""
Modifies J, eqclasses, and w.

If we have two paths A->B, p₁₁...p₁ₙ and p₂₁...p₂ₙ, then, if, for a starting
point in A:
1.) one of the paths is completely determined
2.) the other path is determined entirely except for the last relation

We can set the value of the last relation to the value of the determined one.

If both paths are determined, the final terms can be set to be equivalent, if
this is allowed (otherwise, return `true`).
"""
function path_eqs!(S::Sketch, J::StructACSet, eqclasses::EqClass, w::Weights
                  )::Pair{Bool, Bool}
  verbose, changed = false, false
  for (eqn, p, q) in S.eqs # could be done in parallel
    if verbose println("processing equality $eqn") end
    src_tab, tgt_tab = src(S, p[1]), tgt(S, p[end])
    eqc = eq_reps(eqclasses[src_tab])
    for x in eqc # can be parallel
      res_p, is_penult_p = eval_path!(p, J, x, w)
      res_q, is_penult_q = eval_path!(q, J, x, w)
      if verbose println("""x $x res_p $res_p (is_penult $is_penult_p)
        res_q $res_q (is_penult $is_penult_q)""") end
      real_p, real_q = (!isnothing).([res_p, res_q])
      if is_penult_p && real_q && !is_penult_q
        if verbose println("$eqn (rev) set $(last(p)): $res_p -> $res_q") end
        changed = true
        add_rel!(J, last(p), res_p, res_q)
      elseif is_penult_q && real_p && !is_penult_p
        if verbose println("$eqn (fwd) set $(last(q)): $res_q -> $res_p") end
        changed = true
        add_rel!(J, last(q), res_q, res_p)
      elseif real_p && real_q && !(is_penult_p || is_penult_q) && !in_same_set(
              eqclasses[tgt_tab],res_p,res_q)
        changed = true
        if rigid && tgt_tab ∈ free_obs(S)
          if verbose
            println("Fail: tried to equate $tgt_tab #$res_p and $res_q")
          end
          return changed => true
        else
          println("$eqn set $tgt_tab: $res_p == $res_q")
          union!(eqclasses[tgt_tab], res_p, res_q)
        end
      end
    end
  end
  return changed => false
end

"""
Compose relations starting as functions.

Because `eq_fun` quotients by functionality, we only need to pick, for a
relation A->B and  aᵢ, a single related bⱼ (if any exists).

This process terminates when nothing is related in the codomain. If this happens
right before the *last* relation, then we note this with a `true` boolean flag.

Modifies w
"""
function eval_path!(pth::Vector{Symbol}, J::StructACSet, x::Int, w::Weights
                   )::Pair{Union{Nothing, Int}, Bool}
  prev_x = x
  for (i, edge) in enumerate(pth)
    edgesrc, edgetgt = add_srctgt(edge)
    if isnothing(x)
      return nothing => false
    else
      prev_x, inc = x, incident(J, x, edgesrc)
      x = isempty(inc) ? nothing : J[first(inc), edgetgt]
      if isnothing(x)
        w[edge => prev_x] += 1 / (1+length(pth)-i)
      end
    end
  end
  return isnothing(x) ? prev_x => true : x => false
end

# Misc
######

"""
1. Enumerate elements of ℕᵏ for an underlying graph with k nodes.
2. For each of these: (c₁, ..., cₖ) create a term model with that many constants

Do the first enumeration by incrementing n_nonzero and finding partitions so
that ∑(c₁,...) = n_nonzero

In the future, this function will write results to a database
that hashes the Sketch as well as the set of constants that generated the model.

Also crucial is to decompose Sketch into subparts that can be efficiently solved
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

"""Check if each coproduct as |A|+|B|, etc. """
function discrete_cardinality_check(S::Sketch, J::StructACSet)::Bool
  verbose = false
  for c in S.cones
    if nv(c.d) == 0 && nparts(J, c.apex) != 1
      if verbose println("Empty cone $(c.apex) doesn't have one elem") end
      return false
    elseif ne(c.d) == 0 && nparts(J, c.apex) != prod([nparts(J,c.d[x,:vlabel]) for x in first.(c.legs)])
      if verbose println("Cone $(c.apex) doesn't have $(prod([nparts(J,c.d[x,:vlabel]) for x in first.(c.legs)]))") end
      return false
    end
  end
  for c in S.cocones
    if nv(c.d) == 0 && nparts(J, c.apex) != 0
      if verbose println("Empty cocone $(c.apex) has more than 0 elem") end
      return false
    elseif ne(c.d) == 0 && nparts(J, c.apex) != sum([nparts(J,c.d[x, :vlabel]) for x in first.(c.legs)])
      if verbose println("Empty cone $(c.apex) doesn't have $(sum([nparts(J,c.d[x, :vlabel]) for x in first.(c.legs)]))") end
      return false
    end
  end
  return true
end
end # module
include(joinpath(@__DIR__, "Sketch.jl"))
include(joinpath(@__DIR__, "DB.jl"))
include(joinpath(@__DIR__, "Models.jl"))

using Catlab.Programs.RelationalPrograms: parse_relation_diagram
using Catlab.WiringDiagrams
using Combinatorics

"""
rigid: model exploration is forced to maintain the cardinalities of NON-limit
objects.

1. When branching, don't add a free option if the codom is non-limit
2. When merging (due to funeq or patheq), fail if two non-limit items are merged
"""
const rigid = true

# Type synonyms
###############
const ACDict = Dict{UInt64, Pair{StructACSet, ChaseStepData}}
const Poss = Tuple{Symbol, Int, Int, Modify}
const LoneCones = Dict{Symbol,Set{Int}}

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
                    )::Union{Nothing,Pair{StructACSet,Vector{Poss}}}
  verbose = false
  J = deepcopy(J)
  m, lc = Modify(), LoneCones()
  cnt = 0

  while true
    cnt+=1
    pi_res = propagate_info(S, J)
    if isnothing(pi_res) return nothing end
    J_new, m_new, lc_new = pi_res
    # println("NEW LC $new_lc\n$(isempty(m_old)) $(m_new==m) && $(new_lc==lc) && $(eqclass_eq(new_eq, eq))")
    should_break = (J==J_new) && (m_new==m) && (lc_new==lc)
    J, m, lc = (J_new, m_new, lc_new) # overwrite
    if should_break
      break # exit loop once we have no more changes
    end
    if cnt > 1 println("\tchase step, finished loop iter #$cnt") end
  end
  J_res = update_crel(J, m) # add new things that make J bigger
  if verbose
    println("J Res "); show(stdout, "text/plain", crel_to_cset(S, J_res)[1])
  end

  # temp sanity check: elements identified as cocone orphans actually exist
  for (k, vs) in lc
    all([v > 0 && v <= nparts(J_res, k) for v in vs]) || error(string(lc))
  end

  poss = filter(x->!isempty(x), get_possibilities(S, J_res, lc))
  println("$(length(poss)) possibilities")
  return J_res => isempty(poss) ? Poss[] : first(sort(poss, by=length))
end


"""
Use path equalities, functionality of FK relations, cone/cocone constraints to
generate new data and to quotient existing data. Separate information that can
be safely applied within a while loop (i.e. everything except for things
related to newly added elements).
"""
function propagate_info(S::Sketch, J::StructACSet
                        )::Union{Nothing,
                                 Tuple{StructACSet, Modify, LoneCones}}
  verbose = false
  eq = init_eq(S, J) # trivial equivalence classes

  if path_eqs!(S,J,eq)
    return nothing
  end

  cdata = compute_cones!(S, J, eq)
  if isnothing(cdata) return nothing end
  if verbose println("cdata $cdata") end

  # Compute cocones, which has possibility of immediately failing
  cocone_res = compute_cocones!(S, J, eq)
  if isnothing(cocone_res) return nothing end
  ccdata, lone_cones = cocone_res
  m = union(S, J, cdata, ccdata)

  # because this is at the end, chased premodels should be functional
  if fun_eqs!(S,J,eq)
    return nothing
  end

  merge!(S, J, eq)
  crel_to_cset(S, J) # fail if it's nonfunctional

  return (J, m, lone_cones)
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
                           )::Vector{Vector{Poss}}
  res = Vector{Poss}[]
  cols = [:elabel, [:src, :vlabel], [:tgt, :vlabel]]
  # Dangling foreign keys ('tuple generating dependencies')
  for (e, src_tab, tgt_tab) in zip([S.schema[x] for x in cols]...)
    esrc, _ = add_srctgt(e)
    unmatched = setdiff(parts(J,src_tab), J[esrc])
    for u in unmatched
      # possibilities of setting `u`'s value of FK `e`
      subres = Poss[]

      # First possibility: a `e` sends `u` to a fresh ID
      if !(rigid && tgt_tab ∈ realobs(S))
        mu = Modify()
        new_offset = mu.newstuff[tgt_tab] += 1
        push!(mu.update, (e, u, nparts(J, tgt_tab) + new_offset))
        push!(subres, (e, u, 0, mu))
      end
      # Remaining possibilities (check satisfiability w/r/t cocones/cones)
      for p in 1:nparts(J,tgt_tab)
        m = Modify()
        push!(m.update, (e, u, p))
        push!(subres, (e, u, p, m))
      end
      push!(res, subres)
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
      if !(rigid && srctab ∈ realobs(S))
        fresh = Modify()
        new_offset = fresh.newstuff[srctab] += 1
        push!(fresh.update, (leg, nparts(J, srctab) + new_offset, val))
        push!(subres, (leg, nparts(J, srctab) + new_offset, val, fresh))
      end
      # Consider existing elements for which this leg has not yet been set
      for u in setdiff(parts(J, srctab), J[src_fk])
        m = Modify()
        push!(m.update, (leg, u, val))
        push!(subres, (leg, u, val, m))
      end
    end
    push!(res, subres)
  end
  return res
end

# DB
####

"""Explore a premodel and add its results to the DB."""
function chase_step_db(db::LibPQ.Connection, premodel_id::Int; redo::Bool=false
                       )::Pair{Bool, Vector{Int}}
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
  println("\n\nCHASING PREMODEL #$premodel_id: $(sizes(S, J_))")
  # show(stdout, "text/plain", crel_to_cset(S, J_)[1])
  cs_res = chase_step(S, create_premodel(S, J_))

  # Failure
  if isnothing(cs_res)
    set_failed(db, premodel_id, true)
    return false => Int[]
  end

  # Success
  set_failed(db, premodel_id, false)

  J, m = cs_res
  println("\tChased premodel: $(sizes(S, J))")
  # show(stdout, "text/plain", crel_to_cset(S, J)[1])
  chased_id = add_premodel(db, S, J; parent=premodel_id)

  # Check we have a real model
  if isempty(m)
    println("\t\tFOUND MODEL")
    return true => [add_model(db, S, J, chased_id)]
  else
    # Branch
    # println("\tBranching on $([(e,i,j) for (e,i,j,_) in m])")
    res = Int[]
    for (e,i,j,mod) in m
      J__ = update_crel(J, mod)
      push!(res, add_branch(db, S, string((e,i,j)), chased_id, J__))
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
  for combo in combos_below(length(realobs(S)), n)
    ps = mk_pairs(collect(zip(realobs(S), combo)))
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
      [chase_step_db(db, mdl) for mdl in todo]
    end
  end
end


# Colimits
##########

"""
Add cocone apex objects based on the cocone diagram. Modifies `eq`

For example: a cocone object D over a span B <- A -> C (i.e. a pushout)

We start assuming there is a cocone element for |A|+|B|+|C| and then quotient
by each arrow in the diagram. Assume each set has two elements, so we initially
suppose D = |6|. Let A->B map both elements to b₁, while A↪C.

D   legA legB legC
------------------
a₁  {a₁}   ?    ?
a₂  {a₂}   ?    ?
b₁   ?   {b₁}   ?
b₂   ?   {b₂}   ?
c₁   ?    ?    {c₁}
c₂   ?    ?    {c₂}

Take the map component that sends a₁ to b₁. The result will be
D  legA legB legC
-------------------
a₁b₁ {a₁} {b₁}   ?
a₂   {a₂}  ?     ?
b₂    ?   {b₂}   ?
c₁    ?    ?    {c₁}
c₂    ?    ?    {c₂}

After all the quotienting (assuming all map components are defined), we get
  D     legA   legB   legC
------------------------------
a₁a₂b₁c₁c₂  {a₁a₂} {b₁}  {c₁c₂}
b₂            ?    {b₂}    ?

If certain pieces of data are not yet defined (e.g. a₁↦c₁), we may have
overestimated the size of the cocone, but when we later learn that map
information, then the elements in D (a₁c₂ and a₂b₁c₂) will be merged together.
So we get an upper bound on the number of elements of the apex object.

This data combines with existing elements in D and any leg data (A->D,B->D,C->D)
that may exist. Every table in the diagram potentially has a leg into the apex.
We consider all possibilities:
0.) None of the legs are defined (then: add a fresh element to D & set the legs)
1.) All legs within a given group map to the same element in D (nothing to do)
2.) Same as above, except some are undefined (then: set the undefined ones to
    the known value from the other ones)
3.) Distinct values of the apex are mapped to by legs. The only way for this to
    be consistent is if we merge the values in the apex.

There are also possibilities to consider from the apex side:
1.) An apex element has a diagram group associated with it (nothing to do)
2.) An apex element has NO group assigned to it (we need to consider
    all the possibilities for a new element (in one of the legs) mapping
    to it. This makes cocones different from cones: for cones, an unknown cone
    element will have its possibilities resolved by ordinary branching on possible
    FK values, whereas with cocones we have add a distinctive kind of branching.
3.) Multiple groups may be assigned to the SAME apex element. This cannot be
    fixed in general by merging/addition in the way that limit sketch models can
    be. Thus we need a way to fail completely (given by the `nothing` option).
"""
function compute_cocones!(S::Sketch, J::StructACSet, eq::EqClass
                         )::Union{Nothing, Pair{Modify,LoneCones}}
  new_update, lone_cone = Modify(), LoneCones()
  for c in S.cocones
    res = compute_cocone!(S, J, c, new_update, eq)
    if isnothing(res)
      return nothing
    end
    lone_cone[c.apex] = res
    all([v <= nparts(J, c.apex) for v in lone_cone[c.apex]]) || error(
      string(lone_cone))
  end
  return new_update => lone_cone
end

"""
Updates `m` and `eq`

Unlike cones, where knowing partial maps can give you matches, we require all
maps in a cocone diagram to be completely known in order to determine cocone
elements.
"""
function compute_cocone!(S::Sketch, J::StructACSet, co_cone::Cone,
                         m::Modify, eqc::EqClass)::Union{Nothing, Set{Int}}
  verbose=false
  J_orig = deepcopy(J)
  nu, up = m.newstuff, m.update
  diag_objs = co_cone.d[:vlabel]
  diag_homs = ne(co_cone.d)== 0 ? Tuple{Symbol,Int,Int}[] :
    collect(zip([co_cone.d[x] for x in [:elabel, :src,:tgt]]...))

  # Get unquotiented apex: all distinct elements for each table involved
  apex_obs = vcat([[(i, v) for v in eq_reps(eqc[obj])]
                   for (i, obj) in enumerate(diag_objs)]...)
  # Get the apex objs index from the (tab_ind, elem_ind) value itself
  apex_ob_dict = Dict([(j,i) for (i,j) in enumerate(apex_obs)])
  # Equivalence class of `apex_obs`
  eq_elems = IntDisjointSets(length(apex_obs))

  # Check if all homs are total before moving on
  for e in Set(vcat(co_cone.d[:elabel])) # , last.(co_cone.legs)))
    sreps = [find_root!(eqc[src(S,e)],x) for x in J[add_srctgt(e)[1]]]
    missin = setdiff(eq_reps(eqc[src(S,e)]), sreps)
    if !isempty(missin)
      println("cannot compute cocone bc $e does not map $missin anywhere")
      return Set{Int}()
    end
  end

  # Use C-set map data to quotient this
  if verbose println("diag homs $diag_homs") end
  for (e, i, j) in diag_homs
    esrc, etgt = add_srctgt(e)
    stab, ttab = src(S, e), tgt(S,e)
    for (x_src, x_tgt) in zip([J[x] for x in [esrc, etgt]]...)
      is, it = find_root!(eqc[stab], x_src), find_root!(eqc[ttab], x_tgt)
      s, t = [apex_ob_dict[v] for v in [(i, is), (j, it)]]
      union!(eq_elems, s, t)
    end
  end

  # Reorganize equivalence class data into a set of sets.
  eqsets = eq_sets(eq_elems; remove_singles=false)

  # Determine what apex element(s) each eq class corresponds to, if any
  apex_tgt_dict = Dict()
  for eqset in eqsets
    # ignore eqsets that have no leg/apex values
    eqset_vals = [apex_obs[i] for i in eqset]
    eqset_tabs = first.(eqset_vals)
    if isempty(eqset_tabs ∩ vcat([co_cone.apex],first.(co_cone.legs)))
      # println("Eqset disconnected from apex, ignoring $eqset_vals")
      apex_tgt_dict[eqset] = Int[]
      continue
    end

    # sanity check: no table appears more than once in an eq class
    for i in Set(first.(eqset_vals))
      length(filter(==(i), first.(eqset_vals))) <= 1 || "eqset_vals $eqset_vals"
    end

    if verbose println("eqset_vals $eqset_vals") end

    leg_vals = Tuple{Symbol,Int,Int}[]
    for (leg_ind, leg_name) in co_cone.legs
      ind_vals = collect(last.(filter(v->v[1]==leg_ind, eqset_vals)))
      if length(ind_vals) == 1
        ind_val = only(ind_vals)
        l_src, l_tgt = add_srctgt(leg_name)
        a_tgt = J[incident(J, ind_val, l_src), l_tgt]
        if !isempty(a_tgt)
          # println("$(incident(J, ind_val, l_src)) a tgt $a_tgt")
          ap = find_root!(eqc[co_cone.apex], first(a_tgt))
          push!(leg_vals, (leg_name, ind_val, ap))
        end
      end
    end
    apex_tgts = apex_tgt_dict[eqset] = collect(Set(last.(leg_vals)))

    # Handle things different depending on how many apex_tgts the group has
    if length(apex_tgts) == 0 # we have a new element to add
      nu[co_cone.apex] += 1
      apex_rep = nparts(J, co_cone.apex) + nu[co_cone.apex]
    # We have a cocone object with nothing mapping into it. Need to branch.
    elseif length(apex_tgts) == 1 # eqset is consistent
      apex_rep = only(apex_tgts)
    else # eqset is consistent only if we merge apex vals
      apex_rep = minimum(apex_tgts)
      if length(apex_tgts) > 1 # we have to merge elements of apex
        unions!(eqc[co_cone.apex], collect(apex_tgts))
        println("computing cocone $(co_cone.apex) unioned indices $apex_tgts")

      end
    end

    # Update `src(leg)` (index # `l_val`) to have map to `apex_rep` via `leg`
    for (leg_ind, leg_name) in co_cone.legs
      ind_vals = collect(last.(filter(v->v[1]==leg_ind, eqset_vals)))
      if length(ind_vals) == 1
        ind_val = only(ind_vals)
        if length(apex_tgts)==0
          println("Cocone added $leg_name: $ind_val -> $apex_rep (fresh)")
          push!(up, (leg_name, ind_val, apex_rep))
        elseif !has_map(S, J, leg_name, ind_val, apex_rep, eqc)
          println("Cocone added $leg_name: $ind_val -> $apex_rep")
            add_rel!(J, leg_name, ind_val, apex_rep)
        end
      else
        isempty(ind_vals) || error("")
      end
    end
  end

  # Fail if necessarily distinct groups map to the same apex element
  for es in filter(x->x[1]!=x[2], collect(Iterators.product(eqsets, eqsets)))
    tgts1, tgts2 = [apex_tgt_dict[e] for e in es]
    conflict = intersect(tgts1, tgts2)
    if !isempty(conflict)
      evals1, evals2 = [[apex_obs[i] for i in e] for e in es]
      println("FAILING b/c $evals1 and $evals2 both map to $conflict ")
      show(stdout, "text/plain",  J_orig)
      return nothing
    end
  end

  seen_apex_tgts = union(values(apex_tgt_dict)...)
  return Set(collect(setdiff(parts(J, co_cone.apex), seen_apex_tgts)))
end

# Limits
########

"""
Add cone apex objects based on conjunctive queries.

For example: a cone object D over a cospan B -> A <- C (i.e. a pullback)

Imagine all sets have two elements. If B maps both elements to a₁ and C ↪ A,
then a conjunctive query looking for instances of the diagram should return:

QueryRes A  B  C
----------------
    1    a₁ b₁ c₁
    2    a₁ b₂ c₁

Because the functions are partial in the premodel, there may be limit objects
that will be discovered to exist (by merging elements or adding new connections)
So the query result is a lower bound on the number of elements in the apex.

This means we expect there to be two objects in the limit object D.
If an element already exists with the same legs, then we are good. If an element
that disagrees with one of the legs exists, then we need to add a new element.
If is an element with information that partially matches a query result, we
still add a new element but note that these two may be merged at a later point.

"""
function compute_cones!(S::Sketch, J::StructACSet, eq::EqClass)::Modify
  m = Modify()
  [compute_cone!(S, J, c, m, eq) for c in S.cones]
  return m
end

"""Special case treated separately. Modifies `m` and `eq`"""
function empty_cone!(J::StructACSet, apx::Symbol, m::Modify, eq::EqClass)
  if nparts(J, apx) == 0
    m.newstuff[apx] = 1
  else
    unions!(eq[apx], collect(parts(J, apx)))
  end
end

"""
Modifies `m` and `eq`

Check/enforce the following cone properties in this order:
1. Two cone apex elements are equal if their corresponding leg values match.
2. Same as (1), but in the other direction.
3. For every pattern match of the cone's diagram in J, there is a cone element.

(1)/(2) update `eq`, whereas information from (3) is added to the `Modify`

Dream: we can somehow only query 'newly added' information
"""
function compute_cone!(S::Sketch, J::StructACSet, cone_::Cone, m::Modify,
                       eq::EqClass)::Nothing
  if isempty(cone_.legs)
    return empty_cone!(J, cone_.apex, m, eq)
  end
  verbose = false
  nu, upd = m.newstuff, m.update
  cones = cone_eqs!(S, J, cone_, eq)
  if isnothing(cones) return nothing end
  if verbose println("CURRENT CONE $cones") end
  # look for instances of the pattern
  query_results = query_cone(S, J, cone_, eq) #query(J, cone_query(cone_))
  for res in query_results
    length(res) == length(cone_.legs) || error("Bad res $res from query")
    resv = Vector{Int}(collect(res))
    # For any new diagram matches that we do not have an explicit apex elem for:
    if !haskey(cones, resv)
      println("ADDING NEW cone apex $(cone_.apex) b/c $resv not found in $cones")
      new_offset = nu[cone_.apex] += 1
      for (f, v) in zip(last.(cone_.legs), resv)
        push!(upd, (f, nparts(J, cone_.apex) + new_offset, v))
      end
    else
      # anything to do?
    end
  end
end


"""Look for instances of a cone's diagram in a premodel"""
function query_cone(S,J,c,eq)::Vector{Vector{Int}}
  res = [[]]
  verbose=  false
  for (i, tab) in enumerate(c.d[:vlabel])
    if verbose println("i $i tab $tab") end
    new_res = Vector{Int}[]
    if isempty(res) return Vector{Int}[] end
    # we could product our options with this set, but let's filter now
    eqs = eq_reps(eq[tab])

    # We can immediately filter possible values based on self-edges in diagram
    for self_e in incident(c.d, i, :tgt) ∩ incident(c.d, i, :src)
      eqs = filter(x -> has_map(S, J, c.d[self_e, :elabel], x, x, eq), eqs)
    end
    # any edges from tables we've seen so far into this current one constrain us
    es = filter(e->c.d[e, :src] < i, incident(c.d, i, :tgt))
    for old_res in res
      for new_val in eqs
        fail = false
        for e in es
          e_name, e_src = [c.d[e, x] for x in [:elabel, :src]]
          if !has_map(S, J, e_name, old_res[e_src], new_val, eq)
            if verbose println("No match: or $old_res, nv $new_val, e $e") end
            fail = true
            break
          end
        end
        if !fail
          push!(new_res, vcat(old_res, [new_val]))
        end
      end
    end
    res = new_res
  end
  return unique([[subres[i] for i in first.(c.legs)] for subres in res])
end

"""
Start with equivalence classes of apex elements. Make the corresponding leg
elements equal.
Use the equivalences of cone apex elements to induce other equivalences.
Return whether the resulting model is *un*satisfiable (if certain merging is
forbidden). Modifies `eq`
"""
function cone_eqs!(S::Sketch, J::StructACSet, c::Cone, eq::EqClass
                  )::Union{Nothing, Dict{Vector{Int}, Int}}
  eqclasses_legs = Vector{Int}[]
  apex_elems = eq_reps(eq[c.apex])
  legnames = last.(c.legs)
  legtabs = [tgt(S, leg) for leg in legnames]
  for eqs in apex_elems
    eqclass_legs = Int[]
    for (tab, leg) in zip(legtabs, legnames)
      s, t = add_srctgt(leg)
      legvals = Set(vcat(J[incident(J, eqs, s), t]...))
      if length(legvals) == 1
        [add_rel!(J, leg, e, only(legvals)) for e in eqs]
        push!(eqclass_legs, only(legvals))
      elseif isempty(legvals)
        push!(eqclass_legs, 0)
      elseif length(legvals) > 1
        # all the elements in this leg are equal
        if rigid && tab ∈ realobs(S)
          println("CONE EQ $eqs leg $leg merges $tab elements: $legvals")
          return nothing
        else
          unions!(eq[tab], legvals)
          push!(eqclass_legs, first(legvals))
        end
      end
    end
    push!(eqclasses_legs, eqclass_legs)
  end
  # Now quotient the apex elements if they have the same legs
  res = Dict{Vector{Int}, Int}()
  for (eqc, eqcl) in zip(apex_elems, eqclasses_legs)
    if minimum(eqcl) > 0
      lv = [find_root!(eq[tab], v) for (tab, v) in zip(legtabs, eqcl)]
      if haskey(res, lv)
        union!(eq[c.apex], eqc, res[lv])
      else
        res[lv] = eqc
      end
    end
  end
  return res
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

(could be parallelized)
"""
function fun_eqs!(S::Sketch, J::StructACSet, eqclass::EqClass)::Bool
  cols = [:elabel, [:src, :vlabel], [:tgt, :vlabel]]
  for (d, srcobj, tgtobj) in zip([S.schema[x] for x in cols]...)
    dsrc, dtgt = add_srctgt(d)
    srcobj, tgtobj = src(S, d), tgt(S,d)
    for src_eqset in collect.(eq_sets(eqclass[srcobj]; remove_singles=false))
      tgtvals = Set(J[vcat(incident(J, src_eqset, dsrc)...), dtgt])
      if length(tgtvals) > 1
        if rigid && tgtobj ∈ realobs(S)
          println("Fun Eq of $d (src: $src_eqset) merges $tgtobj: $tgtvals")
          show(stdout, "text/plain", J)
          return true
        else
          unions!(eqclass[tgtobj], collect(tgtvals))
        end
      end
    end
  end
  return false
end


"""
Modifies J and eqclasses.

If we have two paths A->B, p₁₁...p₁ₙ and p₂₁...p₂ₙ, then, if, for a starting
point in A:
1.) one of the paths is completely determined
2.) the other path is determined entirely except for the last relation

We can set the value of the last relation to the value of the determined one.

If both paths are determined, the final terms can be set to be equivalent, if
this is allowed (otherwise, return `true`).
"""
function path_eqs!(S::Sketch, J::StructACSet, eqclasses::EqClass)::Bool
  verbose = true
  for (eqn, p, q) in S.eqs # could be done in parallel
    if verbose println("processing equality $eqn") end
    src_tab, tgt_tab = src(S, p[1]), tgt(S, p[end])
    eqc = eq_reps(eqclasses[src_tab])
    for x in eqc # can be parallel
      res_p, is_penult_p = eval_path(p, J, x)
      res_q, is_penult_q = eval_path(q, J, x)
      if verbose println("""x $x res_p $res_p (is_penult $is_penult_p)
        res_q $res_q (is_penult $is_penult_q)""") end
      real_p, real_q = (!isnothing).([res_p, res_q])
      if is_penult_p && real_q && !is_penult_q
        println("$eqn (rev) set $(last(p)): $res_p -> $res_q")
        add_rel!(J, last(p), res_p, res_q)
      elseif is_penult_q && real_p && !is_penult_p
        println("$eqn (fwd) set $(last(q)): $res_q -> $res_p")
        add_rel!(J, last(q), res_q, res_p)
      elseif real_p && real_q && !(is_penult_p || is_penult_q) && (res_p!=res_q)
        if rigid && tgt_tab ∈ realobs(S)
          println("Fail: tried to equate $tgt_tab #$res_p and $res_q")
          return true
        else
          println("$eqn set $tgt_tab: $res_p == $res_q")
          union!(eqclasses[tgt_tab], res_p, res_q)
        end
      end
    end
  end
  return false
end

"""
Compose relations starting as functions.

Because `eq_fun` quotients by functionality, we only need to pick, for a
relation A->B and  aᵢ, a single related bⱼ (if any exists).

This process terminates when nothing is related in the codomain. If this happens
right before the *last* relation, then we note this with a `true` boolean flag.
"""
function eval_path(pth::Vector{Symbol}, J::StructACSet, x::Int
                   )::Pair{Union{Nothing, Int}, Bool}
  prev_x = x
  for (i, m) in enumerate(pth)
    msrc, mtgt = add_srctgt(m)
    if isnothing(x)
      return nothing => false
    else
      prev_x, inc = x, incident(J, x, msrc)
      x = isempty(inc) ? nothing : J[first(inc), mtgt]
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
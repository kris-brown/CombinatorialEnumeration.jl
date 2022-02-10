module Limits
export Weights, LoneCones, compute_cones!, compute_cocones!, query_cone

using ..Sketches
using ..Models

using Catlab.CategoricalAlgebra
using DataStructures
const Weights = DefaultDict{Pair{Symbol, Int}, Float64}
const LoneCones = Dict{Symbol,Set{Int}}

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
So the query result is a *lower* bound on the number of elements in the apex.

This means we expect there to be two objects in the limit object D.
If an element already exists with the same legs, then we are good. If an element
that disagrees with one of the legs exists, then we need to add a new element.
If is an element with information that partially matches a query result, we
still add a new element but note that these two may be merged at a later point.

"""
function compute_cones!(S::Sketch, J::StructACSet, eq::EqClass, #ns::NewStuff,
                        d::Defined)::Tuple{Bool,Bool}
  changed = false
  for c in filter(c -> c.apex ∉ d[1], S.cones)
    cchanged, cfail = compute_cone!(S, J, c, eq, d)
    changed |= cchanged
    if cfail return (changed, true, m) end
  end
  return changed, false
end

"""
Modifies `m`, `eq`, and `d`

Check/enforce the following cone properties in this order:
1. Two cone apex elements are equal if their corresponding leg values match.
2. Same as (1), but in the other direction.
3. For every pattern match of the cone's diagram in J, there is a cone element.

If we do this process and all objects/arrows in the cone's diagram are defined,
then the limit object itself is fully defined (cannot change in cardinality).

(1)/(2) update `eq`, whereas information from (3) is added to the `Modify`

Dream: we can somehow only query 'newly added' information

Returns whether it changed anything and whether it failed.
"""
function compute_cone!(S::Sketch, J::StructACSet, cone_::Cone,
                       eq::EqClass, d::Defined)::Pair{Bool, Bool}
  cone_.apex ∉  d[1] || error("don't compute cone for something defined! $J $d")
  verbose, changed = false, false
  cchange, cfail, cones = cone_eqs!(S, J, cone_, eq, d)
  changed |= cchange
  if cfail return changed => true end
  # look for instances of the pattern
  query_results = query_cone(S, J, cone_, eq) #query(J, cone_query(cone_))
  for res in query_results
    length(res) == length(cone_.legs) || error("Bad res $res from query")
    resv = Vector{Int}(collect(res))
    # For any new diagram matches that we do not have an explicit apex elem for:
    if !haskey(cones, resv)
      ne = add_part!(J, cone_.apex)
      for (f, v) in zip(last.(cone_.legs), resv)
        add_rel!(S, J, d, f, ne, v)
      end
      changed=true
      # If we don't already have a NewElem with these legs...
      # new_elms = collect(values(ns.ns[cone_.apex]))
      # if verbose
      #   println("Checking if res $res is in existing ns $(new_elms)")
      # end
      # if !any([all([in_same_set(eq[tgt(S,f)], ne.map_out[f], c.map_out[f])
      #          for f in last.(cone_.legs)]) for c in new_elms])
      #   changed = true
      #   if verbose println("NEW APEX $res") end
      #   ns.ns[cone_.apex][resv] = ne
      # end
    else
      # anything to do?
    end
  end
  return changed => false
end


"""
Look for instances of a cone's diagram in a premodel
Modifies w
"""
function query_cone(S::Sketch, J::StructACSet, c::Cone, eq::EqClass,
                   )::Vector{Vector{Int}}
  res = [[]]
  verbose =  false
  for (i, tab) in enumerate(c.d[:vlabel])
    if verbose println("i $i tab $tab\n\tres $res") end
    new_res = Vector{Int}[]
    if isempty(res) return Vector{Int}[] end
    # we could product our options with this set, but let's filter now
    eqs = eq_reps(eq[tab])

    # We can immediately filter possible values based on self-edges in diagram
    for self_e in incident(c.d, i, :tgt) ∩ incident(c.d, i, :src)
      self_e_name = c.d[self_e, :elabel]
      eqs = filter(x -> has_map(S, J, self_e_name, x, x, eq), eqs)
    end
    # any edges w/ tables we've seen so far in/out of current one constrain us
    es_in = filter(e->c.d[e, :src] < i, incident(c.d, i, :tgt))
    es_out =filter(e->c.d[e, :tgt] < i, incident(c.d, i, :src))
    for old_res in res
      for new_val in eqs
        fail = false
        for e in es_in
          e_name, e_src = [c.d[e, x] for x in [:elabel, :src]]
          if !has_map(S, J, e_name, old_res[e_src], new_val, eq)
            if verbose println("No match: or $old_res, nv $new_val, e $e") end
            fail = true
            break
          end
        end
        for e in (fail ? [] : es_out)
          e_name, e_tgt = [c.d[e, x] for x in [:elabel, :tgt]]
          if !has_map(S, J, e_name, new_val, old_res[e_tgt], eq)
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
forbidden).

Modifies `eq` and `w`.
"""
function cone_eqs!(S::Sketch, J::StructACSet, c::Cone, eq::EqClass, d::Defined,
                  )::Tuple{Bool, Bool, Dict{Vector{Int}, Int}}
  changed, verbose = false, false
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
        [add_rel!(S, J, d, leg, e, only(legvals)) for e in eqs]
        push!(eqclass_legs, only(legvals))
      elseif isempty(legvals)
        push!(eqclass_legs, 0)
      elseif length(legvals) > 1
        # all the elements in this leg are equal
        if tab ∈ d[1]
          return (changed, true, Dict{Vector{Int}, Int}())
        else
          for (lv1, lv2) in Iterators.product(legvals, legvals)
            if !in_same_set(eq[tab], lv1, lv2)
              changed = true
              union!(eq[tab], lv1, lv2)
            end
          end
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
        if !in_same_set(eq[c.apex], eqc, res[lv])
          if verbose
            println("$(c.apex) elements have the same legs: $eqc $(res[lv])")
          end
          changed = true
          union!(eq[c.apex], eqc, res[lv])
        end
      else
        res[lv] = eqc
      end
    end
  end
  return (changed, false, res)
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
function compute_cocones!(S::Sketch, J::StructACSet, eq::EqClass,
                          d::Defined)::Tuple{Bool,Bool,LoneCones}
  changed, lone_cone = false, LoneCones()
  for c in filter(c->c.apex ∉ d[1], S.cocones)
    cchanged, cfailed, res = compute_cocone!(S, J, c, eq, d)
    if cfailed return (changed, true, lone_cone) end
    changed |= cchanged
    lone_cone[c.apex] = res  # assumes there aren't multiple cones on same vert
  end
  return (changed, false, lone_cone)
end

"""
Unlike cones, where knowing partial maps can give you matches, we require all
maps in a cocone diagram to be completely known in order to determine cocone
elements.

Updates `m` and `eq` and `d`
"""
function compute_cocone!(S::Sketch, J::StructACSet, co_cone::Cone,
                         eqc::EqClass, d::Defined)::Tuple{Bool,Bool, Set{Int}}
  co_cone.apex ∉ d[1] || error("Don't compute cocone that's defined $J $d")
  verbose, changed = false, false
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
      # println("cannot compute cocone bc $e does not map $missin anywhere")
      return changed, false, Set{Int}()
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

    # Now that we know this eqset maps to apex elements, we set their leg maps
    # to this apex value.
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
      ne = NewElem()
    # We have a cocone object with nothing mapping into it. Need to branch.
    elseif length(apex_tgts) == 1 # eqset is consistent
      apex_rep = only(apex_tgts)
    else # eqset is consistent only if we merge apex vals
      apex_rep = minimum(apex_tgts)
      if length(apex_tgts) > 1 # we have to merge elements of apex
        unions!(eqc[co_cone.apex], collect(apex_tgts))
        if verbose
          println("computing cocone $(co_cone.apex) unioned indices $apex_tgts")
        end
      end
    end

    # Update `src(leg)` (index # `l_val`) to have map to `apex_rep` via `leg`
    for (leg_ind, leg_name) in co_cone.legs
      for ind_val in collect(last.(filter(v->v[1]==leg_ind, eqset_vals)))
        if length(apex_tgts)==0
          #println("Cocone added $leg_name: $ind_val -> $apex_rep (fresh)")
          push!(ne.map_in[leg_name], ind_val)
        elseif !has_map(S, J, leg_name, ind_val, apex_rep, eqc)
          if verbose
            println("Cocone added $leg_name: $ind_val -> $apex_rep")
          end
          changed = true
          add_rel!(S, J, d, leg_name, ind_val, apex_rep)
        end
      end
    end

    if length(apex_tgts)==0
      new_ind = add_part!(J, co_cone.apex)
      for (k, vs) in ne.map_in
        for v in vs
          add_rel!(S, J, d, k, v, new_ind)
        end
      end
        changed = true
      end
    end

  # Fail if necessarily distinct groups map to the same apex element
  eqset_pairs = collect(Iterators.product(eqsets, eqsets))
  for es in filter(x->x[1]!=x[2], eqset_pairs)
    tgts1, tgts2 = [apex_tgt_dict[e] for e in es]
    conflict = intersect(tgts1, tgts2)
    if !isempty(conflict)
      return changed, true, Set{Int}()
    end
  end

  seen_apex_tgts = (isempty(apex_tgt_dict) ? Set{Int}()
                                           : union(values(apex_tgt_dict)...))

  return changed, false, Set(
    collect(setdiff(parts(J, co_cone.apex), seen_apex_tgts)))
end
end # module
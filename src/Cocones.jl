
# Colimits
##########


propagate_cocones!(S::Sketch,J::SketchModel,f::CSetTransformation,ch::Change) =
  vcat([propagate_cocone!(S, J, f, i, ch) for i in 1:length(S.cocones)]...)


"""
Rebuild the cocone equivalence classes (across different tables) from scratch.
This could be made more incremental using the change + the old cocone data
"""
function update_cocones!(S::Sketch,J::SketchModel,f::ACSetTransformation,_)
  new_cocones = map(zip(S.cocones, J.cocones)) do (c, (_,_))

    # create new aggregation of all tables in the cocone diagram
    cdict = Pair{Symbol, Int}[]
    for v in unique(vlabel(c.d))
      for p in parts(J.model, v) push!(cdict, v => p) end
    end
    cdict_inv = Dict([v=>i for (i,v) in enumerate(cdict)])
    new_eq = IntDisjointSets(length(cdict))

    # merge elements based on eq
    for (v, veq) in J.eqs
      for eqset in collect.(eq_sets(veq; remove_singles=true))
        e1, rest... = collect(eqset)
        [union!(new_eq, cdict_inv[v=>e1], cdict_inv[v=>i]) for i in rest]
      end
    end

    # Quotient by maps in the diagram
    for h in unique(elabel(c.d))
      sT, tT, (hsrc, htgt) = src(S,h), tgt(S,h), add_srctgt(h)
      for (s,t) in zip(J.model[hsrc], J.model[htgt])
        union!(new_eq, cdict_inv[sT=>s], cdict_inv[tT=>t])
      end
    end
    return new_eq => cdict
  end

  J.cocones = new_cocones
end

"""
We assume that the cocone data (of connected components in the category of
elements) has already been updated in update_cocones!.

There are two ways to perform cocone constraint inference:
1.) If two elements map to the same cocone element that are in a connected
    component, then the cocone elements must be merged.

2.) If two objects in distinct connected components map to the same cocone apex
    element, then we must fail if it is not possible for some future assignment
    of foreign keys to put them in the same connected component.
"""
function propagate_cocone!(S::Sketch, J::SketchModel,f::CSetTransformation, ci::Int,  c::Change)
  verbose = false
  cc, (ccdata, cd), res = S.cocones[ci], J.cocones[ci], Change[]
  if verbose println("updating cocone $ci with apex $(cc.apex) po data $(J.cocones)") end

  # We care about, ∀ connected components, which apexes are mapped to
  ap_to_cc = DefaultDict(()->Set{Int}()) # ap₁ -> [cc₁,cc₂,...]
  # We care about, ∀ apexes, which connected components map to it
  cc_to_ap = DefaultDict(()->Set{Int}()) # cc₁ -> [ap₁, ap₂,...]
  for l in last.(cc.legs)
    for p in parts(J.model, src(S,l))
      ap = fk(S, J.model, l, p)
      if !isnothing(ap)
        ccmp = find_root!(ccdata, findfirst(==(src(S, l)=>p), cd))
        push!(ap_to_cc[ap], ccmp)
        push!(cc_to_ap[ccmp], ap)
      end
    end
  end
  # 1.) check for apex elements that should be merged
  for vs in collect.(filter(x->length(x)>1, collect(values(cc_to_ap))))
    if verbose println("MERGING COCONE APEX ELEMS $vs") end
    push!(res, Merge(S,J,Dict(cc.apex=>[vs])))
  end
  # 2.) check for connected components that cannot possibly be merged
  startJ = project(S,merge_eq(S,J.model,J.eqs), cc)

  for vs in collect.(filter(x->length(x)>1, collect(values(ap_to_cc))))
    if !connection_possible(S, startJ, cc, ccdata, cd, vs)
      throw(ModelException())
    end
  end

  res
end


"""
Check if there exists a foreign key assignment that connects n sets of elements
in a C-Set.
"""
function connection_possible(S::Sketch,J_orig::StructACSet,
                             cocone::Cone,
                             conn_orig::IntDisjointSets{Int},
                             conndict::Vector{Pair{Symbol,Int}},
                             comps::Vector{Int})
  verbose = false
  if verbose println("are $comps mergable ?") end
  connd = Dict(v=>k for (k,v) in enumerate(conndict))
  is_tot(J,e) = length(unique(J[add_src(e)])) == nparts(J, src(S,e))
  queue = [J_orig=>conn_orig]
  while !isempty(queue)
    J, conn = pop!(queue)
    if verbose println("popping $conn (in queue: $(length(queue)))") end
    es = [e for e in unique(elabel(cocone.d)) if !is_tot(J,e)]
    if isempty(es) continue end # this branch cannot branch further
    e = first(es) # or some more intelligent way to pick one?
    (se, te), sT, tT = add_srctgt(e), src(S,e), tgt(S,e)
    if verbose println("\tbranch on $e:$sT->$tT") end
    undefd = first(collect(setdiff(parts(J, sT), J[se])))
    u_ind = connd[sT=>undefd]
    u_cc = find_root!(conn, u_ind)
    if verbose println("\tlooking for fk targets for $sT#$undefd") end
    for p in parts(J,tT) # we actually only need to consider distinct orbits
      if verbose println("\tconsidering ->$tT#$p") end
      p_ind = connd[tT=>p]
      p_cc = find_root!(conn, p_ind)
      if u_cc != p_cc
        J_, conn_ = deepcopy.([J, conn])
        add_part!(J_, e; Dict(zip([se,te],[undefd,p]))...)
        union!(conn_, u_ind, p_ind)
        if length(unique([find_root!(conn_, x) for x in comps])) == 1
          return true
        else
          push!(queue, J_=>conn_)
        end
      end
    end
  end
  return false # no more branching options, comps still unconnected
end

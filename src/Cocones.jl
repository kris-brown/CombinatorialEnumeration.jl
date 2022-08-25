using ..Models: is_surjective
# Colimits
##########


"""
Propagate cocone information for cocones that are not frozen.
If the previous change added a leg element (which may have frozen the leg) we
want to run the checks again, even though it appears as if the diagram is
frozen.
"""
function propagate_cocones!(S::Sketch,J::SketchModel,f::CSetTransformation,ch::Change)
  res = Change[]
  for (i,cc) in enumerate(S.cocones)
    legcond = any(l->!is_surjective(f[l]), unique(last.(cc.legs)))
    if legcond || !([cc.apex,vlabel(cc)...]⊆J.frozen[1] && ((last.(cc.legs) ∪ elabel(cc)) ⊆ J.frozen[2]))
      append!(res, propagate_cocone!(S, J, f, i, ch))
    end
  end
  res
end

"""
Rebuild the cocone equivalence classes (across different tables) from scratch.
This could be made more incremental using the change + the old cocone data
"""
function update_cocones!(S::Sketch,J::SketchModel,f::ACSetTransformation,ch::Change)
  new_cocones = map(zip(S.cocones, J.cocones)) do (c, (_,_))

    # create new aggregation of all tables in the cocone diagram
    cdict = Tuple{Symbol, Int, Int}[]
    for (vi,v) in enumerate(vlabel(c.d))
      for p in parts(J.model, v) push!(cdict, (v, vi, p)) end
    end

    cdict_inv = Dict([v=>i for (i,v) in enumerate(cdict)])
    new_eq = IntDisjointSets(length(cdict))

    # Merge elements based on leg into apex being the same
    ldict = [l=>[ti for (ti, l_) in c.legs if l_==l] for l in unique(last.(c.legs))]
    for (l,ltabs) in filter(x->length(x[2])>1, ldict)
      ref_inds = findall(x->x[2]==first(ltabs), cdict)
      for ltab in ltabs[2:end]
        for (i,j) in zip(ref_inds, findall(x->x[2]==ltab, cdict))
          union!(new_eq, i, j)
        end
      end
    end

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
        for (i,(sT_,_,s_)) in enumerate(cdict)
          if (sT_,s_) == (sT,s)
            for (j,(tT_,_,t_)) in enumerate(cdict)
              if (tT_,t_) == (tT,t)
                union!(new_eq, i, j)
              end
            end
          end
        end
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
  if verbose println("updating cocone $ci with frozen $(J.frozen) apex $(cc.apex) po data $(J.cocones) and ")
  show(stdout,"text/plain",crel_to_cset(S,J.model)[1])
  end
  # We care about, ∀ apexes, which connected components map to it
  ap_to_cc = DefaultDict(()->Set{Int}()) # ap₁ -> [cc₁,cc₂,...]
  # We care about, ∀ connected components, which apexes are mapped to
  cc_to_ap = DefaultDict(()->Set{Int}()) # cc₁ -> [ap₁, ap₂,...]
  for (ccdata_i, (t,ti,v)) in enumerate(cd)
    for (_,l) in filter(x->x[1]==ti, cc.legs)
      l_src, l_tgt = add_srctgt(l)
      for ap in J.model[incident(J.model, v, l_src), l_tgt]
        ccmp = find_root!(ccdata, ccdata_i)
        push!(ap_to_cc[ap], ccmp)
        push!(cc_to_ap[ccmp], ap)
      end
    end
  end
  frozen_diag = vlabel(cc) ⊆ J.frozen[1] && elabel(cc) ⊆ J.frozen[2]
  if verbose println("cc_to_ap $cc_to_ap\nap_to_cc $ap_to_cc") end
  # 1.) check for apex elements that should be merged
  for vs in collect.(filter(x->length(x)>1, collect(values(cc_to_ap))))
    if cc.apex ∈ J.frozen[1] throw(ModelException()) end
    if verbose println("MERGING COCONE APEX ELEMS $vs") end
    push!(res, Merge(S,J,Dict(cc.apex=>[vs])))
  end
  # 2a) if diagram completely determined, we have one apex elem per connected comp
  if frozen_diag && cc.apex ∉ J.frozen[1]
    for cc_root in unique(find_root!(ccdata, i) for i in 1:length(ccdata))
      if !haskey(cc_to_ap, cc_root)
        if cc.apex ∈ J.frozen[1] throw(ModelException()) end
        if verbose println("New cc_root that is unmatched $cc_root") end
        newL, newI = S.crel(), S.crel()
        ipartdict = Dict()
        ILd, IRd = [DefaultDict{Symbol,Vector{Int}}(()->Int[]) for _ in 1:2]
        add_part!(newL, cc.apex)
        ccinds = [i for i in 1:length(ccdata) if find_root!(ccdata, i)==cc_root]
        for (cctab, cctabi, ccind) in cd[ccinds]
          if ccind ∉ collect(IRd[cctab]) # don't repeat when same table appears in diagram multiple times
            for (_,l) in filter(x->x[1]==cctabi, cc.legs)
              lsrctgt = add_srctgt(l)
              if haskey(ipartdict, cctab=>ccind)
                (ipart,lpart) = ipartdict[cctab=>ccind]
              else
                ipart = add_part!(newI, cctab)
                lpart = add_part!(newL, cctab)
                ipartdict[cctab=>ccind] = ipart => lpart
                push!(ILd[cctab], lpart)
                push!(IRd[cctab], ccind);
              end
              add_part!(newL, l; Dict(zip(lsrctgt, [lpart, 1]))...)
            end
          end
        end
        IL = ACSetTransformation(newI,newL; ILd...)
        IR = ACSetTransformation(newI,J.model; IRd...)
        ad = Addition(S,J,IL,IR)
        push!(res, ad)
      else
        # set all legs if not yet determined
        for (cctab, cctabi, ccind) in cd[[i for i in 1:length(ccdata) if find_root!(ccdata, i) == cc_root]]
          for l in filter(l->src(S,l)==cctab,unique(last.(legs(cc))))
            lsrc,ltgt = add_srctgt(l)
            if isempty(incident(J.model, ccind, lsrc))
              error("""We're expecting the legs to be filled already...
                    we can fill this in if that's not the case though""")
            end
          end
        end
      end
    end
  end
  # cardinality checks if the apex # is known
  if cc.apex ∈ J.frozen[1]
    startJ = project(S,merge_eq(S,J.model,J.eqs), cc)
    mn, mx = [minmax_groups(S,startJ, cc, ccdata, cd; is_min=x) for x in [true,false]]
    if verbose println("mn $mn -- parts $(nparts(J.model, cc.apex)) -- mx $mx\n")
    show(stdout, "text/plain", J.model)
    end
    if !(mn <= nparts(J.model, cc.apex) <= mx)
      throw(ModelException())
    end
  end

  # 2.) check for connected components that cannot possibly be merged
  startJ = project(S,merge_eq(S,J.model,J.eqs), cc)
  if verbose
    println("check for connected components that cannot possibly be merged")
    println("values(ap_to_cc) $(collect(values(ap_to_cc)))")
  end
  for vs in collect.(filter(x->length(x)>1, collect(values(ap_to_cc))))
    # conservative approach - don't try anything if tables not frozen
    # TODO revisit this assumption, maybe something can still be inferred?
    if vlabel(cc) ⊆ J.frozen[1]
      if !connection_possible(S, startJ, cc, ccdata, cd, vs)
        throw(ModelException())
      end
    end
  end
  res
end

"""
The minimum # of connected components in a colimit diagram (or maximum)
This is a simple branching search problem except we'd like to be able to reason
even about tables that are not yet frozen.

If the diagram is a DAG with loops, we can say that, if there exists an unfrozen
table joining two other tables, that it's possible for all the elements to be
collapsed into one group (in case we are trying to minimize groups) and, if
there exists an unfrozen table that is terminal, that there could exist MAXINT
groups.
"""
function minmax_groups(S::Sketch,J_orig::StructACSet,cc::Cone,
                    conn_orig::IntDisjointSets{Int},
                    cd::Vector{Tuple{Symbol,Int,Int}}; is_min::Bool=true)
  verbose = false
  connd = Dict(v=>k for (k,v) in enumerate(cd))
  queue = [J_orig=>conn_orig]
  min_g = length(conn_orig) # highest it could be
  minmax = is_min ? min : max
  if is_min
    # for each unfrozen table, add all possible maps out
  else
    # if any terminal unfrozen tables, immediately return MAXINT
  end
  if verbose
    println("$(is_min ? "min" : "max") # of connected components in $cd ?");
    show(stdout,"text/plain",J_orig)
  end
  while !isempty(queue)
    J, conn = pop!(queue)
    min_g = minmax(min_g, num_groups(conn))
    d = sort(filter(x->!isempty(x[2]),
      [e=>setdiff(parts(J,src(S,e)), J[add_src(e)]) for e in elabel(cc)]),
      by=x->length(x[2]))
    if !isempty(d) # work still remaining to be done on this branch
      e, unassgn = first(d)
      error("TODO e $e unassgn $unassgn")
    end
  end
  return min_g
end

"""
Check if there exists a foreign key assignment that connects n sets of elements
in a C-Set.
"""
function connection_possible(S::Sketch,J_orig::StructACSet,
                             cocone::Cone,
                             conn_orig::IntDisjointSets{Int},
                             conndict::Vector{Tuple{Symbol,Int,Int}},
                             comps::Vector{Int})
  verbose = false
  if verbose println("are $comps mergable ?") end
  connd = Dict([v=>i for (i,v) in enumerate(conndict)])
  is_tot(J,e) = length(unique(J[add_src(e)])) == nparts(J, src(S,e))
  queue = [J_orig=>conn_orig]
  while !isempty(queue)
    J, conn = pop!(queue)
    if verbose println("popping $conn (in queue: $(length(queue)))") end
    es = [e for e in unique(elabel(cocone.d)) if !is_tot(J,e)]
    if isempty(es) continue end # this branch cannot branch further
    e = first(es) # or some more intelligent way to pick one?
    for e_i in incident(cocone.d, e, :elabel)
      s_i, t_i = src(cocone.d, e_i), tgt(cocone.d, e_i)
      (se, te), sT, tT = add_srctgt(e), src(S,e), tgt(S,e)
      if verbose println("\tbranch on $e:$sT->$tT") end
      undefd = first(collect(setdiff(parts(J, sT), J[se])))
      u_ind = connd[(sT,s_i,undefd)]
      u_cc = find_root!(conn, u_ind)
      if verbose println("\tlooking for fk targets for $sT#$undefd") end
      for p in parts(J,tT) # TODO we actually only need to consider distinct orbits
        if verbose println("\tconsidering ->$tT#$p") end
        p_ind = connd[(tT,t_i,p)]
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
  end
  return false # no more branching options, comps still unconnected
end

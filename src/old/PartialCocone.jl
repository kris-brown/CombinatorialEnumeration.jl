function compute_cocone!(S::Sketch, J::StructACSet, co_cone::Cone,
    m::Modify, eqc::EqClass)::Union{Nothing, Set{Int}}
verbose=false
nu, up = m.newstuff, m.update
diag_objs = co_cone.d[:vlabel]
diag_homs = ne(co_cone.d)== 0 ? Tuple{Symbol,Int,Int}[] :
collect(zip([co_cone.d[x] for x in [:elabel, :src,:tgt]]...))

# Get unquotiented apex: all distinct elements for each table involved
apex_obs = vcat([[(i, v) for v in eq_reps(eqc[obj])]
for (i, obj) in enumerate(diag_objs)]...)
if verbose println("apex_obs $apex_obs") end
# Get the apex objs index from the (tab_ind, elem_ind) value itself
apex_ob_dict = Dict([(j,i) for (i,j) in enumerate(apex_obs)])
# Equivalence class of `apex_obs`
eq_known = IntDisjointSets(length(apex_obs)) # known connections
eq_poss = IntDisjointSets(length(apex_obs)) # possible connections

# Use C-set map data to quotient this
if verbose println("diag homs $diag_homs") end
for (e, i, j) in diag_homs
esrc, etgt = add_srctgt(e)
stab, ttab = src(S, e), tgt(S,e)
(stab == diag_objs[i]) && (ttab == diag_objs[j]) || error("problem")
for (x_src, x_tgt) in zip([J[x] for x in [esrc, etgt]]...)
is, it = find_root!(eqc[stab], x_src), find_root!(eqc[ttab], x_tgt)
s, t = [apex_ob_dict[v] for v in [(i, is), (j, it)]]
union!(eq_known, s, t); union!(eq_poss, s, t)
end
for src_ind in parts(J, stab)
if isempty(incident(J, src_ind, esrc)) # it could map to anything!

tgt_inds = Int[apex_ob_dict[(j, tgt_ind)] for tgt_ind in parts(J, ttab)]
unions!(eq_poss, vcat(Int[apex_ob_dict[(i,src_ind)]], tgt_inds))
end
end
end

# Reorganize equivalence class data into a set of sets.
eqsets = eq_sets(eq_known; remove_singles=false)

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
for es in Iterators.product(eqsets, eqsets)
eqset1, eqset2 = es
tgts1, tgts2 = [apex_tgt_dict[e] for e in es]
conflict = intersect(tgts1, tgts2)
if !isempty(conflict)
# check if eqset1 and eqset2 could be possibly connected
poss_conn = false
for (t1, t2) in Iterators.product(eqset1, eqset2)
poss_conn |= in_same_set(eq_poss, t1, t2)
end
if !poss_conn
evals1, evals2 = [[apex_obs[i] for i in e] for e in es]
println("FAILING b/c $evals1 and $evals2 both map to $conflict ")
show(stdout, "text/plain",  J)
return nothing
end
end
end

seen_apex_tgts = union(values(apex_tgt_dict)...)
return Set(collect(setdiff(parts(J, co_cone.apex), seen_apex_tgts)))
end
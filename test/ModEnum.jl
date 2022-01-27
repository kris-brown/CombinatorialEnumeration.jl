include(joinpath(@__DIR__, "../src/ModEnum.jl"))
include(joinpath(@__DIR__, "../data/sketches/vec.jl"))
include(joinpath(@__DIR__, "../data/sketches/reflgraph.jl"))


# Chase step db
db = init_db(reset=true)


S = vec_sketch;
res = chase_below(db, S, 3; extra=0)
ms = get_models(db, S, 3)
lists = to_list.(ms)


if false
    S = rgraph_sketch
arr_ = S.cset()
add_parts!(arr_, :V, 2)
add_parts!(arr_, :E, 1)
set_subpart!(arr_, :src, [1])
set_subpart!(arr_, :tgt, [2])
arr = create_premodel(S, arr_)
add_premodel(db, S, arr)
chase_step_db(db, 1)
chase_step_db(db, 3)

res = chase_below(db, S, 3)

# Vectors
S = vec_sketch;
J = create_premodel(S, l321)
cone_ = S.cones[1]
eq = init_eq(S,l321)

# Cones
#######
@test isempty(compute_cones!(S, l321, eq))

missing_one = deepcopy(J)
rem_part!(missing_one, one, 1)
cmod = compute_cones!(S, missing_one, eq)
has_one = update_crel(missing_one, cmod)
@test nparts(has_one, one) == 1

# Cocones
#########
@test isempty(compute_cocones!(S, J, eq))

missing_N_ = deepcopy(l321)
rem_parts!(missing_N_, :ℕ, 1:4)
missing_N = create_premodel(S, missing_N_)
ccmod = compute_cocones!(S, missing_N, eq)
has_N = crel_to_cset(S,update_crel(missing_N, ccmod))[1]
@test nparts(has_one, :ℕ) == 4
@test sort(vcat(has_N[:succ], has_N[:zero])) == [1,2,3,4]

# Chase step
@test chase_step(S, J) == (J => Modify[])

# Branching on a cocone
extraN = apex(terminal(S.cset))
eN = create_premodel(S, extraN)
add_part!(extraN, :ℕ)
add_part!(extraN, :Succ)
@test compute_cocone!(eN, S.cocones[1], Modify(), init_eq(S, eN)) == Set([2])
get_possibilities(S, eN, Dict([:ℕ => Set([2])]))


end
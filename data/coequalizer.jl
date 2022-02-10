include(joinpath(@__DIR__, "equalizer.jl"))
include(joinpath(@__DIR__, "../../src/Models.jl"))
include(joinpath(@__DIR__, "../../src/ModEnum.jl"))

pushout_sketch = dual(eqsketch, :Coequalizer, [Symbol("f×ᵦg")=>Symbol("f+ᵦg")])

db = init_db(reset=true)

S = pushout_sketch;
Jinit = create_premodel(S, [:A=>2, :B=>2])
chase_set(db, S, StructACSet[Jinit], 4)
ms = get_models(db, S, 4)
include(joinpath(@__DIR__, "../src/DB.jl"))
include(joinpath(@__DIR__, "FLS.jl"))

db = init_db(reset=true)
@test add_fls(db, fls) == 1
@test get_fls(db, 1) == fls

@test add_fls(db, fls) == 1 # does not insert again


@test add_premodel(db, fls, xrel) == 1
@test get_premodel(db, 1) == (fls => xrel)
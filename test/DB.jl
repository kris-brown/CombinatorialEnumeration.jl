include(joinpath(@__DIR__, "../src/DB.jl"))
include(joinpath(@__DIR__, "Sketch.jl"))

db = init_db(reset=true)
@test add_sketch(db, fg) == 1
@test get_sketch(db, 1) == fg

@test add_sketch(db, fg) == 1 # does not insert again


@test add_premodel(db, fg, xrel) == 1
@test get_premodel(db, 1) == (fg => xrel)
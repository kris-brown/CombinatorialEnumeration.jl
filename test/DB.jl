module TestDB

# using Revise
using Test
using ModelEnumeration
using Catlab.CategoricalAlgebra

include(joinpath(@__DIR__, "TestSketch.jl"));

J = create_premodel(S);
es = EnumState()

@test add_premodel(es, S, J) == 1
@test get_premodel(es, S, 1) == J
@test add_premodel(es, S, J) == 1 # does not insert again


# To do: reimplement postgres backend & test db.
# @test add_sketch(db, S) == 1
# @test get_sketch(db, 1) == S
# @test add_sketch(db, S) == 1 # does not insert again

end # module

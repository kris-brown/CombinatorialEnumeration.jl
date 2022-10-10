module TestDB

using Test
using CombinatorialEnumeration
using Catlab.CategoricalAlgebra

include(joinpath(@__DIR__, "../TestSketch.jl"));

J = create_premodel(S);
es = EnumState()

@test add_premodel(es, S, J) == 1
@test es[1] == J
@test add_premodel(es, S, J) == 1 # does not insert again

# TODO test other stuff

end # module

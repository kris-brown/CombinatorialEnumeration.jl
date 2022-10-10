module TestSketches

using Test
using CombinatorialEnumeration
using Catlab.CategoricalAlgebra

include(joinpath(@__DIR__, "../TestSketch.jl"));

@test elabel(S.cones[1]) == [:f,:g]
@test src(S, :f) == :A
@test tgt(S, :f) == :B
@test hom_set(S, :A,:B) == [:f,:g]
@test hom_set(S, [:I,:Z],[:A]) == [:a,:z]
@test hom_in(S,:A) == [:e,:z,:a]
@test isempty(hom_set(S,:A,:A))
@test dual(dual(S)) == S
@test S.zero_obs == Set([:Z])
@test sketch_from_json(to_json(S)) == S
@test sizes(S,S.crel|>terminal|>apex) == "A: 1, B: 1, C: 1, E: 1, Z: 1, I: 1"

end # module

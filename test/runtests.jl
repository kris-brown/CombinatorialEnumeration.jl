using Test

@testset "Examples" begin
  include(joinpath(@__DIR__, "../data/petri.jl"));
  @test Petri.runtests()
  include(joinpath(@__DIR__, "../data/left_inverse_involution.jl"));
  @test LeftInvInvolution.runtests()
end


@testset "Sketches" begin
  include("Sketches.jl")
end

@testset "Models" begin
  include("Models.jl")
end

@testset "DB" begin
  include("DB.jl")
end

@testset "Propagate" begin
  include("Propagate.jl")
end


@testset "ModEnum" begin
  include("ModEnum.jl")
end




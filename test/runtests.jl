using Test


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

@testset "Examples" begin
  include(joinpath(@__DIR__, "../data/petri.jl"));
  @test Petri.runtests()
  include(joinpath(@__DIR__, "../data/left_inverse_involution.jl"));
  @test LeftInvInvolution.runtests()
  include(joinpath(@__DIR__, "../data/equalizer.jl"));
  @test Equalizer.runtests()
  include(joinpath(@__DIR__, "../data/coequalizer.jl"));
  @test Coequalizer.runtests()
  include(joinpath(@__DIR__, "../data/coproduct.jl"));
  @test Coproduct.runtests()
end

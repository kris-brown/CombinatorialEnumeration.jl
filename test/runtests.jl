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

for ex in filter(f->f[end-2:end]==".jl",readdir("data"))
  @testset "$ex" begin
    println("$ex")
    include(joinpath(@__DIR__, "../data/$ex")).runtests()
  end
end
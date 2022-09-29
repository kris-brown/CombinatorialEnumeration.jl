using Test
using CombinatorialEnumeration

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

@testset "SketchColimits" begin
  include("SketchColimits.jl")
end

# to start the tests at a later one, change the "a" to another letter
for ex in filter(f->f[end-2:end]==".jl" && f > "a",
                 readdir("$(pkgdir(CombinatorialEnumeration))/data"))
  @testset "$ex" begin
    println("$ex")
    include(joinpath(@__DIR__, "$(pkgdir(CombinatorialEnumeration))/data/$ex")).runtests()
  end
end
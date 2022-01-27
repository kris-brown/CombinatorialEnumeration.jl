using Test

@testset "ME" begin
    include("ModelEnumeration.jl")
end

@testset "DB" begin
    include("DB.jl")
end

@testset "Sketch" begin
    include("Sketch.jl")
end



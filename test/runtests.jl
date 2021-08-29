using Test

@testset "ME" begin
    include("ModelEnumeration.jl")
end

@testset "DB" begin
    include("DB.jl")
end

@testset "FLS" begin
    include("FLS.jl")
end



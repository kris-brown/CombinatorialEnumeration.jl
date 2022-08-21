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





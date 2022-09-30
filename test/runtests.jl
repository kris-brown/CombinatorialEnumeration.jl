using Test
using CombinatorialEnumeration


@testset "Product" begin
  include("examples/Product.jl")
end
@testset "Coproduct" begin
  include("examples/Coproduct.jl")
end
@testset "Equalizer" begin
  include("examples/Equalizer.jl")
end
@testset "Coequalizer" begin
  include("examples/Coequalizer.jl")
end
@testset "Pullback" begin
  include("examples/Pullback.jl")
end
@testset "Pushout" begin
  include("examples/Pushout.jl")
end
@testset "Triple" begin
  include("examples/Triple.jl")
end

@testset "Inj" begin
  include("examples/Inj.jl")
end
@testset "Surj" begin
  include("examples/Surj.jl")
end
@testset "JointSurj" begin
  include("examples/JointSurj.jl")
end

@testset "Const" begin
  include("examples/Const.jl")
end
@testset "Petri" begin
  include("examples/Petri.jl")
end
@testset "ReflGraph" begin
  include("examples/ReflGraph.jl")
end
@testset "Perm" begin
  include("examples/Perm.jl")
end
@testset "LeftInverse_Involution" begin
  include("examples/LeftInverse_Involution.jl")
end
@testset "GraphOverlap" begin
  include("examples/GraphOverlap.jl")
end

@testset "Semigroup" begin
  include("examples/Semigroup.jl")
end
@testset "Category" begin
  include("examples/Category.jl")
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

@testset "SketchColimits" begin
  include("SketchColimits.jl")
end



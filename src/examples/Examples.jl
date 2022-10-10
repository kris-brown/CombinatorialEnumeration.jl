module Examples
using Reexport

# Basic (co)limits
include(joinpath(@__DIR__, "Product.jl"))
include(joinpath(@__DIR__, "Coproduct.jl"))
include(joinpath(@__DIR__, "Equalizer.jl"))
include(joinpath(@__DIR__, "Coequalizer.jl"))
include(joinpath(@__DIR__, "Pullback.jl"))
include(joinpath(@__DIR__, "Pushout.jl"))
include(joinpath(@__DIR__, "Triple.jl"))

# Kinds of morphisms
include(joinpath(@__DIR__, "Inj.jl"))
include(joinpath(@__DIR__, "Surj.jl"))
include(joinpath(@__DIR__, "JointSurj.jl"))

# Combinatorial data structures
include(joinpath(@__DIR__, "Const.jl"))
include(joinpath(@__DIR__, "Petri.jl"))
include(joinpath(@__DIR__, "ReflGraph.jl"))
include(joinpath(@__DIR__, "UndirectedGraph.jl"))
include(joinpath(@__DIR__, "SimpleUndirectedGraph.jl"))
include(joinpath(@__DIR__, "Perm.jl"))
include(joinpath(@__DIR__, "LeftInverse_Involution.jl"))
include(joinpath(@__DIR__, "GraphOverlap.jl"))

# Algebraic data structures
include(joinpath(@__DIR__, "Semigroup.jl"))
include(joinpath(@__DIR__, "Category.jl"))


@reexport using .ProductSketch
@reexport using .CoproductSketch
@reexport using .EqualizerSketch
@reexport using .CoequalizerSketch
@reexport using .PullbackSketch
@reexport using .PushoutSketch
@reexport using .TripleSketch

@reexport using .InjSketch
@reexport using .SurjSketch
@reexport using .JointSurjSketch

@reexport using .ConstSketch
@reexport using .PetriSketch
@reexport using .ReflGraphSketch
@reexport using .UndirectedGraphSketch
@reexport using .SimpleUndirectedGraphSketch
@reexport using .PermSketch
@reexport using .LeftInverse_InvolutionSketch
@reexport using .GraphOverlapSketch

@reexport using .SemigroupSketch
@reexport using .CategorySketch

end
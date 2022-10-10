module Core 

using Reexport

"""
Data structures for representing / manipulating sketches 

Dependencies:  LGraphs → SketchCSets → Sketches → SketchCat → SketchColimits  
"""


include("LGraphs.jl")
include("SketchCSets.jl")
include("Sketches.jl")
include("SketchCat.jl")
include("SketchColimits.jl")

@reexport using .LGraphs
@reexport using .SketchCSets
@reexport using .Sketches
@reexport using .SketchCat
@reexport using .SketchColimits

end # module 

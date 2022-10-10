module CombinatorialEnumeration
using Reexport

"""
Dependencies: 

      Core 
     ↙    ↘ 
  Enum   Examples
"""

include(joinpath(@__DIR__, "core/Core.jl"))
include(joinpath(@__DIR__, "enum/Enum.jl"))
include(joinpath(@__DIR__, "examples/Examples.jl"))


@reexport using .Core
@reexport using .Enum
@reexport using .Examples

end # module

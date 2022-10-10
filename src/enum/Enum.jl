module Enum 
using Reexport

"""
Model enumeration code 

Dependencies:    Models 
                ↙      ↘
          Propagate     DB 
                ↘      ↙
                 ModEnum
"""

include(joinpath(@__DIR__, "Models.jl"))
include(joinpath(@__DIR__, "DB.jl"))
include(joinpath(@__DIR__, "propagate/Propagate.jl"))
include(joinpath(@__DIR__, "ModEnum.jl"))

@reexport using .Models
@reexport using .DB
@reexport using .Propagate
@reexport using .ModEnum

end # module 

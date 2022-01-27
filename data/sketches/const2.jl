include(joinpath(@__DIR__, "../../src/Sketch.jl"))

"""
CONSTANTS

Models are two constants from a set. A constant is an arrow from 1, the set with one element.
"""

s1 = Symbol("1")

const2schema = @acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [s1, :A]
    elabel = [:f, :g]
    src = [1,1]
    tgt = [2,2]
end

const2 = Sketch(:const2, const2schema, [Cone(c2d, s1,[])], [])

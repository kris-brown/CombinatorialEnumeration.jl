include(joinpath(@__DIR__, "../../src/Sketch.jl"))

"""
Cartesian Product
"""

pairschema = @acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [:s, :s2]
    elabel = [:p1, :p2]
    src = [2,2]
    tgt = [1,1]
end

paird= @acset LabeledGraph begin
    V = 2
    vlabel = [:s, :s]
end

pairs = Sketch(:pairs, pairschema, [
    Cone(lconed, :s2, [1=>:p1,2=>:p2])], [])

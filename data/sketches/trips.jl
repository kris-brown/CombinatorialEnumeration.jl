include(joinpath(@__DIR__, "../../src/Sketch.jl"))

"""
3-ary Cartesian product
"""

tripschema = @acset LabeledGraph begin
    V = 2
    E = 3
    vlabel = [:s, :s3]
    elabel = [:p1, :p2, :p3]
    src = [2,2,2]
    tgt = [1,1,1]
end

tripd = @acset LabeledGraph begin
    V = 4
    vlabel = [:s, :s, :s,]
end

trips = Sketch(:trips, tripschema, [
    Cone(lconed, :s2, [1=>:p1,2=>:p2, 3=>:p3])], [])

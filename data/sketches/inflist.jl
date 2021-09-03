include(joinpath(@__DIR__, "../../src/FLS.jl"))

"""
Infinite sequence of a's and b's
"""

inflistschema = @acset LabeledGraph begin
    V = 3
    E = 4
    vlabel = [s1, :d, :l]
    elabel = [:a,:b,:head,:tail]
    src = [1,1,3,3]
    tgt = [2,2,2,3]
end

add_cone!(inflist, @acset LabeledGraph begin
    V = 1
    vlabel = [s1]
end)

lconed =  @acset LabeledGraph begin
    V = 2
    vlabel = [:d, :l]
end

inflist = FLS(:inflist, inflistschema, [
    Cone(c2d, s1,[]),
    Cone(lconed, :l, [1=>:head,2=>:tail])], [])

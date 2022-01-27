include(joinpath(@__DIR__, "../../src/Sketch.jl"))

"""
Permutations of a set, i.e. invertible endo-functions.
"""
permschema = @acset LabeledGraph begin
    V = 1
    E = 2
    vlabel = [:X]
    elabel = [:f, :f⁻¹]
    src = [1,1]
    tgt = [1,1]
end

perm = Sketch(:perm, permschema, [], [(:inv, [:f, :f⁻¹], [])])

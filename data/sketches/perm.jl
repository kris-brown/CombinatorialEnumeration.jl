include(joinpath(@__DIR__, "../../src/FLS.jl"))

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

perm = FLS(:perm, permschema, [], [(:inv, [:f, :f⁻¹], [])])

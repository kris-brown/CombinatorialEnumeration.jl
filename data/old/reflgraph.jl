include(joinpath(@__DIR__, "../../src/Sketch.jl"))

####################
# REFLEXIVE GRAPHS #
####################

reflgraphschema = @acset LabeledGraph begin
    V = 2
    E = 3
    vlabel = [:V, :E]
    elabel = [:refl, :src, :tgt]
    src    = [1,     2,    2]
    tgt    = [2,     1,    1]
end


rgraph_sketch = Sketch(:reflgraph, reflgraphschema, Cone[], Cone[], [
    (:srcid, [:refl, :src], []),
    (:tgtid, [:refl, :tgt], [])])

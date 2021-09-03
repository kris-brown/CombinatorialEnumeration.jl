include(joinpath(@__DIR__, "../../src/FLS.jl"))

####################
# REFLEXIVE GRAPHS #
####################

reflgraphschema = @acset LabeledGraph begin
    V = 2
    E = 4
    vlabel = [:V, :E]
    elabel = [:id, :refl, :src, :tgt]
    src = [1,1,2,2]
    tgt = [1,2,1,1]
end


reflgraph = FLS(:reflgraph, reflgraphschema, [], [
    (:srcid, [:refl, :src], []),
    (:tgtid, [:refl, :tgt], [])])

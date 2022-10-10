module TestUndirectedGraph

using Test
using Catlab.CategoricalAlgebra
using Catlab.Graphs: Graph
using CombinatorialEnumeration
using CombinatorialEnumeration.Examples.UndirectedGraphSketch: Δ
S = UndirectedGraph;

# There are four undirected graphs with 2 vertices and 2 edges.
I = @acset S.cset begin V=2;E=4 end
es = init_premodel(S,I, [:V,:E]);
chase_db(S,es)
expected = [@acset(Graph, begin V=2;E=4;src=[1,2,1,2];tgt=[2,1,2,1] end), # •=•
            @acset(Graph, begin V=2;E=4;src=[1,2,1,1];tgt=[2,1,1,1] end), # ↻•-•
            @acset(Graph, begin V=2;E=4;src=[1,1,1,1];tgt=[1,1,1,1] end), # ↻•↺ •
            @acset(Graph, begin V=2;E=4;src=[1,1,2,2];tgt=[1,1,2,2] end), # ↻• •↺
]
@test test_models(es, S, expected; f=Δ)

end # module

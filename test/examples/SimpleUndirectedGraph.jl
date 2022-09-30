module TestSimpleUndirectedGraph

using Test
using Catlab.CategoricalAlgebra
using Catlab.Graphs: Graph
using CombinatorialEnumeration
using CombinatorialEnumeration.Examples.SimpleUndirectedGraphSketch: Δ
S = SimpleUndirectedGraph;

# There is only one simple graph with two vertices and X edges, since all edges
# must be between the two vertices (no loops)
I = @acset S.cset begin V=2;E=2 end
es = init_premodel(S,I, [:V,:E]);
chase_db(S,es)
expected = @acset Graph begin V=2;E=2;src=[1,2];tgt=[2,1] end
@test test_models(es, S, [expected]; f=Δ)


# There is one simple graph with three vertices and two edges
I = @acset S.cset begin V=3;E=4 end
es = init_premodel(S,I, [:V,:E]);
chase_db(S,es)
expected = @acset Graph begin V=3;E=4; src=[1,2,2,3]; tgt=[2,1,3,2] end
@test test_models(es, S, [expected]; f=Δ)

# There are two simple graphs with four vertices and two edges
I = @acset S.cset begin V=4;E=4 end
es = init_premodel(S,I, [:V,:E]);
chase_db(S,es)
expected = [@acset(Graph, begin V=4;E=4; src=[1,2,2,3]; tgt=[2,1,3,2] end),
            @acset(Graph, begin V=4;E=4; src=[1,2,3,4]; tgt=[2,1,4,3] end)]

@test test_models(es, S, expected; f=Δ)

end # module

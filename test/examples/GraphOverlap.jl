module TestGraphOverlap

using Test
using Revise
using Catlab.CategoricalAlgebra, Catlab.Graphs
using CombinatorialEnumeration
using CombinatorialEnumeration.Examples.GraphOverlapSketch: init_graphs, parse_result, R, GraphOverlap

using Catlab.Graphics, Catlab.Programs, Catlab.WiringDiagrams

S = GraphOverlap

pg = path_graph(Graph,2)
I = init_graphs(pg,pg)
es = init_premodel(S,I, [:V₁, :V₂, :E₁,:E₂])
chase_db(S,es);


expected = [
  # arrows pointing opposite between same vertices
  @acset(R, begin V₁=2;V₂=2;E₁=1;E₂=1;s₁=1;t₁=2;s₂=1;t₂=2
  V₃=2;E₃=2;s₃=[1,2];t₃=[2,1]; fᵥ=[1,2];gᵥ=[2,1];fₑ=1;gₑ=2 end),
  # arrows pointing in parallel between same vertices
  @acset(R, begin V₁=2;V₂=2;E₁=1;E₂=1;s₁=1;t₁=2;s₂=1;t₂=2
  V₃=2;E₃=2;s₃=1;t₃=2; fᵥ=[1,2];gᵥ=[1,2];fₑ=1;gₑ=2 end),
  # no overlap
  @acset(R, begin V₁=2;V₂=2;E₁=1;E₂=1;s₁=1;t₁=2;s₂=1;t₂=2
  V₃=4;E₃=2;s₃=[1,3];t₃=[2,4]; fᵥ=[1,2];gᵥ=[3,4];fₑ=1;gₑ=2 end),
  # total overlap
  @acset(R, begin V₁=2;V₂=2;E₁=1;E₂=1;s₁=1;t₁=2;s₂=1;t₂=2
  V₃=2;E₃=1;s₃=1;t₃=2; fᵥ=[1,2];gᵥ=[1,2];fₑ=1;gₑ=1 end),
  # overlap a1 b1
  @acset(R, begin V₁=2;V₂=2;E₁=1;E₂=1;s₁=1;t₁=2;s₂=1;t₂=2
  V₃=3;E₃=2;s₃=1;t₃=[2,3]; fᵥ=[1,2];gᵥ=[1,3];fₑ=1;gₑ=2 end),
  # overlap a2 b1
  @acset(R, begin V₁=2;V₂=2;E₁=1;E₂=1;s₁=1;t₁=2;s₂=1;t₂=2
  V₃=3;E₃=2;s₃=[1,2];t₃=[2,3]; fᵥ=[1,2];gᵥ=[2,3];fₑ=1;gₑ=2 end),
  # overlap a1 b2
  @acset(R, begin V₁=2;V₂=2;E₁=1;E₂=1;s₁=1;t₁=2;s₂=1;t₂=2
  V₃=3;E₃=2;s₃=[1,2];t₃=[2,3]; fᵥ=[2,3];gᵥ=[1,2];fₑ=2;gₑ=1 end),
  # overlap a2 b2
  @acset(R, begin V₁=2;V₂=2;E₁=1;E₂=1;s₁=1;t₁=2;s₂=1;t₂=2
  V₃=3;E₃=2;s₃=[1,3];t₃=2; fᵥ=[1,2];gᵥ=[3,2];fₑ=1;gₑ=2 end),
];
@test test_models(es, S, expected; f=parse_result)

end # module

module UndirectedGraphSketch
export UndirectedGraph
using Catlab.CategoricalAlgebra, Catlab.Present
using Catlab.Graphs: Graph, SchGraph
using ...Core

"""
Undirected graph as a half-edge graph with no dangling edges possible.
"""

schema = @acset LGraph begin
  V=4; E=4; vlabel=[:E,:V,:Refl,:Z];
  elabel=[:v,:flip,:refl,:zero]
  src=[1,1,3,3]; tgt=[2,1,1,4]
end
# show_lg(schema)


# Refl picks out dangling edges
refl_eq = Cone(@acset(LGraph, begin
  V=1;E=1;vlabel=[:E];elabel=[:flip];src=1;tgt=1 end),
  :Refl, [1=>:refl])

# Z is a zero object
z = Cone(:Z)
eqs = [[[:flip,:flip],  [add_id(:E)]]]
UndirectedGraph = Sketch(schema, cones=[refl_eq], cocones=[z],
                               eqs=eqs)

v,flip,_,_ = Presentation(UndirectedGraph.cset).generators[:Hom]
Δ = DeltaMigration(FinFunctor(Dict(:V=>:V,:E=>:E), Dict(:src=>v,:tgt=>flip⋅v),
                   SchGraph,Presentation(UndirectedGraph.cset)),
                   UndirectedGraph.cset, Graph)

"""Interpret a graph as an undirected graph"""
function init_ug(g::Graph)
  nv, ne = nparts(g, :V), nparts(g, :E)
  return @acset UndirectedGraph.cset begin V=nv; E=2*ne; 
              flip=vcat([[2*i,2*i-1] for i in 1:ne]...)
              v=vcat([[src(g,e), tgt(g,e)] for e in 1:ne]...)
  end 
end

end # module

module SimpleUndirectedGraphSketch
export SimpleUndirectedGraph
using Catlab.CategoricalAlgebra, Catlab.Present
using Catlab.Graphs: Graph, SchGraph
using ...Core

"""
Simple, undirected graphs without loops.
"""

schema = @acset LGraph begin
  V=5; E=8; vlabel=[:E,:V,:VV,:Loop,:Z];
  elabel=[:src,:tgt,:u,:flip,:p1,:p2,:loop,:zero]
  src=[1,1,1,1,3,3,4,4]; tgt=[2,2,3,1,2,2,1,5]
end
# show_lg(schema)

# VV is the product of V and V
vv = Cone(@acset(LGraph, begin V=2;vlabel=[:V] end), :VV, [1=>:p1,2=>:p2])

# u is monic
u_monic = Cone(@acset(LGraph, begin
  V=3; E=2; vlabel=[:E,:E,:VV]; elabel=[:u,:u]; src=[1,2];tgt=3 end),
  :E,[1=>add_id(:E),2=>add_id(:E)])

# loop is the equalizer of src and tgt
loop_eq = Cone(@acset(LGraph, begin
  V=2;E=2;vlabel=[:E,:V];elabel=[:src,:tgt];src=1;tgt=2 end),
  :Loop, [1=>:loop])

# Z is a zero object
z = Cone(:Z)
eqs = [[[:u,:p1],       [:src]],
       [[:flip,:tgt],   [:src]],
       [[:u,:p2],       [:tgt]],
       [[:flip,:src],   [:tgt]],
       [[:flip,:flip],  [add_id(:E)]]]
SimpleUndirectedGraph = Sketch(schema, cones=[vv,u_monic,loop_eq], cocones=[z],
                               eqs=eqs)

Δ = DeltaMigration(FinFunctor(Dict(:V=>:V,:E=>:E), Dict(:src=>:src,:tgt=>:tgt),
                   SchGraph,Presentation(SimpleUndirectedGraph.cset)),
                   SimpleUndirectedGraph.cset, Graph)

"""Interpret a graph as a simple undirected graph without loops"""
function init_sg(g::Graph)
  nv = nparts(g, :V)
  p1, p2= zip(Iterators.product(1:nv,1:nv)...) |> collect
  vvdic = Dict((v1,v2)=>k for (k,(v1,v2)) in enumerate(zip(p1,p2)))
  sg = @acset SimpleUndirectedGraph.cset begin V=nv; VV=nv*nv; p1=p1; p2=p2 end 
  for (s, t) in zip(g[:src], g[:tgt])
    if s == t println("ignoring loop on $s") end
    ne = nparts(sg, :E)
    add_parts!(sg, :E, 2; u=[vvdic[(s,t)], vvdic[(t,s)]], src=[s,t], tgt=[t,s], flip=[ne+2,ne+1])
  end
  return sg
end

end # module

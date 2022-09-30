module ProductSketch
export Prod
using Catlab.CategoricalAlgebra
using ...Sketches

"""
Cartesian Product
"""

pairschema = @acset LabeledGraph begin
  V=2; E=2; vlabel=[:s, :s2]; elabel=[:p1, :p2]; src=2; tgt=1
end

Prod = Sketch(pairschema, cones=[Cone(@acset(LabeledGraph,
    begin V=2;vlabel = [:s, :s] end), :s2, [1=>:p1,2=>:p2])])

end # module

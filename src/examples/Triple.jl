module TripleSketch
export Triple

using Catlab.CategoricalAlgebra
using ...Sketches

"""
3-ary Cartesian product
"""

tripschema = @acset LabeledGraph begin
  V = 2; E = 3; vlabel = [:s, :s3]; elabel = [:p1, :p2, :p3]; src = 2; tgt = 1
end

td = @acset LabeledGraph begin V = 3; vlabel = [:s, :s, :s,] end

Triple = Sketch(tripschema, cones=[Cone(td, :s3, [1=>:p1,2=>:p2, 3=>:p3])])


end # module

module ConstSketch
export Const

using Catlab.CategoricalAlgebra
using ...Sketches

"""
CONSTANTS

Models are two constants from a set.
A constant is an arrow from 1, the set with one element.
"""

constschema = @acset LabeledGraph begin
  V = 2; E = 2; vlabel = [:I, :A]; elabel = [:f, :g]; src = 1; tgt = 2
end

Const = Sketch(constschema, cones=[Cone(:I)])

end # module

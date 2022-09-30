module CoproductSketch
export Coprod,CoprodAA

using Catlab.CategoricalAlgebra
using ...Sketches

"""
Coproduct of two sets
"""
schema = @acset LabeledGraph begin
  V=3; E=2; vlabel=[:A,:B,:A_B]; elabel=[:iA,:iB]; src=[1,2]; tgt=3
end
"""A_B is the coproduct A+B"""
a_b = Cone(@acset(LabeledGraph, begin V=2; vlabel=[:A,:B] end),
           :A_B, [1=>:iA,2=>:iB])

Coprod = Sketch(schema, cocones=[a_b])

"""
Coproduct of a set with itself
"""
schemaAA = @acset LabeledGraph begin
  V=2; E=2; vlabel=[:A,:A_A]; elabel=[:iA,:iB]; src=1; tgt=2
end

"""A_A is the coproduct A+B"""
a_a = Cone(@acset(LabeledGraph, begin V=2; vlabel=[:A,:A] end),
           :A_A, [1=>:iA,2=>:iB])

CoprodAA = Sketch(schemaAA, cocones=[a_a])


end # module

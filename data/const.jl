module Const

using Catlab.CategoricalAlgebra
using CombinatorialEnumeration
using Test
"""
CONSTANTS

Models are two constants from a set. A constant is an arrow from 1, the set with one element.
"""


constschema = @acset LabeledGraph begin
  V = 2; E = 2; vlabel = [:I, :A]; elabel = [:f, :g]; src = 1; tgt = 2
end

S = Sketch(:const, constschema, cones=[Cone(:I)])

function runtests()
  I = @acset S.cset begin A=3 end
  es = init_premodel(S,I, [:A])
  chase_db(S,es)
  expected = [
    # f and g are the same
    @acset(S.cset,begin A=3;I=1;f=1;g=1 end),
    # f and g are different
    @acset(S.cset,begin A=3;I=1;f=1;g=2 end),
  ]
  @test test_models(es, S, expected)
  return true
end

end # module

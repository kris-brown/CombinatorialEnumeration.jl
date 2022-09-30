module TestConst

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

S = Const

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

end # module

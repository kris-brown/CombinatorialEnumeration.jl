module TestCoproduct

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

S = CoprodAA

I = @acset S.cset begin A=3 end
es = init_premodel(S,I, [:A])
expected = @acset S.cset begin A=3;A_A=6; iA=[1,2,3];iB=[4,5,6] end
chase_db(S,es)
@test test_models(es, S, [expected])

I = @acset S.cset begin A=3; A_A=6 end
es = init_premodel(S,I, [:A,:A_A])
chase_db(S,es)
@test test_models(es, S, [expected])

end # module

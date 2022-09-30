module TestInj

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

S = Inj

I = @acset S.cset begin A=2;B=1 end # not possible to have surj
es = init_premodel(S,I,[:A,:B])
chase_db(S,es)
@test test_models(es, S, [])

I = @acset S.cset begin A=2; B=2 end
es = init_premodel(S,I,[:A,:B])
chase_db(S,es)
expected = @acset S.cset begin A=2;B=2; f=[1,2] end
@test test_models(es, S, [expected])

end # module
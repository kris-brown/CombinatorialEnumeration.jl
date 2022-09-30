module TestSurj

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

S = Surj

I = @acset S.cset begin A=1;B=2 end # not possible to have surj
es = init_premodel(S,I,[:A,:B])
chase_db(S,es)
@test test_models(es, S, [])

I = @acset S.cset begin A=3; B=2 end
es = init_premodel(S,I,[:A,:B])
chase_db(S,es)
expected = @acset S.cset begin A=3;B=2;C=5;
  d=[1,1,2];d0=[1,1,2,2,3];d1=[1,2,1,2,3] end
@test test_models(es, S, [expected])


end # module
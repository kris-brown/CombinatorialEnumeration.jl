module TestTriple

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

S = Triple

I = @acset S.cset begin s=2 end
es = init_premodel(S,I)
chase_db(S,es)
ex = @acset S.cset begin s=2; s3=8;
  p1=[1,2,1,2,1,2,1,2]; p2=[1,1,2,2,1,1,2,2]; p3=[1,1,1,1,2,2,2,2]
end
@test test_models(es, S, [ex])

end # module

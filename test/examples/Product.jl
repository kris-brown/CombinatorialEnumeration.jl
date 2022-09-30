module TestProduct

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

S = Prod

I = @acset S.cset begin s=2 end
es = init_premodel(S,I)
chase_db(S,es)
ex = @acset S.cset begin s=2; s2=4; p1=[1,2,1,2]; p2=[1,1,2,2] end
@test test_models(es, S, [ex])

I = @acset S.cset begin s=3 end
es = init_premodel(S,I)
chase_db(S,es)
mo = get_model(es,S,last(sort(collect(es.models))))
@test nparts(mo, :s2) == 9

end # module

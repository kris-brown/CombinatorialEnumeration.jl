module TestReflGraph

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

S = ReflGraph

I = @acset S.cset begin V=2; E=3 end
es = init_premodel(S,I, [:V,:E])
chase_db(S,es)

expected = [
    @acset(S.cset, begin V=2;E=3;refl=[1,2];src=[1,2,1];tgt=[1,2,1] end),
    @acset(S.cset, begin V=2;E=3;refl=[1,2];src=[1,2,1];tgt=[1,2,2] end),
]
@test test_models(es, S, expected)

I = @acset S.cset begin V=2; E=1 end
es = init_premodel(S,I, [:V,:E])
chase_db(S,es)
@test test_models(es, S, [])

end # module

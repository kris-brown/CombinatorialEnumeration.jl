module TestPerm

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

S = Perm

I = @acset S.cset begin X=3 end
es = init_premodel(S,I, [:X])
chase_db(S,es)

expected = [
    @acset(S.cset, begin X=3;f=[1,2,3];f⁻¹=[1,2,3] end),
    @acset(S.cset, begin X=3;f=[1,3,2];f⁻¹=[1,3,2] end),
    @acset(S.cset, begin X=3;f=[2,3,1];f⁻¹=[3,1,2] end),
]

@test test_models(es, S, expected)

end # module

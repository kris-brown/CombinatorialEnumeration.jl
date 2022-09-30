module TestSemigroup

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration
using CombinatorialEnumeration.Examples.SemigroupSketch: get_semis

S = Semigroup

I = @acset S.cset begin s=2 end;
es = init_premodel(S,I, [:s]);
chase_db(S,es)
@test test_models(es,S,get_semis(2))


end # module

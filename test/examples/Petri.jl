module TestPetri

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration
using CombinatorialEnumeration.Examples.PetriSketch: all_petri

S = Petri

I = @acset S.cset begin S=2;T=2;I=2;O=2 end;
es = init_premodel(S,I,[:S,:T,:I,:O]);
chase_db(S,es)
expected = all_petri(2);
@test test_models(es, S, expected)


end # module

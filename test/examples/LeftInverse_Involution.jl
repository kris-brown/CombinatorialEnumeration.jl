module TestLeftInverse_Involution

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

S = LeftInverse_Involution

I = @acset S.cset begin A=1;B=2 end
es = init_premodel(S,I,[:A,:B])
chase_db(S,es)
expected = [@acset(S.cset, begin A=1;B=2;f=1;g=1;inv=[1,2]end), # id inv
            @acset(S.cset, begin A=1;B=2;f=1;g=1;inv=[2,1]end)] # swap inv
@test test_models(es, S, expected)

I = @acset S.cset begin A=2;B=2 end
es = init_premodel(S,I,[:A,:B])
chase_db(S,es)
expected = [@acset(S.cset, begin A=2;B=2;f=[1,2];g=[1,2];inv=[1,2]end), # id
            @acset(S.cset, begin A=2;B=2;f=[1,2];g=[1,2];inv=[2,1]end)] # swap
@test test_models(es, S, expected)


I = @acset S.cset begin A=2;B=1 end
es = init_premodel(S,I,[:A,:B])
chase_db(S,es)
@test test_models(es, S, []) # no left inv possible for f


I = @acset S.cset begin A=2;B=3 end
es = init_premodel(S,I,[:A,:B])
chase_db(S,es)

# think of A as picking out a subset of B, f(A). let the excluded element be bₓ
expected = [
  # inv is id
  @acset(S.cset, begin A=2;B=3;f=[1,2];g=[1,2,1];inv=[1,2,3]end),
  # inv swaps f(A).
  @acset(S.cset, begin A=2;B=3;f=[1,2];g=[1,2,1];inv=[2,1,3]end),
  # inv swaps one element in f(A) with bₓ. g(bₓ) maps to the unswapped element.
  @acset(S.cset, begin A=2;B=3;f=[1,2];g=[1,2,1];inv=[1,3,2]end),
  # inv swaps one element in f(A) with bₓ. g(bₓ) maps to the swapped element.
  @acset(S.cset, begin A=2;B=3;f=[1,2];g=[1,2,2];inv=[1,3,2]end)
]
@test test_models(es, S, expected)

end # module

module LeftInvInvolution

using Test
using Revise
using Catlab.CategoricalAlgebra
using ModelEnumeration

"""
LEFT INVERSE / INVOLUTION

Models are pairs of involutions inv:B -> B
AND
monomorphisms f:A->B (with right inverse g: B->A)

This is just a simple illustrative example of sketches. TODO we will use it to
show how this sketch is the pushout of two smaller sketches and how we can
compute the models compositionally.
"""

##########
# Sketch #
##########

fgschema = @acset LabeledGraph begin
  V = 2
  E = 3
  vlabel = [:A,:B]
  elabel = [:f,:g, :inv]
  src    = [1,  2,  2]
  tgt    = [2,  1,  2]
end

S = Sketch(:FG, fgschema; eqs=[
  [[:f, :g],   Symbol[]],
  [[:inv,:inv],Symbol[]]])

#########
# Tests #
#########

function runtests()
  I = @acset S.cset begin A=1;B=2 end
  es = init_db(S,I,[:A,:B])
  chase_db(S,es)
  expected = [@acset(S.cset, begin A=1;B=2;f=1;g=1;inv=[1,2]end), # id inv
              @acset(S.cset, begin A=1;B=2;f=1;g=1;inv=[2,1]end)] # swap inv
  test_models(es, S, expected)

  I = @acset S.cset begin A=2;B=2 end
  es = init_db(S,I,[:A,:B])
  chase_db(S,es)
  expected = [@acset(S.cset, begin A=2;B=2;f=[1,2];g=[1,2];inv=[1,2]end), # id
              @acset(S.cset, begin A=2;B=2;f=[1,2];g=[1,2];inv=[2,1]end)] # swap
  test_models(es, S, expected)


  I = @acset S.cset begin A=2;B=1 end
  @test_throws(ModelException, init_db(S,I,[:A,:B])) # no left inv poss' for f

  I = @acset S.cset begin A=2;B=3 end
  es = init_db(S,I,[:A,:B])
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
  test_models(es, S, expected)
  return true
end

end # module

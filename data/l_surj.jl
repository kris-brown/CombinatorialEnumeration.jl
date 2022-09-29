module Surj

# using Revise
using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

"""
Encoding of a surjection as a pair cone and cocone as described in
Barr and Wells CTCS 10.4.6

  d₀  d
C ⇉ A ⟶ B
  d₁
"""
schema = @acset LabeledGraph begin
  V=3; E=3; vlabel=[:C,:A,:B]; elabel=[:d0,:d1,:d];
  src=[1,1,2]; tgt=[2,2,3]
end

"""c is a pullback: all pairs of a that agree on their value in d"""
c = Cone(@acset(LabeledGraph, begin V=3;E=2;vlabel=[:A,:A,:B];
          elabel=[:d,:d];src=[1,2]; tgt=3 end,), :C, [1=>:d0,2=>:d1])
"""b is the coequalizer of c's legs"""
cc = Cone(@acset(LabeledGraph, begin V=2;E=2;vlabel=[:C,:A];
          elabel=[:d0, :d1]; src=1; tgt=2 end), :B, [2=>:d])

S = Sketch(schema, cones=[c], cocones=[cc])

function runtests()
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

  return true
end

end # module

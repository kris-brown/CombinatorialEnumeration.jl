module JointSurj

# using Revise
using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

"""
Using the surjection encoding, this is a sketch for a pair of maps that are
*jointly surjective*.

         A
    π₁ ↙   ↘ f
PB ⇉ A+B ↠  C
    π₂   ↖ ↗ g
          B
"""
schema = @acset LabeledGraph begin
  V=5; E=7; vlabel=[:A,:B,:C,:A_B,:PB];
  elabel=[:f,:g,:iA,:iB,:p1,:p2,:c];
  src=[1,2,1,2,5,5,4]; tgt=[3,3,4,4,4,4,3]
end

"""PB is a pullback: all pairs of A+B that agree on their value in c"""
c = Cone(@acset(LabeledGraph, begin V=3;E=2;vlabel=[:A_B,:A_B,:C];
                elabel=[:c,:c];src=[1,2]; tgt=3 end,),
          :PB, [1=>:p1,2=>:p2])

"""(C,c) is the coequalizer of PB's legs"""
cc = Cone(@acset(LabeledGraph, begin V=3;E=2;vlabel=[:PB,:A_B,:A_B];
                  elabel=[:p1, :p2]; src=1; tgt=2 end),
          :C, [2=>:c, 3=>:c])
"""A_B is the coproduct A+B"""
a_b = Cone(@acset(LabeledGraph, begin V=2;vlabel=[:A,:B] end),
           :A_B, [1=>:iA,2=>:iB])

eqs = [[[:f],[:iA,:c]],[[:g],[:iB,:c]]]
S = Sketch(:JointSurj, schema, cones=[c], cocones=[cc,a_b,],eqs=eqs)

function runtests()
  I = @acset S.cset begin A=2;B=2;C=2 end
  es = init_premodel(S,I, [:A,:B,:C])
  chase_db(S,es)

  expected = [
    @acset(S.cset, begin
      A=2;B=2;C=2;A_B=4;iA=[1,2];iB=[3,4];c=[1,1,2,2];
      f=1;g=2;PB=8;p1=[1,1,2,2,3,3,4,4];p2=[1,2,1,2,3,4,3,4] end),
    @acset(S.cset, begin
      A=2;B=2;C=2;A_B=4;iA=[1,2];iB=[3,4];c=[1,2,1,2];
      f=[1,2];g=[1,2];PB=8;p1=[1,1,2,2,3,3,4,4];p2=[1,3,2,4,1,3,2,4] end),
    @acset(S.cset, begin
      A=2;B=2;C=2;A_B=4;iA=[1,2];iB=[3,4];c=[1,2,2,2];
      f=[1,2];g=2;PB=10;
      p1=[1,2,2,2,3,3,3,4,4,4];p2=[1,2,3,4,2,3,4,2,3,4] end),
    @acset(S.cset, begin
      A=2;B=2;C=2;A_B=4;iA=[1,2];iB=[3,4];c=[1,1,1,2];
      f=1;g=[1,2];PB=10;
      p1=[1,1,1,2,2,2,3,3,3,4];p2=[1,2,3,1,2,3,1,2,3,4] end),
  ]

  @test test_models(es, S, expected)

  # we can also, knowing what A and B are, freeze A+B.
  I = @acset S.cset begin A=2;B=2;C=2;A_B=4 end
  es = init_premodel(S,I, [:A,:B,:C,:A_B])
  chase_db(S,es)

  @test test_models(es, S, expected)
  return true
end

end # module

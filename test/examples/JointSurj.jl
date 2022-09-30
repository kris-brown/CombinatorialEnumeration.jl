module TestJointSurj

using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

S = JointSurj

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
end # module

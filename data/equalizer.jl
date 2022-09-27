module Equalizer

# using Revise
using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration


eqschema = @acset LabeledGraph begin
  V = 3; E = 3
  vlabel = [:A,:B,:E]; elabel = [:f,:g, :e]
  src = [1,1,3]; tgt = [2,2,1]
end

eqconed = @acset LabeledGraph begin
  V=3; E=2; vlabel=[:A,:A,:B]; elabel=[:f,:g]; src=[1,2]; tgt=[3,3]
end

S = Sketch(eqschema, cones=[Cone(eqconed, :E, [1=>:e,2=>:e])]);

function runtests()
  I = @acset S.cset begin A=2;B=2 end
  es = init_premodel(S,I, [:A,:B])
  chase_db(S,es)
  ms = [get_model(es,S,i) for i in es.models]

  expected =[
    # f,g both const and point to same element
    @acset(S.cset,begin A=2;B=2;E=2;f=1;g=1;e=[1,2] end),
    # f,g both const and point to different elements
    @acset(S.cset,begin A=2;B=2;f=1;g=2 end),
    # g const, f is not
    @acset(S.cset,begin A=2;B=2;E=1;f=[1,2];g=1;e=1 end),
    # f const, g is not
    @acset(S.cset,begin A=2;B=2;E=1;g=[1,2];f=1;e=1 end),
    # f and g are id
    @acset(S.cset,begin A=2;B=2;E=2;f=[1,2];g=[1,2];e=[1,2] end),
    # f and g are swapped
    @acset(S.cset,begin A=2;B=2;f=[1,2];g=[2,1] end),
  ]
  @test test_models(es, S, expected)
  return true
end

end # module

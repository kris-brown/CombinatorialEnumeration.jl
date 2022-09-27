module Coequalizer

# using Revise
using Test
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration

include(joinpath(@__DIR__, "equalizer.jl"))

S = dual(Equalizer.S, [:E=>:C, :e=>:c])

function runtests()

  I = @acset S.cset begin A=2;B=2 end
  es = init_premodel(S,I, [:A,:B])
  chase_db(S,es)

  expected =[
    # f,g both const and point to same element
    @acset(S.cset,begin A=2;B=2;C=2;f=1;g=1;c=[1,2] end),
    # f,g both const and point to different elements
    @acset(S.cset,begin A=2;B=2;C=1;f=1;g=2;c=1 end),
    # g const, f is not
    @acset(S.cset,begin A=2;B=2;C=1;f=[1,2];g=1;c=1 end),
    # f const, g is not
    @acset(S.cset,begin A=2;B=2;C=1;g=[1,2];f=1;c=1 end),
    # f and g are id
    @acset(S.cset,begin A=2;B=2;C=2;f=[1,2];g=[1,2];c=[1,2] end), #
    # f and g are swapped
    @acset(S.cset,begin A=2;B=2;C=1;f=[1,2];g=[2,1];c=1 end),
  ]
  @test test_models(es, S, expected)
  return true
end

end # module

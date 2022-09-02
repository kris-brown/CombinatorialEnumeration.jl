module Inj

# using Revise
using Test
using Catlab.CategoricalAlgebra
using ModelEnumeration

"""
Encoding of a injection as a limit cone with id legs
Barr and Wells CTCS 10.4.6

"""
schema = @acset LabeledGraph begin
  V=2; E=1; vlabel=[:A,:B]; elabel=[:f];  src=[1]; tgt=[2]
end

"""           id    f
            ----> A ↘
      Apex A          B
            ----> A ↗
              id    f

"""
c = Cone(@acset(LabeledGraph, begin V=3;E=2;vlabel=[:A,:A,:B];
          elabel=[:f,:f];src=[1,2]; tgt=3 end,), :A, [1=>:id_A,2=>:id_A])

S = Sketch(:Inj, schema, cones=[c])

function runtests()
  I = @acset S.cset begin A=2;B=1 end # not possible to have surj
  @test_throws(ModelException,init_db(S,I,[:A,:B]))

  I = @acset S.cset begin A=2; B=2 end
  es = init_db(S,I,[:A,:B])
  chase_db(S,es)
  expected = @acset S.cset begin A=2;B=2; f=[1,2] end
  @test is_isomorphic(get_model(es,S,only(es.models)), expected)
  return true
end

end # module
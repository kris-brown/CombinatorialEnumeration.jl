module Coproduct

using Catlab.CategoricalAlgebra
using ModelEnumeration

"""
Using the surjection encoding, this is a sketch for a pair of maps that are *jointly surjective*.
"""
schema = @acset LabeledGraph begin
  V=3; E=2; vlabel=[:A,:B,:A_B];
  elabel=[:iA,:iB];
  src=[1,2]; tgt=[3,3]
end


"""A_B is the coproduct A+B"""
a_b = Cone(@acset(LabeledGraph, begin V=2;vlabel=[:A,:B] end),
           :A_B, [1=>:iA,2=>:iB])

S = Sketch(:Coprod, schema, cocones=[a_b,])

function runtests()
  I = @acset S.cset begin A=2;B=2 end
  es = init_db(S,I, [:A,:B])
  chase_db(S,es)
  expected = @acset S.cset begin A=2;B=2;A_B=4; iA=[1,2];iB=[3,4] end
  is_isomorphic(get_model(es,S,only(es.models)), expected)
end

end # module

module Coproduct

using Catlab.CategoricalAlgebra
using ModelEnumeration

"""
Using the surjection encoding, this is a sketch for a pair of maps that are *jointly surjective*.
"""
schema = @acset LabeledGraph begin
  V=2; E=2; vlabel=[:A,:A_A];
  elabel=[:iA,:iB]; src=1; tgt=2
end


"""A_A is the coproduct A+B"""
a_a = Cone(@acset(LabeledGraph, begin V=2; vlabel=[:A,:A] end),
           :A_A, [1=>:iA,2=>:iB])

S = Sketch(:Coprod, schema, cocones=[a_a,])

function runtests()
  I = @acset S.cset begin A=3 end
  es = init_db(S,I, [:A])
  expected = @acset S.cset begin A=3;A_A=6; iA=[1,2,3];iB=[4,5,6] end
  is_isomorphic(get_model(es,S,only(es.models)), expected)

  I = @acset S.cset begin A=3; A_A=6 end
  es = init_db(S,I, [:A,:A_A])
  chase_db(S,es)
  is_isomorphic(get_model(es,S,only(es.models)), expected)
end

end # module

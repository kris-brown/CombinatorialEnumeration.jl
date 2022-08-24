module Surj

using Revise
using Catlab.CategoricalAlgebra
using ModelEnumeration

"""
Encoding of a surjection as a pair cone and cocone as described in
Barr and Wells CTCS 10.4.6
"""
schema = @acset LabeledGraph begin
  V=3; E=3; vlabel=[:c,:a,:b]; elabel=[:d0,:d1,:d];
  src=[1,1,2]; tgt=[2,2,3]
end

"""c is a pullback: all pairs of a that agree on their value in d"""
c = Cone(@acset(LabeledGraph, begin V=3;E=2;vlabel=[:a,:a,:b];
          elabel=[:d,:d];src=[1,2]; tgt=3 end,), :c, [1=>:d0,2=>:d1])
"""b is the coequalizer of c's legs"""
cc = Cone(@acset(LabeledGraph, begin V=2;E=2;vlabel=[:c,:a];
          elabel=[:d0, :d1]; src=1; tgt=2 end), :b, [2=>:d])

S = Sketch(:surj, schema, cones=[c], cocones=[cc])

function runtests()
  I = @acset S.cset begin a=3;b=2 end
  es = init_db(S,I,[:a,:b])
  chase_db(S,es)
  expected = @acset S.cset begin a=3;b=2;c=5;
    d=[1,1,2];d0=[1,1,2,2,3];d1=[1,2,1,2,3] end
  is_isomorphic(get_model(es,S,only(es.models)), expected)
end

end # module

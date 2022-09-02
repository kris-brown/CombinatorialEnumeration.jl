module Pairs

using Catlab.CategoricalAlgebra
using ModelEnumeration
using Test

"""
Cartesian Product
"""

pairschema = @acset LabeledGraph begin
  V=2; E=2; vlabel=[:s, :s2]; elabel=[:p1, :p2]; src=2; tgt=1
end

S = Sketch(:pairs, pairschema, cones=[Cone(@acset(LabeledGraph,
    begin V=2;vlabel = [:s, :s] end), :s2, [1=>:p1,2=>:p2])])

function runtests()
  I = @acset S.cset begin s=2 end
  es = init_db(S,I)
  ex = @acset S.cset begin s=2; s2=4; p1=[1,2,1,2]; p2=[1,1,2,2] end
  @test is_isomorphic(ex, get_model(es,S,1))
  I = @acset S.cset begin s=3 end
  es = init_db(S,I)
  @test nparts(es[1].model, :s2) == 9
  return true
end

end # module

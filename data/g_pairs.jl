module Pairs

using Catlab.CategoricalAlgebra
using CombinatorialEnumeration
using Test

"""
Cartesian Product
"""

pairschema = @acset LabeledGraph begin
  V=2; E=2; vlabel=[:s, :s2]; elabel=[:p1, :p2]; src=2; tgt=1
end

S = Sketch(pairschema, cones=[Cone(@acset(LabeledGraph,
    begin V=2;vlabel = [:s, :s] end), :s2, [1=>:p1,2=>:p2])])

function runtests()
  I = @acset S.cset begin s=2 end
  es = init_premodel(S,I)
  chase_db(S,es)
  ex = @acset S.cset begin s=2; s2=4; p1=[1,2,1,2]; p2=[1,1,2,2] end
  @test test_models(es, S, [ex])

  I = @acset S.cset begin s=3 end
  es = init_premodel(S,I)
  chase_db(S,es)
  mo = get_model(es,S,last(sort(collect(es.models))))
  @test nparts(mo, :s2) == 9

  return true
end

end # module

# using Revise
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

c = Cone(@acset(LabeledGraph, begin V=3;E=2;vlabel=[:a,:a,:b];
          elabel=[:d,:d];src=[1,2]; tgt=3 end,), :c, [1=>:d0,2=>:d1])

cc = Cone(@acset(LabeledGraph, begin V=2;E=2;vlabel=[:c,:a]; elabel=[:d0, :d1]; src=1; tgt=2 end), :b, [2=>:d])

surj = Sketch(:surj, schema, [c], [cc], [])


es = EnumState()
Jinit = create_premodel(surj, [:a=>1, :b=>1, :c=>1]);
chase_set(es, surj, Pair{StructACSet, Defined}[Jinit=>init_defined(surj, Jinit)], 3)

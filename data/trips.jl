module Trips

using Catlab.CategoricalAlgebra
using ModelEnumeration
using Test

"""
3-ary Cartesian product
"""

tripschema = @acset LabeledGraph begin
  V = 2; E = 3; vlabel = [:s, :s3]; elabel = [:p1, :p2, :p3]; src = 2; tgt = 1
end

td = @acset LabeledGraph begin V = 3; vlabel = [:s, :s, :s,] end

S = Sketch(:trips, tripschema, cones=[Cone(td, :s3, [1=>:p1,2=>:p2, 3=>:p3])])

function runtests()
  I = @acset S.cset begin s=2 end
  es = init_db(S,I)
  ex = @acset S.cset begin s=2; s3=8;
    p1=[1,2,1,2,1,2,1,2]; p2=[1,1,2,2,1,1,2,2]; p3=[1,1,1,1,2,2,2,2]
  end
  @test is_isomorphic(ex, get_model(es,S,1))
  return true
end

end # module
module Pairs

using Revise
using Catlab.CategoricalAlgebra
using ModelEnumeration
using CSetAutomorphisms

"""
Cartesian Product
"""

pairschema = @acset LabeledGraph begin
    V=2; E=2; vlabel=[:s, :s2];elabel=[:p1, :p2]; src=[2,2]; tgt=[1,1]
end


S = Sketch(:pairs, pairschema, cones=[Cone(@acset(LabeledGraph,
    begin V=2;vlabel = [:s, :s] end), :s2, [1=>:p1,2=>:p2])], [])

# function runtests()
I = @acset S.cset begin s=2 end
es = init_db(S,I)

# end
end # module

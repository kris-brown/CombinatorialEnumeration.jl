module PermSketch
export Perm

using Catlab.CategoricalAlgebra
using ...Core

"""
Permutations of a set, i.e. invertible endo-functions.
"""
permschema = @acset LGraph begin
    V = 1
    E = 2
    vlabel = [:X]
    elabel = [:f, :f⁻¹]
    src = [1,1]
    tgt = [1,1]
end

Perm = Sketch(permschema, eqs=[[[:f, :f⁻¹],[add_id(:X)]]])

end # module

module PermSketch
export Perm

using Catlab.CategoricalAlgebra
using ...Sketches

"""
Permutations of a set, i.e. invertible endo-functions.
"""
permschema = @acset LabeledGraph begin
    V = 1
    E = 2
    vlabel = [:X]
    elabel = [:f, :f⁻¹]
    src = [1,1]
    tgt = [1,1]
end

Perm = Sketch(permschema, eqs=[[[:f, :f⁻¹],Symbol[]]])

end # module

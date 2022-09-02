module JointSurj

# using Revise
using Catlab.CategoricalAlgebra
using ModelEnumeration
using Test

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

S = Sketch(:perm, permschema, eqs=[[[:f, :f⁻¹],Symbol[]]])

function runtests()
    I = @acset S.cset begin X=3 end
    es = init_db(S,I, [:X])
    chase_db(S,es)

    expected = [
        @acset(S.cset, begin X=3;f=[1,2,3];f⁻¹=[1,2,3] end),
        @acset(S.cset, begin X=3;f=[1,3,2];f⁻¹=[1,3,2] end),
        @acset(S.cset, begin X=3;f=[2,3,1];f⁻¹=[3,1,2] end),
    ]

    @test test_models(es, S, expected)

    return true
end

end # module

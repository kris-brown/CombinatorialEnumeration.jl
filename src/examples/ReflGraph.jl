module ReflGraphSketch
export ReflGraph

using Catlab.CategoricalAlgebra
using ...Sketches


"""# REFLEXIVE GRAPHS # """

schema = @acset LabeledGraph begin
    V = 2; E = 3
    vlabel = [:V, :E]; elabel = [:refl, :src, :tgt]
    src    = [1,     2,    2]
    tgt    = [2,     1,    1]
end


ReflGraph = Sketch(schema, eqs=[[[:refl, :src], Symbol[]], [[:refl, :tgt], Symbol[]]])


end # module

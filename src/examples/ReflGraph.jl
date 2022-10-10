module ReflGraphSketch
export ReflGraph

using Catlab.CategoricalAlgebra
using ...Core


"""# REFLEXIVE GRAPHS # """

schema = @acset LGraph begin
    V = 2; E = 3
    vlabel = [:V, :E]; elabel = [:refl, :src, :tgt]
    src    = [1,     2,    2]
    tgt    = [2,     1,    1]
end


ReflGraph = Sketch(schema, eqs=[[[:refl, :src], [:refl, :tgt], [add_id(:V)]]])


end # module

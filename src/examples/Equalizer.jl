module EqualizerSketch
export Equalizer

using Catlab.CategoricalAlgebra
using ...Sketches


eqschema = @acset LabeledGraph begin
  V = 3; E = 3
  vlabel = [:A,:B,:E]; elabel = [:f,:g, :e]
  src = [1,1,3]; tgt = [2,2,1]
end

eqconed = @acset LabeledGraph begin
  V=3; E=2; vlabel=[:A,:A,:B]; elabel=[:f,:g]; src=[1,2]; tgt=[3,3]
end

Equalizer = Sketch(eqschema, cones=[Cone(eqconed, :E, [1=>:e,2=>:e])]);

end # module

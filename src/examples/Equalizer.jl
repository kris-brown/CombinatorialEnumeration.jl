module EqualizerSketch
export Equalizer

using Catlab.CategoricalAlgebra
using ...Core

"""
Equalizer of two parallel morphisms
"""

eqschema = @acset LGraph begin
  V = 3; E = 3; vlabel = [:A,:B,:E]; elabel = [:f,:g, :e];
  src = [1,1,3]; tgt = [2,2,1]
end

eqconed = @acset LGraph begin
  V=2; E=2; vlabel=[:A,:B]; elabel=[:f,:g]; src=1; tgt=2
end

Equalizer = Sketch(eqschema, cones=[Cone(eqconed, :E, [1=>:e])]);

end # module

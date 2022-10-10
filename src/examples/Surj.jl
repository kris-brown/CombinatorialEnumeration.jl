module SurjSketch
export Surj

using Catlab.CategoricalAlgebra
using ...Core

"""
Encoding of a surjection as a pair cone and cocone as described in
Barr and Wells CTCS 10.4.6

  d₀  d
C ⇉ A ⟶ B
  d₁
"""
schema = @acset LGraph begin
  V=3; E=3; vlabel=[:C,:A,:B]; elabel=[:d0,:d1,:d];
  src=[1,1,2]; tgt=[2,2,3]
end

"""c is a pullback: all pairs of a that agree on their value in d"""
c = Cone(@acset(LGraph, begin V=3;E=2;vlabel=[:A,:A,:B];
          elabel=[:d,:d];src=[1,2]; tgt=3 end,), :C, [1=>:d0,2=>:d1])
"""b is the coequalizer of c's legs"""
cc = Cone(@acset(LGraph, begin V=2;E=2;vlabel=[:C,:A];
          elabel=[:d0, :d1]; src=1; tgt=2 end), :B, [2=>:d])

Surj = Sketch(schema, cones=[c], cocones=[cc])

end # module

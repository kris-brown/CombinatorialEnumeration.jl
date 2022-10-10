module InjSketch
export Inj

using Catlab.CategoricalAlgebra
using ...Core

"""
Encoding of a injection as a limit cone with id legs
Barr and Wells CTCS 10.4.6

"""
schema = @acset LGraph begin
  V=2; E=1; vlabel=[:A,:B]; elabel=[:f];  src=[1]; tgt=[2]
end

"""           id    f
            ----> A ↘
      Apex A          B
            ----> A ↗
              id    f

"""
c = Cone(@acset(LGraph, begin V=3;E=2;vlabel=[:A,:A,:B];
          elabel=[:f,:f];src=[1,2]; tgt=3 end,), :A, [1=>:id_A,2=>:id_A])

Inj = Sketch(schema, cones=[c])

end # module

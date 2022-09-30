module PetriSketch
export Petri

using Catlab.CategoricalAlgebra
using ...Sketches
using CSetAutomorphisms



petschema = @acset LabeledGraph begin
  V=4; E=4; vlabel=[:S,:T,:I,:O]; elabel=[:is,:it,:os,:ot];
  src= [3,3,4,4]; tgt= [1,2,1,2]
end

Petri = Sketch(petschema)

"""
Create all petri nets with i S/T/I/O brute force.
"""
function all_petri(i::Int)
  i < 3 || error("don't try with large i like $i")
  res = Dict()
  I = @acset Petri.cset begin S=i; T=i; I=i; O=i end
  for os in Iterators.product([1:i for _ in 1:i]...)
    set_subpart!(I, :os, collect(os))
    for it in Iterators.product([1:i for _ in 1:i]...)
      set_subpart!(I, :it, collect(it))
      for si in Iterators.product([1:i for _ in 1:i]...)
        set_subpart!(I, :is, collect(si))
        for to in Iterators.product([1:i for _ in 1:i]...)
          set_subpart!(I, :ot, collect(to))
          cN = call_nauty(I)
          res[cN.hsh] = cN.cset
        end
      end
    end
  end
  return collect(values(res))
end

end # module

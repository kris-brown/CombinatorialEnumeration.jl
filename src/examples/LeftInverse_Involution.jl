module LeftInverse_InvolutionSketch
export LeftInverse_Involution

using Catlab.CategoricalAlgebra
using ...Core

"""
LEFT INVERSE / INVOLUTION

Models are pairs of involutions inv:B -> B
AND
monomorphisms f:A->B (with right inverse g: B->A)

This is just a simple illustrative example of sketches. TODO we will use it to
show how this sketch is the pushout of two smaller sketches and how we can
compute the models compositionally.
"""

##########
# Sketch #
##########

fgschema = @acset LGraph begin
  V = 2
  E = 3
  vlabel = [:A,:B]
  elabel = [:f,:g, :inv]
  src    = [1,  2,  2]
  tgt    = [2,  1,  2]
end

eqs = [
  [[:f, :g],   [add_id(:A)]],
  [[:inv,:inv],[add_id(:B)]]]
LeftInverse_Involution = Sketch(fgschema; eqs=eqs)


end # module

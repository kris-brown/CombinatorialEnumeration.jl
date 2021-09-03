include(joinpath(@__DIR__, "../../src/FLS.jl"))

"""
LEFT INVERSE / INVOLUTION

Models are pairs of involutions inv:B -> B
AND
monomorphisms f:A->B (with right inverse g: B->A)

The main purpose of this is a simple example which shows off
diagrams.
"""

fgschema = @acset LabeledGraph_{Symbol} begin
  V = 2
  E = 3
  vlabel = [:A,:B]
  elabel = [:f,:g, :inv]
  src    = [1,  2,  2]
  tgt    = [2,  1,  2]
end


fg = FLS(:fg, fgschema,[], [
  (:fginv,      [:f, :g],    []),
  (:involution, [:inv,:inv], [])])
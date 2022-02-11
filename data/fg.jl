using Revise
using Catlab.CategoricalAlgebra
using ModelEnumeration

"""
LEFT INVERSE / INVOLUTION

Models are pairs of involutions inv:B -> B
AND
monomorphisms f:A->B (with right inverse g: B->A)

The main purpose of this is a simple example which shows off
diagrams.
"""

fgschema = @acset LabeledGraph begin
  V = 2
  E = 3
  vlabel = [:A,:B]
  elabel = [:f,:g, :inv]
  src    = [1,  2,  2]
  tgt    = [2,  1,  2]
end


fg = Sketch(:FG, fgschema, Cone[], Cone[], [
  (:fginv,      [:f, :g],    []),
  (:involution, [:inv,:inv], [])])

es = EnumState()
I = create_premodel(fg, [:A=>2,:B=>2])
db=  init_db()

chase_set(db, fg, [I=>init_defined(fg, I)], 4)
chase_set(es, fg, [I=>init_defined(fg, I)], 4)
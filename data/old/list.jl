include(joinpath(@__DIR__, "../../src/Sketch.jl"))
include(joinpath(@__DIR__, "../../src/Models.jl"))


"""
All possible lists of elements from an arbitrary alphabet

This is different from inflist.jl, where each model is a single infinite list
on an alphabet.

11.2.1 from Barr and Wells CT4CS

Nontrivial models are infinite because, given a finite set of lists of size |S|,
there will be set of nonempty lists of size |S| - 1. And for each of these,
there will be a pair set of size (|S| - 1)*|D|, which will create that many
extra lists.
"""

one, d_s = Symbol.(["1", "d×s"])
listschema =  @acset LabeledGraph begin
  V = 5
  E = 6
  vlabel = [:list, :nonempty, :sublist, d_s, one]
  elabel = [:push, :pop, :empty, :incl, :π₁, :π₂]
  src    = [4,      2,     5,      2,    4,   4]
  tgt    = [2,      4,     1,      1,    3,   1]
end

"""Equalities"""
pop_push = (:pop_push, [:pop, :push], [])
push_pop = (:push_pop, [:push, :pop], [])

term_cone = Cone(LabeledGraph(), one, Pair{Int64, Symbol}[])
prod_cone = Cone(@acset(LabeledGraph, begin
  V = 2; vlabel = [:d, :s] end), d_s, [1=>:π₁, 2=>:π₂])

ccone = Cone(@acset(LabeledGraph, begin V = 2; vlabel = [one, :t] end),
             :s, [1=>:empty, 2=>:incl]) # s = 1 + t

list_sketch = Sketch(:list_, listschema, [term_cone, prod_cone], [ccone],
                     [pop_push, push_pop])


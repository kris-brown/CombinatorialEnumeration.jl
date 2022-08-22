using Test
# using Revise
using Catlab.CategoricalAlgebra
using ModelEnumeration

"""
Total orders

Transitive: ∀xyz x≤y ∧ y≤z → x≤z
Reflexive: ∀x x≤x
Antisymmetric: ∀xy x≤y ∧ y≤x → x=y
Partial: Transitive ∧ Reflexive ∧ Antisymmetric;
Linear (or total): Partial ∧ ∀xy x≤y ∨ y≤x
    π₁,π₂
   I ⇇ I×I
 refl ↘  ⇈ leq, geq
Cmp ⇉  Leq
  c1,c2

Unclear how this enforces antisymmetry, if it does.
"""

to_schema =  @acset LabeledGraph begin
  V = 4
  E = 9
  vlabel = [:I, :II, :Leq, :Cmp]
  elabel = [:l, :r,  :leq, :geq, :swap, :refl, :c1, :c2, :cmp]
  src    = [2,    2,  3,    3,    2,     1,     4,  4,   4]
  tgt    = [1,    1,  2,    2,    2,     3,     3,  3,   3]
end

"""Equations"""
eqs =[(:refl_l, [:refl, :leq, :l], []),
      (:refl_r, [:refl, :leq, :r], []),
      (:cmp_1, [:c1, :leq, :l], [:cmp, :leq, :l]),
      (:cmp_2, [:c2, :leq, :r], [:cmp, :leq, :r]),
      (:swap_l, [:swap, :l], [:r]),
      (:swap_r, [:swap, :r], [:l]),
      (:swap_g, [:geq, :swap], [:leq])
    ]

"""Cones"""
# Pairs of index elements
I2_cone = Cone(@acset(LabeledGraph, begin V=2; vlabel=[:I, :I] end),
              :II, [1=>:l, 2=>:r])

# Pair of composable arrows in the preorder
Pair_cone = Cone(@acset(LabeledGraph, begin
  V=5; vlabel=[:Leq, :Leq, :II, :II, :I]
  E=4; src=[1,2,3,4]; tgt=[3,4,5,5]; elabel=[:leq,:leq, :r, :l] end),
  :Cmp, [1=>:c1, 2=>:c2])


"""Cocones"""
# I×I is also a pushout
I2_cocone = Cone(@acset(LabeledGraph, begin
               V = 3; vlabel = [:I, :Leq, :Leq]
               E=2; elabel=[:refl, :refl]; src=[1,1]; tgt=[2,3]
              end), :II, [2=>:leq, 3=>:geq])

to_sketch = Sketch(:total_order, to_schema, [I2_cone, Pair_cone],
                  [I2_cocone], eqs)

# HELPER FUNCTIONS
##################
"""Create a total order on `n` objects"""
function from_int(n::Int)::StructACSet
  I = to_sketch.cset()
  p1, p2 = collect.(zip(collect(Iterators.product(1:n,1:n))...))
  p1p2 = collect(zip(p1,p2))
  leq = findall(a-> a[1]<=a[2], p1p2)
  swp = [findfirst(x->x==(b,a), p1p2) for (a,b) in p1p2]
  nleq = length(leq)
  add_parts!(I, :I, n)
  add_parts!(I, :II, n*n; l=p1, r=p2, swap=swp)
  add_parts!(I, :Leq, nleq; leq=leq)
  refl = [only(incident(I, only(incident(I, i, :l) ∩
                                incident(I, i, :r)), :leq))  for i in  1:n]
  set_subpart!(I, :refl, refl); set_subpart!(I, :geq, I[[:leq,:swap]])
  all_c = collect(Iterators.product(1:nleq,1:nleq))
  c_inds = findall(z-> I[z[1], [:leq, :r]] == I[z[2], [:leq, :l]], all_c )
  c1 = [all_c[ci][1] for ci in c_inds]
  c2 = [all_c[ci][2] for ci in c_inds]
  cmp = [only(incident(I,
      only(incident(I, I[x1, [:leq, :l]],:l)
            ∩ incident(I, I[x2, [:leq,:r]],:r)), :leq))
      for (x1,x2) in zip(c1,c2)]
  add_parts!(I, :Cmp, length(c1); c1=c1, c2=c2, cmp=cmp)
  return I
end

# EXAMPLES
##########
r1, r2, r3 = from_int.(1:3) # (1,1), (2,3), (3,6)

db = init_db(reset=true)
S = to_sketch;
Jinit = create_premodel(S, [:I=>1, :Leq=>1])
chase_set(db, S, StructACSet[Jinit], 2)
Jinit = create_premodel(S, [:I=>2, :Leq=>3])
chase_set(db, S, StructACSet[Jinit], 5)
Jinit = create_premodel(S, [:I=>3, :Leq=>6])
chase_set(db, S, StructACSet[Jinit], 9)

for (m, r) in zip(get_models(db, S, 9), [r1,r2,r3])
  @test is_isomorphic(m, r)
end


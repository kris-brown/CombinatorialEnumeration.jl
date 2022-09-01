module Cat

using Revise
using Test
using Catlab.CategoricalAlgebra
using ModelEnumeration

"""Theory of categories


Cmp represents composable pairs of Arrows (c1, c2 are pullback legs, c3 is free
to choose as the composition result).

Asc represents pairs of Cmp's which overlap, i.e. triples of Arrows.



      Cmp
      ⇊ ↓
       A ⇉ O
"""
catschema = @acset LabeledGraph begin
  V = 7;  E = 17
  vlabel=[:O, :A, :cmp, :asc_l, :asc_r, :leftid, :rightid]
  elabel=[:src,:tgt, :refl,
      :c1, :c2, :c3,
      :l1, :l2, :r1, :r2, :asc,
      :lidv, :lida, :lidc,
      :ridv, :rida, :ridc]
  src = [2,2,1, 3,3,3, 4,4,5,5,4, 6,6,6, 7,7,7]
  tgt = [1,1,2, 2,2,2, 3,3,3,3,5, 1,2,3, 1,2,3]
end

"""Pair of arrows that match head to tail"""
cmpconed = @acset LabeledGraph begin
  V = 3;  E = 2; vlabel = [:A,:A,:O]; elabel = [:src, :tgt]
  src = [1,2]; tgt = 3
end

cmpcone = Cone(cmpconed, :cmp, [1=>:c1, 2=>:c2])

"""
 (m₁⋅m₂)⋅m₃
  |     |
  ↓     ↓
Cmp    Cmp
 c₃↘   ↙ c₁
     A

"""
asc_l_coned =  @acset LabeledGraph begin
  V = 3; E = 2; vlabel = [:cmp, :cmp, :A]; elabel = [:c3, :c1];
  src = [1,2]; tgt = 3
end

asc_l_cone = Cone(asc_l_coned,   :asc_l,  [1=>:l1, 2=>:l2])

"""
 m₁⋅(m₂⋅m₃)
  |     |
  ↓     ↓
Cmp    Cmp
 c₂ ↘  ↙ c₃
     A


"""
asc_r_coned =  @acset LabeledGraph begin
  V = 3; E = 2; vlabel = [:cmp, :cmp, :A]; elabel = [:c2, :c3]
  src = [1,2]; tgt = [3,3]
end

asc_r_cone = Cone(asc_r_coned,   :asc_r,   [1=>:r1, 2=>:r2])


"""(id(x)) ⋅ _ """
leftid_coned = @acset LabeledGraph begin
  V = 3; E = 2; vlabel = [:O, :A, :cmp]; elabel = [:c1, :refl]
  src = [3,1]; tgt = 2
end

leftid_cone = Cone(leftid_coned,  :leftid,  [1=>:lidv, 2=>:lida, 3=>:lidc])

rightid_coned = @acset LabeledGraph begin
  V = 3; E = 2;  vlabel = [:O, :A, :cmp]; elabel = [:c2, :refl]
  src = [3,1]; tgt = [2,2]
end

rightid_cone = Cone(rightid_coned, :rightid, [1=>:ridv, 2=>:rida, 3=>:ridc])

catcones = [cmpcone, asc_l_cone, asc_r_cone, leftid_cone, rightid_cone]

cateqs = [
  [[:refl, :src], Symbol[]],     # refl_src
  [[:refl, :tgt], Symbol[]],     # refl_tgt
  [[:lidc, :c2], [:lidc, :c3]],  # Unitality
  [[:ridc, :c1], [:ridc, :c3]],  # Unitality
  [[:l1,:c1], [:asc, :r1, :c1]], # associativity
  [[:l1,:c2], [:asc, :r2, :c1]], # associativity
  [[:l2,:c2], [:asc, :r2, :c2]], # associativity
  [[:l2,:c3], [:asc, :r1, :c3]]  # associativity
]

S = Sketch(:catt, catschema, cones=catcones,  eqs=cateqs);

# function runtests()
I = @acset S.cset begin O=1; A=2 end
es = init_db(S,I, [:O,:A])
chase_db(S,es)

# end


end # module

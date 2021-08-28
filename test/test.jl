include(joinpath(@__DIR__, "../src/ModelEnumeration.jl"))

# Example: categories

catschema = @acset LabeledGraph_{Symbol} begin
  V = 7
  vlabel=[:O, :A, :cmp, :asc_l, :asc_r,
          :leftid, :rightid]
  E = 17
  elabel=[:src,:tgt, :refl,
      :c1, :c2, :c3,
      :l1, :l2, :r1, :r2, :asc,
      :lidv, :lida, :lidc,
      :ridv, :rida, :ridc,
      ]

  src = [2,2,1, 3,3,3, 4,4,5,5,4, 6,6,6, 7,7,7]
  tgt = [1,1,2, 2,2,2, 2,2,2,2,5, 1,2,3, 1,2,3]
end

"""Pair of arrows that match head to tail"""
cmpconed = @acset LabeledGraph_{Symbol} begin
  V = 3
  vlabel = [:A,:A,:O]
  E = 2
  elabel = [:src, :tgt]
  src = [1,2]
  tgt = [3,3]
end
cmpcone = Cone(cmpconed,      :cmp,     Dict([1=>:c1, 2=>:c2]))
"""(m₁⋅m₂)⋅m₃"""
asc_l_coned =  @acset LabeledGraph_{Symbol} begin
  V = 3
  E = 2
  vlabel = [:cmp, :cmp, :A]
  elabel = [:c3, :c1]
  src = [1,2]
  tgt = [3,3]
end

asc_l_cone = Cone(asc_l_coned,   :asc_l,   Dict([1=>:l1, 2=>:l2]))

"""m₁⋅(m₂⋅m₃)"""
asc_r_coned =  @acset LabeledGraph_{Symbol} begin
  V = 3
  E = 2
  vlabel = [:cmp, :cmp, :A]
  elabel = [:c2, :c3]
  src = [1,2]
  tgt = [3,3]
end
asc_r_cone = Cone(asc_r_coned,   :asc_r,   Dict([1=>:r1, 2=>:r2]))

leftid_coned = @acset LabeledGraph_{Symbol} begin
  V = 3
  E = 2
  vlabel = [:O, :A, :cmp]
  elabel = [:c1, :refl]
  src = [3,1]
  tgt = [2,2]
end
leftid_cone = Cone(leftid_coned,  :leftid,  Dict([1=>:lidv, 2=>:lida, 3=>:lidc]))

rightid_coned = @acset LabeledGraph_{Symbol} begin
  V = 3
  E = 2
  vlabel = [:O, :A, :cmp]
  elabel = [:c2, :refl]
  src = [3,1]
  tgt = [2,2]
end
rightid_cone = Cone(rightid_coned, :rightid, Dict([1=>:ridv, 2=>:rida, 3=>:ridc]))

catcones = Set([cmpcone, asc_l_cone, asc_r_cone, leftid_cone, rightid_cone])

cateqs = Set([
  # reflexivity
  [:refl, :src] => Symbol[],
  [:refl, :tgt] => Symbol[],
  # Unitality
  [:lidc, :c2] => [:lidc, :c3],
  [:ridc, :c1] => [:ridc, :c3],
  # associativity
  [:l1,:c1] => [:asc, :r2, :c1],
  [:l1,:c2] => [:asc, :r1, :c1],
  [:l2, :c2] => [:asc, :r2, :c2],
  [:l2, :c3] => [:asc, :r1, :c3]
])

catfls = FLS(:cat, catschema, catcones, cateqs)


I = grph_to_cset(:cat, catschema);
add_part!(I, :A);
add_part!(I, :O; refl=1);
J = initrel(catfls, I);
# Ks = apply_tgds(catfls, J);
# K = Ks[1] # 3^3 models, first one is free
# e = apply_cones!(catfls, K)
# apply_egds!(catfls, K, e)
Ks = chasestep(catfls, J)


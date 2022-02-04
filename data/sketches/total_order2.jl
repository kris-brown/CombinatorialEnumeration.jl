using Revise
using ModelEnumeration
using Catlab.CategoricalAlgebra
"""
Leq as map from I×I to Bool (1+1).
> ⟶ Swap ⟵ Antisym
      ⇊
 𝔹 ⟵I×I ⇇ Cmp
 ⇈    ⇊ ↑ refl
 1    I

We can define swap as a map from II->II with certain path equalities
But this is inefficient to compute with (we can't determine swap, because it is
never the final step of a path equality, so have to guess and check).
- this change reduced the number of premodels required to (exhaustively) search
through total orders with three elements from thousands down to 500.

"""
one, I_, C_, G_ = Symbol.(["1", "!ᵢ", "!c", "!g"])
to_schema =  @acset LabeledGraph begin
  V = 8; E = 16; vlabel = [:I, :II, :𝔹, one, :Cmp, :Antisym, :>, :Swap]
  elabel = [:l, :r, :refl, I_, C_,G_, :c1, :c2, :cmp, :a1, :leq, :⊤, :⊥, :gt, :s1, :s2]
  src    = [2,   2,  1,    1,  5,  7, 5,   5,   5,    6,    2,    4,  4,  7,   8,   8]
  tgt    = [1,   1,  2,    4,  4,  4, 2,   2,   2,    8,    3,    3,  3,  8,   2,   2]
end

"""Equations"""
eqs =[ # DEFINE REFL
      (:refl_l, [:refl, :l], []),
      (:refl_r, [:refl, :r], []),
      # DEFINE CMP
      (:cmp_1, [:c1, :l], [:cmp, :l]),
      (:cmp_2, [:c2, :r], [:cmp, :r]),
      # AXIOMS
      (:antisymmetry, [:a1, :s1, :l], [:a1, :s1, :r]),
      (:transitivity, [:cmp, :leq], [C_, :⊤]),
      (:reflexivity, [:refl, :leq], [I_, :⊤]),
      (:totality, [:gt, :s2, :leq], [G_, :⊤])
    ]


"""Cones"""
one_cone = Cone(LabeledGraph(), one, Pair{Int64, Symbol}[])

# Pairs of index elements
I2_cone = Cone(@acset(LabeledGraph, begin V=2; vlabel=[:I, :I] end),
              :II, [1=>:l, 2=>:r])

Geq_cone = Cone(@acset(LabeledGraph, begin V=4; E=3; vlabel=[one, :𝔹,:II, :Swap]
            src=[1,3,4]; tgt=[2,2,3]; elabel=[:⊥, :leq, :s1] end), :>, [4=>:gt])

# Pair of composable ⊤ pairs in the preorder
Pair_cone = Cone(@acset(LabeledGraph, begin
  V=5; vlabel=[:II, :II, :I, :𝔹, one]
  E=5; src=[1,2,1,2,5]; tgt=[3,3,4,4,4]; elabel=[:r, :l, :leq, :leq, :⊤] end),
  :Cmp, [1=>:c1, 2=>:c2])

# Swapped pairs of ≤
Swap_cone = Cone(@acset(LabeledGraph, begin
  V=4; vlabel=[:II, :II, :I, :I]; E=4;
  src   =[1,  1,  2,  2];
  tgt   =[3,  4,  3,  4];
  elabel=[:l,:r, :r, :l] end),
  :Swap, [1=>:s1, 2=>:s2])

# Identify a pair which is ⊤ AND whose swap is ⊤
Antisym_cone = Cone(@acset(LabeledGraph, begin
  V=5; vlabel=[:Swap, :II, :II, one, :𝔹]
  E=5; src=[1,1,2,3,4]; tgt=[2,3,5,5,5]; elabel=[:s1,:s2, :leq, :leq, :⊤] end),
  :Antisym, [1=>:a1])

"""Cocones"""
# I×I is also a pushout
Bool_cocone = Cone(@acset(LabeledGraph, begin
                 V = 2; vlabel = [one, one] end), :𝔹, [1=>:⊤, 2=>:⊥])
"""Overall"""
to_sketch = Sketch(:total_order, to_schema,
                   [one_cone, I2_cone, Pair_cone, Swap_cone, Geq_cone, Antisym_cone],
                   [Bool_cocone], eqs)
#
"""Create a total order on `n` objects"""
function from_int(n::Int)::StructACSet
  I = to_sketch.cset()
  p1, p2 = collect.(zip(collect(Iterators.product(1:n,1:n))...))
  p1p2 = collect(zip(p1,p2))
  leq = [a[1]<=a[2] ? 1 : 2 for a in p1p2]
  nleq = length(leq)
  refl = only.([findall(x-> x==(i,i), p1p2) for i in 1:n])
  add_parts!(I, :𝔹, 2)
  add_parts!(I, one, 1; ⊤=[1], ⊥=[2])
  add_parts!(I, :I, n; Dict([I_=>repeat([1], n)])...)
  add_parts!(I, :II, n*n; l=p1, r=p2, leq=leq)
  set_subpart!(I, :refl, refl);
  # Swap
  swp = [findfirst(x->x==(b,a), p1p2) for (a,b) in p1p2]
  add_parts!(I, :Swap, nleq; s1=collect(1:nleq), s2=swp)
  # GT
  gt = findall(==(2), leq)
  add_parts!(I, :>, length(gt); gt=gt, Dict([G_=>repeat([1], length(gt))])...)
  # Add composable arrows
  all_c = collect(Iterators.product(1:n^2,1:n^2))
  c1, c2, cmp = [Int[] for _ in 1:3]
  for (p1, p2) in all_c
    if I[p1,:leq]==1 &&I[p2,:leq]==1 && I[p1, :r] == I[p2, :l]
      cmp_ = incident(I, I[p1,:l], :l) ∩ incident(I, I[p2,:r], :r)
      push!(c1, p1); push!(c2, p2); push!(cmp, only(cmp_))
    end
  end
  add_parts!(I, :Cmp, length(c1); c1=c1, c2=c2, cmp=cmp,
             Dict([C_ => repeat([1], length(c1))])...)
  # Add antisym
  add_parts!(I, :Antisym, n; a1=refl)
  return I
end
v1, v2, v3 = from_int.([1,2,3])
#
db = init_db(reset=true)

S= to_sketch;
Jinit = create_premodel(S, [:I=>3])
chase_set(db, S, StructACSet[Jinit], 3)


ms = get_models(db, S, 3)
# Jinit = create_premodel(S, [:I=>1])
# chase_set(db, S, StructACSet[Jinit], 1)

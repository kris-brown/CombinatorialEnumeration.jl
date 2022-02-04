using Revise
using ModelEnumeration
using Catlab.CategoricalAlgebra
"""
Leq as map from I×I to Bool (1+1).
   Antisym / >
     ⇊
𝔹 ⟵I×I ⇇ Cmp
⇈    ⇊ ↑ refl
1 ⟵ I
!
"""
one, I_, C_, G_ = Symbol.(["1", "!ᵢ", "!c", "!g"])
to_schema =  @acset LabeledGraph begin
  V = 7
  E = 15
  vlabel = [:I, :II, :𝔹, one, :Cmp, :Antisym, :>]
  elabel = [:l, :r, :refl, I_, C_,G_, :c1, :c2, :cmp, :a1, :leq, :⊤, :⊥, :swap, :gt]
  src    = [2,   2,  1,    1,  5,  7, 5,   5,   5,    6,    2,    4,  4,  2,    7]
  tgt    = [1,   1,  2,    4,  4,  4, 2,   2,   2,    2,    3,    3,  3,  2,    2]
end

"""Equations"""
eqs =[ # DEFINE REFL
      (:refl_l, [:refl, :l], []),
      (:refl_r, [:refl, :r], []),
       # DEFINE SWAP
      (:swap_l, [:swap, :l], [:r]),
      (:swap_r, [:swap, :r], [:l]),
      # DEFINE CMP
      (:cmp_1, [:c1, :l], [:cmp, :l]),
      (:cmp_2, [:c2, :r], [:cmp, :r]),
      # AXIOMS
      (:antisymmetry, [:a1; :l], [:a1; :r]),
      (:transitivity, [:cmp, :leq], [C_, :⊤]),
      (:reflexivity, [:refl, :leq], [I_, :⊤]),
      (:totality, [:gt, :swap, :leq], [G_, :⊤])
    ]


"""Cones"""
one_cone = Cone(LabeledGraph(), one, Pair{Int64, Symbol}[])

# Pairs of index elements
I2_cone = Cone(@acset(LabeledGraph, begin V=2; vlabel=[:I, :I] end),
              :II, [1=>:l, 2=>:r])

Geq_cone = Cone(@acset(LabeledGraph, begin V=3; vlabel=[:II, :𝔹, one]
              E=2; src=[1,3]; tgt=[2,2]; elabel=[:leq, :⊥] end), :>, [1=>:gt])

Geq_cone2 = Cone(@acset(LabeledGraph, begin V=3; vlabel=[ :𝔹, :II, one]
              E=2; src=[2,3]; tgt=[1,1]; elabel=[:leq, :⊥] end), :>, [2=>:gt])

# Pair of composable ⊤ pairs in the preorder
Pair_cone = Cone(@acset(LabeledGraph, begin
  V=5; vlabel=[:II, :II, :I, :𝔹, one]
  E=5; src=[1,2,1,2,5]; tgt=[3,3,4,4,4]; elabel=[:r, :l, :leq, :leq, :⊤] end),
  :Cmp, [1=>:c1, 2=>:c2])

# Identify a pair which is ⊤ AND whose swap is ⊤
Swap_cone = Cone(@acset(LabeledGraph, begin
  V=4; vlabel=[:II, :II, one, :𝔹]
  E=4; src=[1,1,2,3]; tgt=[2,4,4,4]; elabel=[:swap,:leq, :leq, :⊤] end),
  :Antisym, [1=>:a1])

"""Cocones"""
# I×I is also a pushout
Bool_cocone = Cone(@acset(LabeledGraph, begin
                 V = 2; vlabel = [one, one] end), :𝔹, [1=>:⊤, 2=>:⊥])
"""Overall"""
to_sketch = Sketch(:total_order, to_schema,
                   [one_cone, I2_cone, Pair_cone, Swap_cone, Geq_cone],
                   [Bool_cocone], eqs)
#
"""Create a total order on `n` objects"""
function from_int(n::Int)::StructACSet
  I = to_sketch.cset()
  p1, p2 = collect.(zip(collect(Iterators.product(1:n,1:n))...))
  p1p2 = collect(zip(p1,p2))
  leq = [a[1]<=a[2] ? 1 : 2 for a in p1p2]
  gt = findall(==(2), leq)
  swp = [findfirst(x->x==(b,a), p1p2) for (a,b) in p1p2]
  refl = only.([findall(x-> x==(i,i), p1p2) for i in 1:n])
  add_parts!(I, :𝔹, 2)
  add_parts!(I, one, 1; ⊤=[1], ⊥=[2])
  add_parts!(I, :I, n; Dict([I_=>repeat([1], n)])...)
  add_parts!(I, :II, n*n; l=p1, r=p2, swap=swp, leq=leq)
  set_subpart!(I, :refl, refl);
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
Jinit = create_premodel(S, [:I=>2])
chase_set(db, S, StructACSet[Jinit], 2)


J2 = create_premodel(S, v2) # problem: chasing this creates more > elements
eq = init_eq(S,J2)
ns = NewStuff()
w = Weights(()->.0) # initial weighting
qc = query_cone(S, J2, Geq_cone, eq, w) # THIS SHOULD JUST RETURN [3]

# get_models(db, S, 3)
# Jinit = create_premodel(S, [:I=>1])
# chase_set(db, S, StructACSet[Jinit], 1)

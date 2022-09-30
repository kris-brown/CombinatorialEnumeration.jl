module TestCategory

using Test
using Catlab.CategoricalAlgebra, Catlab.Theories
using CombinatorialEnumeration
using CombinatorialEnumeration.Examples.CategorySketch: mk_cat, Δ, monoid

S = CombinatorialEnumeration.Cat

# Two objects, three arrows
###########################

I = @acset S.cset begin O=2; A=3 end;
es = init_premodel(S,I, [:O,:A]);
chase_db(S,es)

expected = [
  mk_cat(2,[1=>1]), # non id points 1->1.  Composed with itself is identity
  mk_cat(2,[1=>1],[(1,1,1)]),     # non id cmposed with itself is itself
  mk_cat(2,[1=>2])  # non id points 1->2
]

@test test_models(es,S,expected; f=Δ)

# Two objects, four arrows
##########################

I = @acset S.cset begin O=2; A=4 end;
es = init_premodel(S,I, [:O,:A]);
chase_db(S,es)

expected = [
  mk_cat(2, [1=>2,1=>2]), # • ⇉ •
  mk_cat(2, [1=>2,2=>1]), # • ⇆ •

  mk_cat(2, [1=>1,2=>2],[(1,1,1),(2,2,2)]), # •↺ •↺ neither is involution
  mk_cat(2, [1=>1,2=>2],[(1,1,1)]),         # •↺ •↺ one is involution
  mk_cat(2, [1=>1,2=>2]),                   # •↺ •↺ both involutions

  mk_cat(2, [1=>2,2=>2]),           # •⟶•↺  with involution
  mk_cat(2, [1=>2,2=>2],[(2,2,2)]), # •⟶•↺  without involution

  mk_cat(2, [2=>1,2=>2]),           # •⟵•↺  with involution
  mk_cat(2, [2=>1,2=>2],[(2,2,2)]), # •⟵•↺  without involution

  # Categories with one object are monoids. There are 7 monoids of order 3.
  monoid([0 2;2 2]) ⊕ mk_cat(1),
  monoid([2 0 ;0 1]) ⊕ mk_cat(1),
  monoid([1 1;1 2]) ⊕ mk_cat(1),
  monoid([1 1;1 1]) ⊕ mk_cat(1),
  monoid([1 2;2 1]) ⊕ mk_cat(1),
  monoid([1 1; 2 2]) ⊕ mk_cat(1),  # non-commutative
  monoid([1 2 ;1 2 ]) ⊕ mk_cat(1), # non-commutative
]

# This seems like a case where we could exploit compositional structure, e.g.
# if we had computed with O=1, A=3 already and "⊕ mk_cat(1)" all the results...

@test test_models(es,S,expected; f=Δ)

end # module

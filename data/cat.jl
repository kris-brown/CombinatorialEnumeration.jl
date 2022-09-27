module Category

using Test
using Catlab.CategoricalAlgebra, Catlab.Present, Catlab.Theories
using CombinatorialEnumeration

"""
Categories are a reflexive graph with a associative binary composition operation
on composable arrows.

Analogy with semigroups:
  k ↦ cmp
  π₁×π₂ ↦ c1
  π₂×π₃ ↦ c2
  id×k ↦ id_cmp
  k×id ↦ cmp_id
  s ↦ A
  s2 ↦ Cmp
  s3 ↦ Asc
"""

cat_schema = @acset LabeledGraph begin
  V = 4; E = 15; vlabel = [:O, :A, :Cmp, :Asc]
  elabel = [:dom,:codom,:refl,:cmp,:π₁,:π₂,:Π₁,:Π₂,:Π₃, :c1, :c2, :id_cmp, :cmp_id, :reflsrc_id, :id_refltgt]
  src=[2,2,1,3,3,3,4,4,4,4,4,4,4,2,2]
  tgt=[1,1,2,2,2,2,2,2,2,3,3,3,3,3,3]
end

"""Cmp is pullback

      Cmp
      ↙ ↘
     A   A
codom ↘ ↙ dom
       A
"""
cmp_diag = @acset LabeledGraph begin
  V = 3;  E = 2; vlabel = [:A,:A,:O]; elabel = [:codom, :dom]
  src = [1,2]; tgt = 3
end
cmpcone = Cone(cmp_diag, :Cmp, [1=>:π₁, 2=>:π₂])

"""Asc is pullback
    Asc
    ↙  ↘
  Cmp  Cmp
 π₂ ↘ ↙ π₁
     A
"""
asc_diag = @acset LabeledGraph begin
  V = 3;  E = 2; vlabel = [:Cmp,:Cmp,:A]; elabel = [:π₂, :π₁]
  src = [1,2]; tgt = 3
end

asccone = Cone(asc_diag, :Asc, [1=>:c1, 2=>:c2])


cat_eqs = [
  [[:c1, :π₁], [:Π₁]], #c1_p1
  [[:c1, :π₂], [:Π₂]], #c1_p2
  [[:c2, :π₁], [:Π₂]], #c2_p1
  [[:c2, :π₂], [:Π₃]], #c2_p2

  [[:cmp_id, :π₁], [:c1,:cmp]], # cmp_id_p1
  [[:cmp_id, :π₂], [:Π₃]], # cmpid_p2

  [[:id_cmp, :π₂], [:c2,:cmp]], # idk_p2
  [[:id_cmp, :π₁], [:Π₁]], # idk_p1

  [[:id_cmp, :cmp], [:cmp_id, :cmp]], # assoc

  [[:refl, :dom], [add_id(:O)]],
  [[:refl,:codom], [add_id(:O)]],
  [[:cmp,:dom], [:π₁, :dom]],
  [[:cmp,:codom], [:π₂, :codom]],
  # the pair (id, refl;src) has, as first element, id (likewise for tgt)
  [[:reflsrc_id,:π₂], [add_id(:A)]],
  [[:id_refltgt,:π₁], [add_id(:A)]],
  # the pair (id, refl;src) has, as second element, src (likewise for tgt)
  [[:reflsrc_id,:π₁], [:dom, :refl]],
  [[:id_refltgt,:π₂], [:codom, :refl]],
  # the composite of a morphism and an identity is itself
  [[:reflsrc_id,:cmp], [add_id(:A)]],
  [[:id_refltgt,:cmp], [add_id(:A)]],
]

S = Sketch(cat_schema, cones=[cmpcone, asccone], eqs=cat_eqs);

@present ThCat(FreeSchema) begin
  (O,A,Cmp)::Ob
  refl::Hom(O,A)
  (dom,codom)::Hom(A,O)
  (cmp,π₁,π₂)::Hom(Cmp,A)
end

@acset_type SCat(ThCat)

Δ = DeltaMigration(FinFunctor(
    Dict(:O=>:O,:A=>:A,:Cmp=>:Cmp),
    Dict(x=>x for x in [:refl,:dom,:codom,:cmp,:π₁,:π₂]),
  ThCat,Presentation(S.cset)), S.cset, SCat)

"""Give dom/codom for non-id morphisms, give composiitons that aren't id"""
function mk_cat(o::Int,h::Vector{Pair{Int,Int}}=Pair{Int,Int}[],d_::Vector{Tuple{Int,Int,Int}}=Tuple{Int,Int,Int}[])
  d,h = deepcopy.([[(d1=>d2)=>d3 for (d1,d2,d3) in d_],h])
  nh = length(h)
  append!(h, [i=>i for i in 1:o])
  ref = nh+1:nh+o
  for (e1,(s1,t1)) in enumerate(h)
    for (e2,(s2,t2)) in enumerate(h)
      if t1 == s2 && (e1=>e2) ∉ first.(d)
        if e1 ∈ ref push!(d, (e1=>e2)=>e2)
        elseif e2 ∈ ref push!(d, (e1=>e2)=>e1)
        elseif  s1 == t2
          push!(d,(e1=>e2) => ref[s1])
        else
          poss = findall(e->e[1]==s1&&e[2]==t2, h)
          if length(poss) == 1
            push!(d,(e1=>e2) => only(poss))
          else
          error("need to specify composition $e1;$t2")
          end
        end
      end
    end
  end
  return @acset(SCat, begin O=o; A=nh+o; Cmp=length(d); refl=ref;
    dom=first.(h); codom=last.(h)
    π₁=first.(first.(d));π₂=last.(first.(d)); cmp=last.(d) end)
end

function monoid(m)
  n = first(size(m))
  h = map(Iterators.product(1:n,1:n)) do (i,j)
    (i,j, m[i,j] == 0 ? n+1 : m[i,j])
  end |> vec
  mk_cat(1, [1=>1 for _ in 1:n], h)
end


function runtests()

  I = @acset S.cset begin O=2; A=3 end;
  es = init_premodel(S,I, [:O,:A]);
  chase_db(S,es)
  expected = [
    mk_cat(2,[1=>1]), # non id points 1->1.  Composed with itself is identity
    mk_cat(2,[1=>1],[(1,1,1)]),     # non id cmposed with itself is itself
    mk_cat(2,[1=>2])     # non id points 1->2
  ]

  @test test_models(es,S,expected; f=Δ)

  ###

  I = @acset S.cset begin O=2; A=4 end;
  es = init_premodel(S,I, [:O,:A]);
  chase_db(S,es)
  expected = [
    mk_cat(2, [1=>2,1=>2]), # • ⇉ •
    mk_cat(2, [1=>2,2=>1]), # • ⇆ •

    mk_cat(2, [1=>1,2=>2],[(1,1,1),(2,2,2)]), # •↺ •↺ neither is involution
    mk_cat(2, [1=>1,2=>2],[(1,1,1)]), # •↺ •↺ one is involution
    mk_cat(2, [1=>1,2=>2]), # •↺ •↺ both involutions

    mk_cat(2, [1=>2,2=>2]), # •⟶•↺  with involution
    mk_cat(2, [1=>2,2=>2],[(2,2,2)]), # •⟶•↺  without involution

    mk_cat(2, [2=>1,2=>2]), # •⟵•↺  with involution
    mk_cat(2, [2=>1,2=>2],[(2,2,2)]), # •⟵•↺  without involution

    # Categories with one object are monoids. There are 7 monoids of order 3.
    monoid([0 2;2 2]) ⊕ mk_cat(1),
    monoid([2 0 ;0 1]) ⊕ mk_cat(1),
    monoid([1 1;1 2]) ⊕ mk_cat(1),
    monoid([1 1;1 1]) ⊕ mk_cat(1),
    monoid([1 2;2 1]) ⊕ mk_cat(1),
    monoid([1 1; 2 2]) ⊕ mk_cat(1), # non-commutative
    monoid([1 2 ;1 2 ]) ⊕ mk_cat(1), # non-commutative

  ]

  @test test_models(es,S,expected; f=Δ)

  return true
end

end # module

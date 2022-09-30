module GraphOverlapSketch
export GraphOverlap

using Catlab.CategoricalAlgebra, Catlab.Graphics, Catlab.Present, Catlab.Graphs,
      Catlab.Programs
using ...Sketches, ...SketchColimits
using ...Models: is_surjective
using ..InjSketch, ..SurjSketch, ..CoproductSketch, ..JointSurjSketch

using DataStructures
using CSetAutomorphisms
import ...Sketches
const LG = Sketches.LabeledGraph



"""
Using the surjection encoding, this is a sketch for a two pairs of maps that are
each *jointly surjective*. These correspond to the vertex and edge maps of
graph homomorphisms from G₁ and G₂ into G₃.

         V₁
   π₁  ↙   ↘ fᵥ
PB ⇉ V₁+V₂ ↠ V₃
   π₂    ↖ ↗ gᵥ
          V₂

We furthermore need to specify the homomorphism condition (which relates fᵥ to
fₑ, e.g.) and the graph data (which relates V₁ to E₁, e.g.)
"""

schema = @acset LG begin
  V=10; E=20; vlabel=[:V₁,:V₂,:V₃,:V₁_V₂,:PBᵥ,:E₁,:E₂,:E₃,:E₁_E₂,:PBₑ];
  elabel=[:fᵥ,:gᵥ,:iᵥ₁,:iᵥ₂,:pᵥ₁,:pᵥ₂,:fᵥ_gᵥ,
          :fₑ,:gₑ,:iₑ₁,:iₑ₂,:pₑ₁,:pₑ₂,:fₑ_gₑ,
          :s₁,:t₁,:s₂,:t₂,:s₃,:t₃];
  src=[1,2,1,2,5,5,4, 6,7,6,7,10,10,9, 6,6,7,7,8,8];
  tgt=[3,3,4,4,4,4,3, 8,8,9,9,9, 9, 8, 1,1,2,2,3,3]
end

@present SchRes(FreeSchema) begin
  (V₁,V₂,V₃,E₁,E₂,E₃)::Ob
  fᵥ::Hom(V₁,V₃); gᵥ::Hom(V₂,V₃)
  fₑ::Hom(E₁,E₃); gₑ::Hom(E₂,E₃)
  (s₁,t₁)::Hom(E₁,V₁)
  (s₂,t₂)::Hom(E₂,V₂)
  (s₃,t₃)::Hom(E₃,V₃)
end
@acset_type R(SchRes)

# View the schema here
# to_graphviz(schema;node_labels=:vlabel,edge_labels=:elabel)

"""PB is a pullback: all pairs of A+B that agree on their value in c"""
cs = map([:V=>:ᵥ,:E=>:ₑ]) do (x,y)
  vlabel = Symbol.([fill("$(x)₁_$(x)₂",2)...,"$(x)₃"])
  elabel = Symbol.(fill("f$(y)_g$y" ,2))
  lgs    = [1=>Symbol("p$(y)₁"),2=>Symbol("p$(y)₂")]
  g = @acset(LG, begin V=3;E=2; vlabel=vlabel; elabel=elabel;
                                 src=[1,2]; tgt=3 end,)
  Cone(g, Symbol("PB$y"), lgs)
end

"""(C,c) is the coequalizer of PB's legs"""
ccs = map([:V=>:ᵥ,:E=>:ₑ]) do (x,y)
  vlabel = Symbol.(["PB$y",fill("$(x)₁_$(x)₂", 2)...])
  elabel = Symbol.(["p$(y)₁", "p$(y)₂"])
  lgs    = [i=>Symbol("f$(y)_g$y") for i in [2,3]]
  g = @acset(LG, begin V=3;E=2;vlabel=vlabel; elabel=elabel;
                                 src=1; tgt=2 end)
  Cone(g, Symbol("$(x)₃"), lgs)
end

"""A_B is the coproduct A+B"""
a_bs = map([:V=>:ᵥ,:E=>:ₑ]) do (x,y)
  vlabel = Symbol.(["$(x)₁", "$(x)₂"])
  ap = Symbol("$(x)₁_$(x)₂")
  lgs = [1=>Symbol("i$(y)₁"),2=>Symbol("i$(y)₂")]
  Cone(@acset(LG, begin V=2;vlabel=vlabel end), ap, lgs)
end

"""Make a morphism injective"""
mk_inj(s,t,f) = Cone(@acset(LG, begin V=3;E=2;vlabel=[s,s,t];
          elabel=[f,f];src=[1,2]; tgt=3 end,), s, [1=>add_id(s),2=>add_id(s)])
injs = [mk_inj(x...) for x in
        [(:V₁,:V₃,:fᵥ),(:V₂,:V₃,:gᵥ),(:E₁,:E₃,:fₑ),(:E₂,:E₃,:gₑ)]]

# Equations for the consistency of maps out of the coproduct objects
ve_eqs = vcat(map([:ᵥ,:ₑ]) do y
  c = "f$(y)_g$y"
  (m->(n->Symbol.(n)).(m)).([[["f$y"],["i$(y)₁",c]],[["g$y"],["i$(y)₂",c]]])
end...)

# Equations for the homomorphism constraints
hom_eqs = vcat(map([:f => Symbol("₁"), :g => Symbol("₂")]) do (f,i)
  map([:s,:t]) do st
    (m->Symbol.(m)).([["$(f)ₑ","$(st)₃"],["$st$i","$(f)ᵥ"],])
  end
end...)
eqs = vcat(ve_eqs, hom_eqs)

GraphOverlap = Sketch(schema, cones=[cs...,injs...], cocones=[ccs...,a_bs...], eqs=eqs)

# Example of 3 path equations starting from E₁
# to_graphviz(GraphOverlap.eqs[:E₁]; node_labels=:vlabel, edge_labels=:elabel)


function init_graphs(g1::Graph, g2::Graph,vg3=0,eg3=0)
  @acset GraphOverlap.cset begin V₁=nv(g1); V₂=nv(g2);E₁=ne(g1);E₂=ne(g2);V₃=vg3;E₃=eg3
                      s₁=g1[:src];t₁=g1[:tgt];s₂=g2[:src];t₂=g2[:tgt] end
end

function parse_graph(X::StructACSet, i::Symbol)
  @acset Graph begin V=nparts(X,Symbol("V$i")); E=nparts(X,Symbol("E$i"))
      src=X[Symbol("s$i")];tgt=X[Symbol("t$i")]; end
end

function parse_map(X::StructACSet, i::Symbol)
  fv, fe = [Symbol("$(string(i)=="₁" ? "f" : "g" )$p") for p in [:ᵥ,:ₑ]]
  m = ACSetTransformation(parse_graph(X,i), parse_graph(X,Symbol("₃"));
                      V=X[fv], E=X[fe])
  is_natural(m) || error("unnatural $(dom(m))\n$(codom(m))\n$(components(m))")
  m
end

"""Parse maps and confirm it is jointly surjective"""
function parse_graphoverlap(X::StructACSet)
    f, g = [parse_map(X,Symbol(i)) for i in ["₁","₂"]]
    for P in [:V,:E]
      for v in parts(codom(f), P)
        v ∈ collect(f[P]) ∪ collect(g[P]) || error("$P#$v not in image(f+g)")
      end
    end
    return (codom(f),f,g)
end
parse_result(X::StructACSet,Y::StructACSet{S}) where S = begin
  copy_parts!(Y,X,ob(S)); return Y end
parse_result(X::StructACSet) = parse_result(X,R())

##########################
# ALTERNATE FORMULATIONS #
##########################

# Note, with an implementation of limits in the category of sketches, this
# could probably be expressed as a product of JointSurj and Grph (which would
# then make it easy to mechanically generalize to overlaps btw new structures)

# The below constructions which use colimits

Grph = Sketch(SchGraph);


# Alternate construction of sketch via Graphs, and jointly surjective maps
# (to do - add in equations after schema is constructed)
##############################################################################
r = @relation () begin
  V₁(JSV, Grph1); V₂(JSV, Grph2); V₃(JSV, Grph3)
  E₁(JSE, Grph1); E₂(JSE, Grph2); E₃(JSE, Grph3)
end;
# to_graphviz(r; box_labels=:name, junction_labels=:variable)

res = overlap(r,
  # fill junctions with sketches
  (Grph1 = Grph, Grph2 = Grph, Grph3 = Grph, JSV = JointSurj, JSE = JointSurj),
  # fill circles with overlap criteria
  (V₁=[(:V₁=>(Grph1=:V, JSV=:A))],
   V₂=[(:V₂=>(Grph2=:V, JSV=:B))],
   V₃=[(:V₃=>(Grph3=:V, JSV=:C))],
   E₁=[(:E₁=>(Grph1=:E, JSE=:A))],
   E₂=[(:E₂=>(Grph2=:E, JSE=:B))],
   E₃=[(:E₃=>(Grph3=:E, JSE=:C))])) |> apex;

# Clean up names via direct substitution or regex
res2 = rename(res, Dict(
  r"_Grph"=>"", r"_Grph"=>"", r"_Coprod"=>"","1"=>"₁","2"=>"₂","iA"=>"i₁",
  "iB"=>"i₂","_JS"=>"", "A_B"=>"")) |> codom; # res2.schema |> show_lg
# res2.schema |> show_lg

# Alternate construction of sketch via Graphs, coproducts, monos, and epis.
# This is a more complicated assembly, but it uses simpler building blocks
# (to do - add in equations after schema is constructed)
##########################################################

r = @relation () begin
  V₁(Grph1, MonoV1, CoprodV)
  V₂(Grph2, MonoV2, CoprodV)
  E₁(Grph1, MonoE1, CoprodE)
  E₂(Grph2, MonoE2, CoprodE)
  V₁V₂(CoprodV, SurjV)
  E₁E₂(CoprodE, SurjE)
  V₃(MonoV1, MonoV2, SurjV, Grph3)
  E₃(MonoE1, MonoE2, SurjE, Grph3)
end; # to_graphviz(r, box_labels=:name, junction_labels=:variable)

res = overlap(r,
  # fill junctions with sketches
  (Grph1 = Grph, Grph2 = Grph, Grph3 = Grph,
   CoprodV = Coprod, CoprodE = Coprod,
   SurjV = Surj, SurjE = Surj,
   MonoV1 = Inj, MonoV2 = Inj, MonoE1 = Inj, MonoE2 = Inj),
  # fill circles with overlap criteria
  (V₁=[(:V₁=>(Grph1=:V,MonoV1=:A, CoprodV=:A))],
   V₂=[(:V₂=>(Grph2=:V,MonoV2=:A, CoprodV=:B))],
   E₁=[(:E₁=>(Grph1=:E, MonoE1=:A, CoprodE=:A))],
   E₂=[(:E₂=>(Grph2=:E, MonoE2=:A, CoprodE=:B))],
   V₁V₂=[(:V₁V₂=>(CoprodV=:A_B, SurjV=:A))],
   E₁E₂=[(:E₁E₂=>(CoprodE=:A_B, SurjE=:A))],
   V₃=[(:V₃=>(MonoV1=:B, MonoV2=:B, SurjV=:B, Grph3=:V))],
   E₃=[(:E₃=>(MonoE1=:B, MonoE2=:B, SurjE=:B, Grph3=:E))])) |> apex;

# Clean up names via direct substitution or regex
res2 = rename(res, Dict(
  r"_Grph"=>"", r"_Grph"=>"", r"_Coprod"=>"","1"=>"₁","2"=>"₂","iA"=>"i₁",
  "iB"=>"i₂",r"_Mono"=>"","_Surj"=>"")) |> codom; # res2.schema |> show_lg


end # module

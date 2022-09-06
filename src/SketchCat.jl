module SketchCat
export SketchHom, to_refl

using Catlab, Catlab.CategoricalAlgebra, Catlab.Theories, Catlab.Graphs
using ..Sketches
using ..Sketches: SchLabeledGraph, LabeledGraph
import Catlab.Theories: dom, codom, compose, id

"""
Category of sketches.
- Sketch morphisms
- Sketch (co)-limits


Sketch morphisms are FinFunctors between FinCats (with the additional restriction of being (co)cone-preserving), and their (co)-limits are partially implemented in the Category of Diagrams PR in Catlab. ('partially' because the coequalizer requires automated theorem proving when the domain is not free).
"""

f_obmap(f, s, t,v::Symbol) = begin
  iv = only(incident(s, v, :vlabel))
  println("v $v iv $iv")
  t[f[:V](iv), :vlabel]
end

f_hommap(f, s, t,v::Symbol) = begin
  iv = only(incident(s, v, :elabel))
  println("v $v iv $iv")
  t[f[:E](iv), :elabel]
end

"""Relabel a labeled graph"""
function f_map(f,s,t,X::LabeledGraph)
  X = deepcopy(X)
  println("f_map input $X")
  set_subpart!(X,:vlabel,[f_obmap(f,s,t,v) for v in X[:vlabel]])
  set_subpart!(X,:elabel,[f_hommap(f,s,t,v) for v in X[:elabel]])
  println("f_map result $X")
  return X
end

F = FinDomFunctor(
    Dict([v=>v for v in SchReflexiveGraph.generators[:Ob]]),
    Dict([v=>v for v in SchReflexiveGraph.generators[:Hom]]),
    FinCat(SchReflexiveGraph), FinCat(SchLabeledGraph),
)

ΔF = DeltaMigration(F, LabeledGraph, ReflexiveGraph)
to_refl(x) = x |> deepcopy |> ΔF

@present SchLabeledUnReflGraph <: SchGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end;

@acset_type LabeledUnReflGraph_(
  SchLabeledUnReflGraph, index=[:src,:tgt,:vlabel,:elabel]
) <: AbstractGraph

const LabeledUnReflGraph = LabeledUnReflGraph_{Symbol}
F = FinDomFunctor(
    Dict(vcat([[v=>v for v in SchLabeledUnReflGraph.generators[x]] for x in [:Ob, :AttrType]]...)),
    Dict(vcat([[v=>v for v in SchLabeledUnReflGraph.generators[x]] for x in [:Hom,:Attr]]...)),
    FinCat(SchLabeledUnReflGraph), FinCat(SchLabeledGraph),
)
ΔF2 = DeltaMigration(F, LabeledGraph, LabeledUnReflGraph)
to_grph(x) = x |> deepcopy |> ΔF2

map_cone(f,s, t,c::Cone) = Cone(f_map(f,s,t,c.d), f_obmap(f, s, t, c.apex), Pair{Int,Symbol}[i=>f_hommap(f,s,t,v) for (i,v) in c.legs])

struct SketchHom
  dom::Sketch
  codom::Sketch
  f::ACSetTransformation # graph morphism between the schemas
  function SketchHom(d,c,f) # validate
    s, t = d.schema, c.schema
    dom(f) == to_refl(s) || error("")
    codom(f) == to_refl(t) || error("")
    is_natural(f) || error("")
    for con in d.cones  # check cone is preserved
      map_cone(f,s,t,con) ∈ c.cones || error("Sketch Hom does not preserve cone $con")
    end
    for ccon in d.cocones # check cocone is preserved
      map_cone(f,s,t,ccon) ∈ c.cocones || error("Sketch Hom does not preserve cocone $ccon")
    end
    for (v,veqs) in collect(d.eqs) # check equality is preserved
      !isnothing(homomorphism(to_grph(f_map(f,s,t,veqs)),to_grph(c.eqs[f_obmap(f,s,t,v)]))) || error("eq doesn't hold $(to_grph(f_map(f,s,t,veqs)))\n$(to_grph(c.eqs[f_obmap(f,s,t,v)])))")
    end
    new(d,c,f)
  end
end

@instance ThCategory{Sketch, SketchHom} begin
  dom(f::SketchHom) = f.dom
  codom(f::SketchHom) = f.codom
  id(A::Sketch) = SketchHom(A, A, id(ΔF(A.schema)))
  function compose(f::SketchHom, g::SketchHom; strict::Bool=false)
    !strict || codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SketchHom(dom(f), codom(g), compose(f.f, g.f))
  end
end


# function oapply(composite::UndirectedWiringDiagram,
#   spans::AbstractVector{<:Multispan}; Ob=nothing, Hom=nothing)
# end

# function pushout...

end # module

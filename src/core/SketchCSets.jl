module SketchCSets 
export FinCatCSet, SketchCSet, LabeledFinCatCSet, LabeledSketchCSet, 
       mkFinCatCSet, mkFinCatGraph, mkLabeledFinCatCSet, unlabel, 
       mkLabeledSketchCSet, get_diag_graph, mkFinCatCSetMap,
       mkFinFunctorGraph, mkLabeledFinCatCSetMap
using Catlab, Catlab.CategoricalAlgebra, Catlab.Graphs
using Catlab.CategoricalAlgebra.FinCats: FinCatGraph, FinCatPresentation,
                                         FinCatGraphEq, Path, FreeCatGraph
import Catlab.CategoricalAlgebra.FinCats: equations

using ..LGraphs
using ..LGraphs: SchLGraph
import ..LGraphs: mkFinCatPresentation


equations(::FreeCatGraph) = Pair[]

# C-set schemas
###############

@abstract_acset_type HasCat <: HasGraph

# C-Set for FinCats
@present SchFinCat <: SchReflexiveGraph begin
  # Path equality diagrams
  (Dv, De)::Ob
  root::Hom(V, Dv)
  (dSrc, dTgt)::Hom(De,Dv) # graph data of all diagrams (disjoint union)
  dV::Hom(Dv, V) # Partition union of graphs
  dE::Hom(De, V) # via map into V

  # Homomorphism data
  dvMap::Hom(Dv, V)
  deMap::Hom(De, E)

  # Path eq diagrams are disjoint
  compose(dSrc, dV) == dE
  compose(dTgt, dV) == dE

  # Path eq diagrams are homomorphisms
  compose(deMap, src) == compose(dSrc, dvMap)
  compose(deMap, tgt) == compose(dTgt, dvMap)

  # Root of each diagram is the right vertex
  compose(root, dV) == id(V)
  compose(root, dvMap) == id(V)
end

# Add Cones
@present SchFLS <: SchFinCat begin
  (Cone, Cone_Leg, Cv, Ce)::Ob
  (cSrc, cTgt)::Hom(Ce,Cv) # graph data of all cone bases (disjoint union)
  c_apex::Hom(Cone, V)    # Which object is the cone vertex?
  c_leg::Hom(Cone_Leg, Cone) # Which Cone does this leg belong to?
  c_leg_tgt::Hom(Cone_Leg, Cv)
  c_leg_edge::Hom(Cone_Leg, E)
  cV::Hom(Cv, Cone)    # Partition cone graph
  cE::Hom(Ce, Cone)    # via map into Cone

  # Homorphism data
  cvMap::Hom(Cv, V)
  ceMap::Hom(Ce, E)

  # Cone diagrams are disjoint
  compose(cSrc, cV) == cE
  compose(cTgt, cV) == cE

  # Homomorphism properties
  compose(c_leg_edge, src) == compose(c_leg, c_apex) # EQUATION ON CONE LEGS
  compose(c_leg_edge, tgt) == compose(c_leg_tgt, cvMap) # EQUATION ON CONE LEGS
  compose(ceMap, src) == compose(cSrc, cvMap) # EQUATION ON Ce
  compose(ceMap, tgt) == compose(cTgt, cvMap) # EQUATION ON Ce
end;


# Add cocones
@present SchSketch <: SchFLS begin
  (Cocone, Cocone_Leg, CCv, CCe)::Ob
  (ccSrc, ccTgt)::Hom(CCe,CCv) # graph data of all cone bases (disjoint union)
  cc_apex::Hom(Cocone, V)    # Which object is the cone vertex?
  cc_leg::Hom(Cocone_Leg, Cocone) # Which Cone does this leg belong to?
  cc_leg_tgt::Hom(Cocone_Leg, CCv)
  cc_leg_edge::Hom(Cocone_Leg, E)
  ccV::Hom(CCv, Cocone)    # Partition cone graph
  ccE::Hom(CCe, Cocone)    # via map into Cone

  # Homorphism data
  ccvMap::Hom(CCv, V)
  cceMap::Hom(CCe, E)

  # Cocone diagrams are disjoint
  compose(ccSrc, ccV) == ccE
  compose(ccTgt, ccV) == ccE

  # Homomorphism properties
  compose(cc_leg_edge, src) == compose(cc_leg, cc_apex) # EQUATION ON CONE LEGS
  compose(cc_leg_edge, tgt) == compose(cc_leg_tgt, ccvMap) # EQUATION ON CONE LEGS
  compose(cceMap, src) == compose(ccSrc, ccvMap) # EQUATION ON Ce
  compose(cceMap, tgt) == compose(ccTgt, ccvMap) # EQUATION ON Ce
end;

c_vocab = Symbol.(vcat([setdiff(SchFLS.generators[x], SchFinCat.generators[x])
               for x in [:Ob, :Hom]]...))
cc_vocab = Symbol.(vcat([setdiff(SchSketch.generators[x], SchFLS.generators[x])
                for x in [:Ob, :Hom]]...))

@acset_type FinCatCSet(SchFinCat) <: HasCat
@acset_type FLSCSet(SchFLS) <: HasCat
@acset_type SketchCSet(SchSketch) <: HasCat

# Labeled versions and unlabeling
#################################

@present SchLabeledFinCat <: SchFinCat begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end

@present SchLabeledFLS <: SchFLS begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end

@present SchLabeledSketch <: SchSketch begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end


@acset_type LabeledFinCatCSet_(SchLabeledFinCat) <: HasCat
@acset_type LabeledFLSCSet_(SchLabeledFLS) <: HasCat
@acset_type LabeledSketchCSet_(SchLabeledSketch) <: HasCat

LabeledFinCatCSet, LabeledFLSCSet, LabeledSketchCSet = [x{Symbol} for x in
  [LabeledFinCatCSet_, LabeledFLSCSet_, LabeledSketchCSet_]]

# These should be derivable automatically since names are the same
(unlabelFinCatCSet, unlabelFLSCSet, unlabelSketchCSet, SketchToFinCat,
 LabeledSketchCSettoLGraph) = [
  DeltaMigration(FinFunctor(Dict(vcat([a=>a for a in p.generators[:Ob]],
                                      [a=>a for a in p.generators[:AttrType]])),
                            Dict(vcat([a=>a for a in p.generators[:Hom]],
                                      [a=>a for a in p.generators[:Attr]])),
                            p, p2), cd, d) for (p, p2, d, cd) in
    [(SchFinCat, SchLabeledFinCat, FinCatCSet, LabeledFinCatCSet),
    (SchFLS, SchLabeledFLS, FLSCSet, LabeledFLSCSet),
    (SchSketch, SchLabeledSketch, SketchCSet, LabeledSketchCSet),
    (SchLabeledFinCat, SchLabeledSketch, LabeledFinCatCSet, LabeledSketchCSet),
    (SchLGraph, SchLabeledFinCat, LGraph, LabeledFinCatCSet)
    ]
]

unlabel(x::LabeledFinCatCSet) = unlabelFinCatCSet(x)
unlabel(x::LabeledFLSCSet) = unlabelFLSCSet(x)
unlabel(x::LabeledSketchCSet) = unlabelSketchCSet(x)

function unlabel(x::ACSetTransformation)
  d, cd = unlabel.([f(x) for f in [dom,codom]])
  new_ob = Set(typeof(CC.parts).parameters[2])
  dic = filter(kv->kv[1]∈new_ob, collect(pairs(components)))
  ACSetTransformation(d,cd; dic...)
end


# Conversion between Julia structs and above structures
########################################################

# Conversion to Julia structs
#----------------------------

"""FinCatPresentation -> FinCatGraph"""
function mkFinCatGraph(C::FinCatPresentation)
  hs = Symbol.(hom_generators(C))
  eqs = map(equations(C)) do lr
    l, r = map(lr) do term
      typ = only(typeof(term).parameters)
      d, cd = [findfirst(==(f(term)), ob_generators(C)) for f in [dom, codom]]
      if typ == :compose
        es = [findfirst(==(t.args[1]), hs) for t in term.args]
      elseif typ == :generator
        es = [findfirst(==(term.args[1]), hs)]
      elseif typ == :id
        es = Int[]
      else error("unexpected term $term")
      end
      return Path(es, d, cd)
    end
    return l => r
  end
  return (isempty(eqs) ? FinCat(pres_to_grph(presentation(C)))
                       : FinCat(pres_to_grph(presentation(C)), eqs))
end

  
"""FinCatCSet -> FinCatGraph"""
function mkFinCatGraph(X::FinCatCSet)
  non_refl = setdiff(edges(X), X[:refl])
  eqs = vcat(map(vertices(X)) do v
    g, vs, es = get_diag_graph(X, v)
    root = findfirst(==(X[v,:root]), vs)
    epc = collect(filter(x->x[1][1]==root, enum_paths(g)))
    vcat(map(epc) do (ST,PS)
      sV, tV = [X[vs[st],:dvMap] for st in ST]
      filter(!isempty,PS)
      ps = map(PS) do p 
        if isempty(p) || X[es[p[1]],:deMap] ∈ X[:refl]
          xs = []
        else 
          xs = [findfirst(==(z),non_refl) for z in X[es[p],:deMap]]
        end
        Path(xs, sV, tV)
      end
      psort = sort(ps, by=x->length(edges(x)))
      [b => ps[1] for b in reverse(ps[2:end])]
    end...)
  end...)
  eqs_ = Pair{Path,Path}[eqs...]
  G = Graph()
  copy_parts!(G, X; V=vertices(X), E=setdiff(edges(X),X[:refl]))
  isempty(eqs_) ? FinCat(G) : FinCatGraphEq(G, eqs_)
end

"""Hom(FinCatCSets) -> Hom(FinCatGraph)"""
function mkFinFunctorGraph(f::ACSetTransformation)
  d, cd = mkFinCatGraph.([dom(f), codom(f)])
  dnonrefl = setdiff(edges(dom(f)), dom(f)[:refl])
  cdrefl = Dict([v=>i for (i,v) in enumerate(codom(f)[:refl])])
  cdnonrefl = setdiff(edges(codom(f)), collect(keys(cdrefl)))
  emap = map(collect(f[:E])) do e
    if haskey(cdrefl,e) return Path([], cdrefl[e], cdrefl[e])
    else return findfirst(==(e), cdnonrefl)
    end
  end
  return FinFunctor(collect(f[:V]), emap[dnonrefl], d, cd)
end


"""LabeledFinCatCSet -> FinCatPresentation """
function mkFinCatPresentation(X::LabeledFinCatCSet)
  p = Presentation(FreeSchema)
  vs = [add_generator!(p, Ob(FreeSchema, v)) for v in X[:vlabel]]
  cols = collect(enumerate(zip(X[:elabel], X[:src],X[:tgt])))
  es = map(filter(it->it[1] ∉ X[:refl], cols)) do (_,(e, s, t))
    add_generator!(p, Hom(e, vs[s], vs[t]))
  end
  for lr in equations(mkFinCatGraph(unlabel(X)))
    add_equation!(p, map(lr) do term
      if isempty(edges(term)) || (length(edges(term)) == 1 &&
                                  only(edges(term)) ∈ X[:refl])
        return id(vs[term.src])
      else
        return compose(es[edges(term)])
      end
    end...)
  end
  return FinCat(p)
end


# Conversion to combinatorial data structures
#############################################

"""HasCat -> Graph (ignoring edges which have same src/tgt)"""
function get_diag_graph(X::T, v::Int) where T <: HasCat
  vs, es = [incident(X, v, f) for f in [:dV,:dE]]
  filter!(e->X[e,:dSrc] != X[e,:dTgt], es)
  s, t = [[findfirst(==(x), vs) for x in X[es, f]] for f in [:dSrc, :dTgt]]
  g = @acset Graph begin V=length(vs); E=length(es); src=s; tgt=t end
  return (g, vs, es)
end

"""FinCatPresentation -> LabeledFinCatCSet """
function mkLabeledFinCatCSet(C::FinCatPresentation; eqdiags=nothing)
  mkFinCatCSet(mkFinCatGraph(C); vlabel=Symbol.(ob_generators(C)),
    elabel=Symbol.(hom_generators(C)),eqdiags=eqdiags)
end

"""
     FinCatGraph -> FinCatCSet
*or* FinCatGraph + Labels -> LabeledFinCatCSet
"""
function mkFinCatCSet(C::FinCatGraph;
                      vlabel=nothing, elabel=nothing, eqdiags=nothing)
  G = C.graph
  lab = !isnothing(vlabel)
  X = lab ? LabeledFinCatCSet() : FinCatCSet()
  copy_parts!(X, G)
  if lab
    set_subpart!(X, :vlabel, vlabel)
    set_subpart!(X, :elabel, elabel)
  end
  # add reflexive edges
  set_subpart!(X,:refl,[
    add_part!(X,:E; src=v, tgt=v,
              Dict(lab ? [:elabel=>add_id(vlabel[v])] : [])...)
    for v in vertices(G)])

  # Initialize equations
  if isnothing(eqdiags)
    sch = LGraph()
    copy_parts!(sch, G)
    set_subpart!(sch, :vlabel, Symbol.(string.(vertices(G))))
    set_subpart!(sch, :elabel, Symbol.(string.(edges(G))))
    add_id!(sch)
    eqs = map(equations(C)) do lr
      nonempty_pth = first(filter(x->!isempty(edges(x)), collect(lr)))
      first_e = first(edges(nonempty_pth))
      src_v = Symbol(string(src(G, first_e)))
      l, r = map(lr) do term
        isempty(edges(term)) ? [add_id(src_v)] : Symbol.(string.(edges(term)))
      end
      [l, r]
    end
    eqdiags = eqs_to_diagrams(sch, eqs)
  end
  # Add equations
  for (v_,d) in eqdiags
    non_refl = setdiff(edges(d), d[:refl])
    v = parse(Int, string(v_))
    vs = add_parts!(X, :Dv, nv(d); dV=v)
    set_subpart!(X, v, :root, first(vs))
    set_subpart!(X, vs, :dvMap, [parse(Int, i) for i in string.(d[:vlabel])])
    es = add_parts!(X, :De, ne(d); dE=v, dSrc=vs[d[:src]], dTgt=vs[d[:tgt]])
    elabels = map(string.(d[non_refl,:elabel])) do i
      all(isdigit, i) ? parse(Int, i) : sch[parse(Int, rem_id(i)), :refl]
    end
    set_subpart!(X, es[non_refl], :deMap, elabels)
    for (v_i, rfl) in enumerate(d[:refl])
      set_subpart!(X, es[rfl], :deMap, X[vs[v_i],[:dvMap, :refl]])
    end
  end
  return X
end


"""Hom(FinCatPresentation) -> Hom(LabeledFinCatCSet)"""
function mkLabeledFinCatCSetMap(F::FinFunctor{<:FinCatPresentation})
  d,cd = mkLabeledFinCatCSet.([dom(F),codom(F)])
  labels = Dict{Symbol,Symbol}(merge(
    Dict([k=>Symbol(v) for (k,v) in collect(F.ob_map)]),
    Dict([k=>Symbol(v) for (k,v) in collect(F.hom_map)]),
    Dict([add_id(k) => add_id(Symbol(v)) for (k,v) in collect(F.ob_map)])
  ))
  only(homomorphisms(d,cd; type_components=(Label=FinFunction(labels),)))
end

"""Hom(FinCatGraph) -> Hom(FinCatCSet)"""
function mkFinCatCSetMap(F::FinFunctor{T}) where T<:FinCatGraph
  d,cd = mkFinCatCSet.([dom(F),codom(F)])
  only(homomorphisms(d,cd; initial=(V=F.ob_map, E=F.hom_map)))
end


"""LGraph -> LabeledSketchCSet (no eqs/cones/cocones)"""
function mkLabeledSketchCSet(S::LGraph)
  C = LabeledSketchCSet()
  copy_parts!(C, S; V=vertices(S), E=edges(S))
  set_subpart!(C, :root, [add_part!(C, :Dv; dvMap=i, dV=i) for i in vertices(C)])
  return C
end

"""LabeledSketchCSet -> LGraph (just get the schema)"""
function LabeledSketchCSetToLG(x::LabeledSketchCSet)
  lg = LGraph()
  copy_parts!(lg, SketchToFinCat(x))
  return lg
end



# Misc 
######
# TODO 
# dual(x::LabeledSketchCSet) = DeltaMigration(FinFunctor(
#   Dict(:V=>:V,:E=>:E,),Dict(),
#   SchLabeledSketch,SchLabeledSketch),
#   LabeledSketchCSet,LabeledSketchCSet)

end # module 

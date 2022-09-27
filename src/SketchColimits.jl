module SketchColimits
export FinCatCSet, SketchCSet, mkFinCatCSet, coapply, SketchMorphism,
       mkFinCatGraph, mkFinCatPresentation, mkFinFunctor,
       mkLabeledFinCatCSet, unlabel

using Catlab, Catlab.Present, Catlab.CategoricalAlgebra, Catlab.Theories
using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra.FreeDiagrams: BasicBipartiteFreeDiagram
using Catlab.CategoricalAlgebra.CSets: ACSetColimit
using Catlab.CategoricalAlgebra.FinCats: FinCatGraph, FinCatPresentation,
                                         FinCatGraphEq, FreeCatGraph, Path

import Catlab.Graphs: Graph, SchReflexiveGraph, vertices, HasGraph, nv, ne
import Catlab.CategoricalAlgebra.FinCats: equations, FinCat
import Catlab.CategoricalAlgebra: colimit
import Catlab.Theories: dom, codom, id, compose, ⋅

using ..Sketches
import ..Sketches: Sketch
using ..Sketches: eqs_to_diagrams, LabeledGraph, grph_to_pres,
                  diagram_to_eqs, pres_to_grph, add_id!

using DataStructures

# Misc
######

un_id(x::String) = x[4:end] # assumes add_id(x::Symbol) = "id_$x"
equations(::FreeCatGraph) = Pair[]
function uniqueify(xs::Vector{Symbol})
  cnt = Dict(x=>0 for x in xs) # initialize counts
  map(xs) do x
    cnt[x] += 1
    return cnt[x] == 1 ? x : Symbol("$(x)_$(cnt[x])")
  end
end


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

unlabelFinCatCSet, unlabelFLSCSet, unlabelSketchCSet = [
  DeltaMigration(FinFunctor(Dict([a=>a for a in p.generators[:Ob]]),
                            Dict([a=>a for a in p.generators[:Hom]]),
                            p, p2), cd, d) for (p, p2, d, cd) in
    [(SchFinCat, SchLabeledFinCat, FinCatCSet, LabeledFinCatCSet),
    (SchFLS, SchLabeledFLS, FLSCSet, LabeledFLSCSet),
    (SchSketch, SchLabeledSketch, SketchCSet, LabeledSketchCSet),]
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

"""
Throw away information labeling ob/hom generators
"""
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


# FinCatCSet(C::FinCatPresentation) = C |> mkFinCatGraph |> mkFinCatCSet

"""
Conversion from FinCatGraph to FinCatPresentation, given ob/hom labels
"""
function mkFinCatPresentation(X::FinCatGraph, vlabel::Vector{Symbol}, elabel::Vector{Symbol})
  p, G = Presentation(FreeSchema), X.graph
  vs = [add_generator!(p, Ob(FreeSchema, v)) for v in vlabel]
  es = map(zip(elabel, G[:src],G[:tgt])) do (e, s, t)
    add_generator!(p, Hom(e, vs[s], vs[t]))
  end
  for lr in equations(X)
    add_equation!(p, map(lr) do term
      if isempty(edges(term)) || (length(edges(term)) == 1 &&
                                  elabel[only(edges(term))] ∈ add_id.(vlabel))
        return id(vs[term.src])
      else
        return compose(es[edges(term)])
      end
    end...)
  end
  return FinCat(p)
end

"""Convert labeled FinCat to combinatorial representation"""
function mkLabeledFinCatCSet(C::FinCatPresentation; eqdiags=nothing)
  mkFinCatCSet(mkFinCatGraph(C); vlabel=Symbol.(ob_generators(C)),
    elabel=Symbol.(hom_generators(C)),eqdiags=eqdiags)
end

"""
Convert unlabeled FinCat to combinatorial representation.
If vlabel/elabel provided, then create a labeled combinatorial representation
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
    sch = LabeledGraph()
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
      l => r
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
      all(isdigit, i) ? parse(Int, i) : sch[parse(Int, un_id(i)), :refl]
    end
    set_subpart!(X, es[non_refl], :deMap, elabels)
    for (v_i, rfl) in enumerate(d[:refl])
      set_subpart!(X, es[rfl], :deMap, X[vs[v_i],[:dvMap, :refl]])
    end
  end
  return X
end

"""
Returns a map between the UNLABELED FinCatCSets
We would require the use of LooseACSetTransformations to define morphisms
between the labeled FinCat CSets. We want to take colimits though so this is not
an option.
"""
function mkLabeledFinCatCSetMap(F::FinFunctor{<:FinCatPresentation})
  d,cd = mkLabeledFinCatCSet.([dom(F),codom(F)])

  V = Dict(map(collect(F.ob_map)) do (k,v)
    only(incident(d,Symbol(k),:vlabel)) => only(incident(cd,Symbol(v),:vlabel))
  end)

  E = Dict(map(collect(F.hom_map)) do (k,v)
    ind = findfirst(==(k), d[:vlabel])
    vt = typeof(v).parameters[1]
    if vt == :id
      return cd[findfirst(==(Symbol(v.args[1])), cd[:vlabel]), :refl]
    elseif vt == :generator
      return only(incident(cd, Symbol(v), :elabel))
    else error("unexpected v $v")
    end
  end)
  only(homomorphisms(unlabel(d),unlabel(cd); initial=(V=V, E=E)))
end

function mkFinCatCSetMap(F::FinFunctor{T}) where T<:FinCatGraph
  d,cd = mkFinCatCSet.([dom(F),codom(F)])
  only(homomorphisms(d,cd; initial=(V=F.ob_map, E=F.hom_map)))
end


mkFinCatPresentation(X::LabeledFinCatCSet) = mkFinCatPresentation(mkFinCatGraph(unlabel(X)), X[:vlabel], X[:elabel])

function get_diag_graph(X::T, v::Int) where T <: HasCat
  vs, es = [incident(X, v, f) for f in [:dV,:dE]]
  filter!(e->X[e,:dSrc] != X[e,:dTgt], es)
  s, t = [[findfirst(==(x), vs) for x in X[es, f]] for f in [:dSrc, :dTgt]]
  return @acset Graph begin V=length(vs); E=length(es); src=s; tgt=t end
end

function mkFinCatGraph(X::FinCatCSet)
  non_refl = setdiff(edges(X), X[:refl])
  eqs = vcat(map(vertices(X)) do v
    vs, es = [incident(X, v, f) for f in [:dV,:dE]]
    g = get_diag_graph(X, v)
    epc = collect(filter(x->x[1][1]==1, enum_paths(g)))
    vcat(map(epc) do (ST,PS)
      sV, tV = [X[vs[st],:dvMap] for st in ST]
      ps = sort([Path(X[p[1],:deMap] ∈ X[:refl] ? [] : [
                        findfirst(==(z),non_refl) for z in X[es[p],:deMap]],
                      sV, tV)
            for p in filter(!isempty,PS)], by=x->length(edges(x)))
      [b => ps[1] for b in reverse(ps[2:end])]
    end...)
  end...)
  eqs_ = Pair{Path,Path}[eqs...]
  G = Graph()
  copy_parts!(G, X; V=vertices(X), E=setdiff(edges(X),X[:refl]))
  isempty(eqs_) ? FinCat(G) : FinCatGraphEq(G, eqs_)
end


"""
Convert a map between FinCatCSets into a FinFunctor between FinCatGraphs
"""
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

"""Convert a map between FinCatGraphs into a FinFunctor between FinCatPres"""
function mkFinFunctorPres(f::FinFunctor{<:FinCatGraph},
                          dlabel::Pair{Vector{Symbol},Vector{Symbol}},
                          cdlabel::Pair{Vector{Symbol},Vector{Symbol}})
  v1, e1 = uniqueify.(dlabel|>collect)
  v2, e2 = uniqueify.(cdlabel|>collect)
  d = mkFinCatPresentation(dom(f), v1, e1)
  cd = mkFinCatPresentation(codom(f), v2, e2)
  vmap = Dict([ob_generators(d)[k] => ob_generators(cd)[v]
               for (k,v) in enumerate(f.ob_map)])
  # This will need to be fixed to deal with maps to id morphisms
  emap = Dict([hom_generators(d)[k] => hom_generators(cd)[only(edges(v))]
               for (k,v) in enumerate(f.hom_map)])
  return FinFunctor(vmap, emap, d, cd)
end


function LabeledSketchCSet(S::Sketch)
  C = LabeledSketchCSet()
  vdict, edict = [Dict([k=>i for (i,k) in enumerate(f(S))])
                  for f in [vlabel, elabel]]
  for (v, reflv) in enumerate(S.schema[[:refl,:elabel]])
    edict[reflv] = length(edict)+1
  end
  vdict_, edict_ = [Dict([k=>Symbol(string(v)) for (k,v) in collect(d)])
                    for d in [vdict, edict]]
  S_eqs = Dict(map(collect(S.eqs)) do (v, d)
    new_d = deepcopy(d)
    set_subpart!(new_d, :vlabel, [vdict_[x] for x in d[:vlabel]])
    set_subpart!(new_d, :elabel, [edict_[x] for x in d[:elabel]])
    vdict[v] => new_d
  end)
  Sch = mkLabeledFinCatCSet(FinCat(grph_to_pres(S.schema)); eqdiags=S_eqs)
  copy_parts!(C, Sch)

  # Add cones
  for ((cone, cone_leg,cv, ce, csrc, ctgt, capex, cleg, clegtgt, clegedge, c_v,
       c_e, cvmap, cemap), cs) in zip([c_vocab, cc_vocab], [S.cones, S.cocones])
    for c in cs
      c_id = add_part!(C, cone; Dict([capex=>vdict[c.apex]])...)
      vs = add_parts!(C, cv, nv(c.d); Dict([c_v=>c_id,
                      cvmap=>[vdict[x] for x in c.d[:vlabel]]])...)
      nonrefl = setdiff(edges(c.d), c.d[:refl])
      es = add_parts!(C, ce, ne(c.d)-nv(c.d); Dict([c_e=>c_id,
                      csrc=>vs[c.d[nonrefl, :src]], ctgt=>vs[c.d[nonrefl, :tgt]],
                      cemap=>[edict[x] for x in c.d[nonrefl, :elabel]]])...)
      for (leg_i, leg_val) in c.legs
        add_part!(C, cone_leg; Dict([cleg=>c_id, clegtgt=>vs[leg_i],
                  clegedge=>edict[leg_val]])...)
      end
    end
  end
  return C
end

function Sketch(S::SketchCSet, vs::AbstractVector{Symbol}, es::AbstractVector{Symbol})
  # Get schema
  schema = LabeledGraph()
  copy_parts!(schema, S)
  set_subpart!(schema, :vlabel, vs)
  set_subpart!(schema, setdiff(parts(schema,:E), schema[:refl]), :elabel, es)
  set_subpart!(schema, schema[:refl], :elabel, add_id.(vs))
  es = vcat(es|>collect, add_id.(vs|>collect))
  # Get eqs
  eqs = vcat(map(vertices(S)) do v
    d = LabeledGraph()
    cvs, ces = [incident(S, v, f) for f in [:dV, :dE]]
    filter!(e -> S[e,:deMap] ∉ S[:refl], ces)
    add_parts!(d, :V, length(cvs); vlabel=vs[S[cvs,:dvMap]])
    add_parts!(d, :E, length(ces); elabel=es[S[ces,:deMap]],
              src=[findfirst(==(x),cvs) for x in S[ces,:dSrc]],
              tgt=[findfirst(==(x),cvs) for x in S[ces,:dTgt]])
    diagram_to_eqs(d)
  end...)

  # Get (co)cones
  cones, cocones = map([c_vocab, cc_vocab]) do (
        cone, _, _, _, csrc, ctgt, capex, cleg, clegtgt,
        clegedge, c_v,c_e, cvmap, cemap)
    map(parts(S,cone)) do c_id
      cvs, ces = [incident(S,c_id,f) for f in [c_v,c_e]]
      cd = LabeledGraph()
      for cvert in cvs add_part!(cd, :V, vlabel=vs[S[cvert, cvmap]]) end
      for cedge in ces
        add_part!(cd, :E, elabel=es[S[cedge, cemap]],
                  src=findfirst(==(S[cedge,csrc]), cvs),
                  tgt=findfirst(==(S[cedge,ctgt]), cvs))
      end
      lgs = Vector{Pair{Int,Symbol}}(map(incident(S, c_id, cleg)) do l_id
        findfirst(==(S[l_id, clegtgt]), cvs) => es[S[l_id, clegedge]]
      end)
      Cone(cd, vs[S[c_id, capex]], lgs)
    end
  end
  Sketch(schema; cones=cones, cocones=cocones, eqs=eqs)
end

# Colimits of FinCats
#####################
"""
Colimit of labeled FinCats
"""
function colimit(::Type{Tuple{C,Hom}}, diagram) where {
      T, C<:FinCat, Hom <: FinFunctor{<:FinCatPresentation}}
  if diagram isa Multispan
    new_diagram = Multispan(mkLabeledFinCatCSetMap.(legs(diagram)))
    d_legs = legs(diagram)
    c_lim = colimit(new_diagram)
  else
    new_diagram = BasicBipartiteFreeDiagram{FinCatCSet, ACSetTransformation}()
    for (v,o) in [:V₁=>:ob₁, :V₂=>:ob₂]
      add_parts!(new_diagram, v, nparts(diagram, v); Dict(o=>unlabel.(mkLabeledFinCatCSet.(diagram[o])))...)
    end
    for (es,et,eh) in zip([diagram[x] for x in [:src,:tgt,:hom]]...)
      add_part!(new_diagram, :E; src=es, tgt=et, hom=mkLabeledFinCatCSetMap(eh))
    end
    d_legs = diagram[:hom]
    c_lim = colimit(typeof((FinCatCSet(),id(FinCatCSet()))), new_diagram)
  end

  unlabeled_res = mkFinFunctorGraph.(c_lim.cocone)
  new_vlabel = map(ob_generators(codom(first(unlabeled_res)))) do i
    for (spleg, cspleg) in zip(d_legs, unlabeled_res)
      preim = findfirst(==(i), cspleg.ob_map)
      if !isnothing(preim)
        ob_name = Symbol(ob_generators(codom(spleg))[preim])
        for (k,v) in collect(spleg.ob_map)
          if Symbol(v) == ob_name return k end
        end
        return ob_name
      end
    end
    error("colimits should be jointly surjective $i")
  end
  new_elabel = map(hom_generators(codom(first(unlabeled_res)))) do i
    for (spleg, cspleg) in zip(d_legs, unlabeled_res)
      preim = findall(p->length(p)==1 && only(p)==i, edges.(cspleg.hom_map))
      if !isempty(preim)
        length(preim) == 1 || error("expected only 1 $preim")
        hom_name = Symbol(hom_generators(codom(spleg))[only(preim)])
        for (k,v) in collect(spleg.hom_map)
          if Symbol(v) == hom_name return k end
        end
        return hom_name
      end
    end
    error("colimits should be jointly surjective $i")
  end
  old_labels = [
    Symbol.(ob_generators(leg)) => vcat(
      Symbol.(hom_generators(leg)), add_id.(Symbol.(ob_generators(leg))))
    for leg in codom.(d_legs)]

  return Multicospan([mkFinFunctorPres(ures,ol,new_vlabel=>new_elabel)
                      for (ol, ures) in zip(old_labels, unlabeled_res)])
end

"""
Colimit of unlabeled FinCatGraphs
"""
function colimit(::Type{Tuple{C,Hom}}, diagram) where {
      T, C<:FinCat, Hom <: FinFunctor{<:FinCatGraph}}
  if diagram isa Multispan
    new_diagram = Multispan(mkFinCatCSetMap.(legs(diagram)))
    return Multicospan(mkFinFunctorGraph.(colimit(new_diagram).cocone))
  else
    new_diagram = BasicBipartiteFreeDiagram{FinCatCSet, ACSetTransformation}()
    for (v,o) in [:V₁=>:ob₁, :V₂=>:ob₂]
      add_parts!(new_diagram, v, nparts(diagram, v); Dict(o=>mkFinCatCSet.(diagram[o]))...)
    end
    for (es,et,eh) in zip([diagram[x] for x in [:src,:tgt,:hom]]...)
      add_part!(new_diagram, :E; src=es, tgt=et, hom=mkFinCatCSetMap(eh))
    end
    return Multicospan(mkFinFunctorGraph.(colimit(
            typeof((FinCatCSet(),id(FinCatCSet()))), new_diagram).cocone))
  end
end

struct CompositeSketch
  uwd::UndirectedWiringDiagram
  args::Vector{Sketch}
end

"""Use UWD to organize a colimit"""
function coapply(composite::UndirectedWiringDiagram,
  spans::AbstractVector{<:Multispan}; Ob=nothing, Hom=nothing)
  @assert nboxes(composite) == length(spans)
  # FIXME: This manual type inference is hacky and bad. The right solution is to
  # extend `Multi(co)span` with type parameters that allow abstract types.
  if isnothing(Ob); Ob = typejoin(mapreduce(typeof∘apex, typejoin, spans),
                                  mapreduce(eltype∘feet, typejoin, spans)) end
  if isnothing(Hom); Hom = mapreduce(eltype∘legs, typejoin, spans) end
  junction_feet = Vector{Ob}(undef, njunctions(composite))

  # Create bipartite free diagram whose vertices of types 1 and 2 are the UWD's
  # boxes and junctions, respectively.
  diagram = BipartiteFreeDiagram{Ob,Hom}()
  add_vertices₁!(diagram, nboxes(composite), ob₁=map(apex, spans))
  add_vertices₂!(diagram, njunctions(composite))
  for (b, span) in zip(boxes(composite), spans)
    for (p, leg) in zip(ports(composite, b), legs(span))
      j = junction(composite, p)
      add_edge!(diagram, b, j, hom=leg)
      foot = codom(leg)
      if isassigned(junction_feet, j)
        foot′ = junction_feet[j]
        foot == foot′ || error("Feet of spans are not equal: $foot != $foot′")
      else
        junction_feet[j] = foot
      end
    end
  end
  all(isassigned(junction_feet, j) for j in junctions(composite)) ||
    error("Limits with isolated junctions are not supported")
  diagram[:ob₂] = junction_feet
  # The composite multispan is given by the limit of this diagram.
  lim = colimit(diagram)
  outer_legs = map(junction(composite, outer=true)) do j
    e = first(incident(diagram, j, :tgt))
    legs(lim)[src(diagram, e)]
  end
  Multicospan(apex(lim), outer_legs)
end

# Sketch morphisms
##################
function mkFinCatPresentation(S::LabeledGraph)
  p = Presentation(FreeSchema)
  vs = Dict([v=>add_generator!(p, Ob(FreeSchema, v)) for v in vlabel(S)])
  for (e,s,t) in elabel(S,true)
    add_generator!(p, Hom(e, vs[s],vs[t]))
  end
  return FinCat(p)
end

mkFinCatPresentation(S::Sketch) = mkFinCatPresentation(S.schema)
mkFinCatGraph(S::Sketch) = mkFinCatGraph(S.Schema)
struct SketchMorphism
  dom::Sketch
  codom::Sketch
  f::FinFunctor
  function SketchMorphism(d,c,fob,fhom=nothing)
    # (co)cones/eqs check?
    f = FinFunctor(fob,fhom,mkFinCatPresentation.([d,c])...)
    is_functorial(f) || error("f $f")
    return new(d,c,f)
  end
end

function toLabeledSketchCSetHom(F::SketchMorphism)
  c,cd = LabeledSketchCSet.([dom(F), codom(F)])
  vmap, emap = [Dict{Int,Int}() for _ in 1:2]
  for (c_ob, cd_ob) in collect(F.f.ob_map)
    ind, val = [findfirst(==(Symbol(o)), vlabel(f(F)))
                for (o,f) in zip([c_ob, cd_ob],[dom,codom])]
    vmap[ind] = val
  end
  for (c_hom, cd_hom) in collect(F.f.hom_map)
    ind, val = [findfirst(==(Symbol(o)), elabel(f(F)))
                for (o,f) in zip([c_hom, cd_hom],[dom,codom])]
    if isnothing(val) # it's an ID morphism
      typeof(cd_hom).parameters[1] == :id || error("Only codom vals that are generators or id are allowed")
      valob = findfirst(==(Symbol(cd_hom.args[1])), vlabel(codom(F)))
      val = cd[valob, :refl]
    end
    emap[ind] = val
  end
  return only(homomorphisms(c,cd; type_components=(Label=merge(vmap,emap),)))
end

function toSketchHom(f::ACSetTransformation,
                      dlabel::Pair{Vector{Symbol},Vector{Symbol}},
                      cdlabel::Pair{Vector{Symbol},Vector{Symbol}})
  v1, e1 = uniqueify.(dlabel|>collect)
  v2, e2 = uniqueify.(cdlabel|>collect)

  ds = Sketch(dom(f), v1, e1)
  cds = Sketch(codom(f), v2, e2)
  dnonrefl = setdiff(edges(dom(f)), dom(f)[:refl])
  cdrefl = Dict([v=>i for (i,v) in enumerate(codom(f)[:refl])])
  cdnonrefl = setdiff(edges(codom(f)), collect(keys(cdrefl)))
  emap = map(collect(f[:E])) do e
    if haskey(cdrefl,e) return Path([], cdrefl[e], cdrefl[e])
    else return findfirst(==(e), cdnonrefl)
    end
  end
  fob = collect(f[:V])
  fhom = emap[dnonrefl]
  return SketchMorphism(ds,cds, fob, hom)
end

@instance ThCategory{Sketch, SketchMorphism} begin
  dom(f::SketchMorphism) = f.dom
  codom(f::SketchMorphism) = f.codom
  id(A::Sketch) = SketchMorphism(A, A, id(FinCat(dom(A))))
  function compose(f::SketchMorphism, g::SketchMorphism; strict::Bool=false)
    !strict || codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SketchMorphism(dom(f), codom(g), compose(f.f, g.f))
  end
end

function colimit(::Type{Tuple{Sketch,SketchMorphism}}, diagram)
  if diagram isa Multispan
    error("here")
    new_diagram = Multispan(mkFinCatCSet.(legs(diagram)))
  else
    new_diagram = BasicBipartiteFreeDiagram{SketchCSet, ACSetTransformation}()
    for (v,o) in [:V₁=>:ob₁, :V₂=>:ob₂]
      add_parts!(new_diagram, v, nparts(diagram, v); Dict(o=>LabeledSketchCSet.(diagram[o]))...)
    end
    for (es,et,eh) in zip([diagram[x] for x in [:src,:tgt,:hom]]...)
      add_part!(new_diagram, :E; src=es, tgt=et, hom=toLabeledSketchCSetHom(eh))
    end
    d_legs = diagram[:hom]
    c_lim = colimit(typeof((SketchCSet(),id(SketchCSet()))), new_diagram)
    # return c_lim # Multicospan([toSketchHom(x,c,d) for x in )
  end
  unlabeled_res = c_lim.cocone
  cc = codom(first(unlabeled_res)) # colimit apex
  new_vlabel = map(parts(cc, :V)) do i
    symb_dict = DefaultDict{Symbol,Vector{Int}}(()->Int[])
    for (legi, (spleg, cspleg)) in enumerate(zip(d_legs, unlabeled_res))
      for (vsymb, vtarg) in zip(vlabel(codom(spleg)), cspleg[:V]|>collect)
        if vtarg == i
          push!(symb_dict[vsymb], legi)
        end
      end
    end
    return Symbol(join(map(sort(collect(symb_dict))) do (s, leg_is)
            if length(leg_is) == length(unlabeled_res)
              return s
            else
              return Symbol("$(s)_"*join(Symbol.(string.(leg_is)),"_"))
            end
          end,"__"))
  end
  new_elabel = map(filter(i->i∉cc[:refl], parts(cc, :E))) do i
    symb_dict = DefaultDict{Symbol,Vector{Int}}(()->Int[])
    for (legi, (spleg, cspleg)) in enumerate(zip(d_legs, unlabeled_res))
      println("dom cspleg refl $(dom(cspleg)[:refl])", )
      for (vsymb, vtarg) in zip(elabel(codom(spleg)), cspleg[:E]|>collect)
        if vtarg == i
          push!(symb_dict[vsymb], legi)
        end
      end
    end
    return Symbol(join(map(sort(collect(symb_dict))) do (s, leg_is)
      if length(leg_is) == length(unlabeled_res)
        return s
      else
        return Symbol("$(s)_"*join(Symbol.(string.(leg_is)),"_"))
      end
    end,"__"))
  end
  # warning this assumes that the inputs have all non-id homs first...
  old_labels = [
    Symbol.(vlabel(leg)) => vcat(
      Symbol.(elabel(leg)))# , add_id.(Symbol.(vlabel(leg))))
    for leg in codom.(d_legs)]
  println("new_vlabel $new_vlabel\nnew_elabel $new_elabel \nold_labels $(old_labels)")
  return Multicospan([toSketchHom(ures,ol,new_vlabel=>new_elabel)
                      for (ol, ures) in zip(old_labels, unlabeled_res)])
  end



end # module
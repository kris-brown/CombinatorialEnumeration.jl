module SketchColimits
export coapply,
       rename, overlap, suffix

using Catlab, Catlab.Present, Catlab.CategoricalAlgebra, Catlab.Theories
using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra.FreeDiagrams: BasicBipartiteFreeDiagram
using Catlab.CategoricalAlgebra.CSets: ACSetColimit, unpack_diagram, pack_components, type_components
using Catlab.CategoricalAlgebra.FinCats: FinCatPresentation, FreeCatGraph, Path

import Catlab.Graphs: Graph, SchReflexiveGraph, vertices, HasGraph, nv, ne
import Catlab.CategoricalAlgebra.FinCats: equations, FinCat
using Catlab.CategoricalAlgebra.FinSets: IdentityFunction, TypeSet
import Catlab.CategoricalAlgebra: colimit
import Catlab.Theories: dom, codom, id, attr, compose, ⋅ # adom, acodom_nums, acodom, 

using ..SketchCSets, ..Sketches, ..LGraphs, ..SketchCat
import ..Sketches: Sketch
using ..Sketches: eqs_to_diagrams, grph_to_pres, diagram_to_eqs

using DataStructures


# Colimits of FinCats
#####################

"""
"""
function colimit(::Type{Tuple{C,Hom}}, diagram; type_components=nothing) where {
                  C<:FinCat, Hom <: FinFunctor{<:FinCat}}
  if Hom <: FinFunctor{<:FinCatGraph}
    CType,CHType,mkCSet, mkCSetMap,mkFunctor, tcarg = FinCatCSet,TightACSetTransformation,mkFinCatCSet,mkFinCatCSetMap, mkFinFunctorGraph, Dict()
  elseif Hom <: FinFunctor{<:FinCatPresentation}
    CType,CHType,mkCSet,mkCSetMap,mkFunctor, tcarg = LabeledFinCatCSet,LooseACSetTransformation,mkLabeledFinCatCSet,mkLabeledFinCatCSetMap, mkFinFunctorPres, Dict(:type_components=>type_components)
  else error("Unexpected kind of FinCat $(first(Hom.parameters))")
  end
  if diagram isa Multispan
    new_diagram = Multispan(mkCSetMap.(legs(diagram)))
    return Multicospan(mkFunctor.(colimit(new_diagram; tcarg...).cocone))
  else
    new_diagram = BasicBipartiteFreeDiagram{CType, CHType}()
    for (v,o) in [:V₁=>:ob₁, :V₂=>:ob₂]
      add_parts!(new_diagram, v, nparts(diagram, v); Dict(o=>mkCSet.(diagram[o]))...)
    end
    for (es,et,eh) in zip([diagram[x] for x in [:src,:tgt,:hom]]...)
      add_part!(new_diagram, :E; src=es, tgt=et, hom=mkCSetMap(eh))
    end
    ty = typeof((new_diagram[1,:ob₁], new_diagram[1,:hom]))
    return Multicospan(mkFunctor.(colimit(ty, new_diagram; tcarg...).cocone))
  end
end

struct CompositeSketch
  uwd::UndirectedWiringDiagram
  args::Vector{Sketch}
end

"""Use UWD to organize a colimit"""
function coapply(composite::UndirectedWiringDiagram,
                 spans::AbstractVector{<:Multispan};
                 Ob=nothing, Hom=nothing, type_components=nothing)
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
  lim = colimit(diagram; type_components=type_components)
  outer_legs = map(junction(composite, outer=true)) do j
    legs(lim)[j]
  end
  Multicospan(apex(lim), outer_legs)
end

# Renaming
##########
function rename(S::FinCatPresentation, d::Dict{Symbol,Symbol})
  comb = rename(mkLabeledFinCatCSet(S), d)
  mkFinFunctorPres(comb)
end

"""
Either match a symbol exactly (and provide exact replacement) or give a list
of regex replacements to perform on every symbol.
"""
function rename(S::LabeledFinCatCSet, d::AbstractDict)
  T = deepcopy(S)
  for lab in [:vlabel, :elabel]
    old_lab = deepcopy(S[lab])
    set_subpart!(T, lab, [rename(x,d) for x in S[lab]])
    for (oldx,x) in zip(old_lab,T[lab]) d[oldx] = x end
  end
  comps = Dict(k=>parts(S,k) for k in typeof(S.parts).parameters[2])
  return LooseACSetTransformation(comps, Dict(:Label=>FinFunction(d)), S, T)
end

rename(S::Sketch, d::NamedTuple) = rename(S,Dict(collect(pairs(d))))

function rename(S::Sketch, d::AbstractDict)
  comb = rename(mkLabeledSketchCSet(S), d)
  mkSketchMorphism(comb)
end

rename(x::Symbol,d::Dict{Symbol,Symbol}) = get(d,x,x)
function rename(x::Symbol,d::AbstractDict)
  res = string(x)
  for (k,v) in collect(d) res = replace(res,k=>v) end
  return Symbol(res)
end

function rename(S::LabeledSketchCSet, d::AbstractDict)
  T = deepcopy(S)
  ff = Dict{Symbol,Symbol}()
  for lab in [:vlabel, :elabel]
    old_lab = deepcopy(S[lab])
    set_subpart!(T, lab, [rename(x,d) for x in S[lab]])
    for (oldx,x) in zip(old_lab,T[lab]) ff[oldx] = x end
  end
  comps = Dict(k=>parts(S,k) for k in typeof(S.parts).parameters[2])
  return LooseACSetTransformation(comps, Dict(:Label=>FinFunction(ff)), S, T)
end

suffix(x::Symbol, k::Symbol) = Symbol("$(x)_$k")
function suffix(S::Sketch, k::Symbol)
  SC = mkLabeledSketchCSet(S)
  rename(SC, Dict(vcat([[v=>suffix(v, k) for v in SC[x]] for x in [:vlabel, :elabel]]...)))
end
unsuffix(x::Symbol, k::Symbol) = Symbol(string(x)[1:end-(length(string(k))+1)])


function colimit(::Type{Tuple{Sketch,SketchMorphism}}, diagram; type_components=nothing)
  if diagram isa Multispan
    error("here")
    new_diagram = Multispan(mkFinCatCSet.(legs(diagram)))
  else
    new_diagram = BasicBipartiteFreeDiagram{LabeledSketchCSet, ACSetTransformation}()
    for (v,o) in [:V₁=>:ob₁, :V₂=>:ob₂]
      add_parts!(new_diagram, v, nparts(diagram, v); Dict(o=>mkLabeledSketchCSet.(diagram[o]))...)
    end
    for (es,et,eh) in zip([diagram[x] for x in [:src,:tgt,:hom]]...)
      add_part!(new_diagram, :E; src=es, tgt=et, hom=toLabeledSketchCSetHom(eh))
    end
    d_legs = diagram[:hom]
    ty = typeof((LabeledSketchCSet(),new_diagram[1,:hom]))
    return Multicospan(mkSketchMorphism.(colimit(ty, new_diagram; type_components=type_components)))
  end
end

# Sugar for defining overlap Multispans
#######################################

"""
A list of sketches can be merged along vertices or edges in the graphs
presenting their schemas. Overlaps are given by a list of Vector{Symbol},
each element of which specifies an overlapping vertex or edge by name.
"""
function overlap(Ss::Vector{Sketch}, ovs::Vector{Vector{Symbol}})
  apx = LGraph()
  n = length(Ss)
  all(x->length(x)==n, ovs) || error("One of the overlaps has wrong #")
  type_components = [Dict{Symbol,Symbol}() for _ in 1:n]
  for (i, ov) in enumerate(ovs)
    if first(ov) ∈ vlabel(first(Ss)) # figure if a morphism or an object
      sym = Symbol("ob$i")
      v = add_vertex!(apx, vlabel=sym)
      set_subpart!(apx, apx[v,:refl], :elabel, add_id(sym))
      for (o,tc,_) in zip(ov, type_components, Ss)
        tc[add_id(sym)] = add_id(o)
      end
    else
      sym, o1,o2 = Symbol.(["hom$i","src$i", "tgt$i"])
      for (o,tc,S) in zip(ov, type_components, Ss)
        tc[o1] = src(S,o)
        tc[o2] = tgt(S,o)
      end

    end
    for (o,tc) in zip(ov, type_components) tc[sym] = o end
  end
  apx = mkLabeledSketchCSet(apx)
  return Multispan([
    mkSketchMorphism(only(homomorphisms(apx, mkLabeledSketchCSet(S);
                       type_components=(Label=FinFunction(tc),))))
    for (S,tc) in zip(Ss,type_components)])

end

function overlap(uwd::UndirectedWiringDiagram,X::NamedTuple{Snames},Y::NamedTuple{Jnames}) where {Snames,Jnames}
  sort(unique(uwd[:name])) == sort(collect(Jnames)) || error(
    "Keys don't match box names $(uwd[:name])")
  sort(unique(uwd[:variable])) == sort(collect(Snames)) || error(
    "Keys don't match junction names $(uwd[:variable])!=$Snames")
  Xd = Dict(k=>suffix(v,k) for (k,v) in pairs(X))
  Yd = Dict(map(collect(pairs(Y))) do (k,v1)
    k => map(v1) do (k2, v2)
      k2 => Dict([k3=>suffix(v3,k3) for (k3,v3) in pairs(v2)])
    end
  end)
  tcs = Dict{Symbol,Symbol}()
  overs = map(enumerate(uwd[:name])) do (b, v)
    newsymb_comps = Yd[v]
    snames = uwd[incident(uwd,b,:box),[:junction,:variable]]
    sketches = [Sketch(codom(Xd[j])) for j in snames]
    over = [[comp[j] for j in snames] for comp in last.(newsymb_comps)]
    for (k,vs) in collect(newsymb_comps)
      for (_,v) in collect(vs)
        tcs[v] = k; tcs[add_id(v)] = add_id(k) # quick hack for looking up the actual id name
      end
    end
    overlap(sketches, over)
  end
  for sname in Snames
    _, suffixS = X[sname], codom(Xd[sname])
    for lab in [:vlabel, :elabel]
      for sufflab in suffixS[lab]
        if !haskey(tcs, sufflab)
          tcs[sufflab] = sufflab
        end
      end
    end
  end

  return coapply(uwd, overs; type_components=[(Label=FinFunction(tcs),) for _ in parts(uwd,:Port)])
end



end # module

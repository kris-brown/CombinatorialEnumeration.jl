using Catlab.Present
using Catlab.Graphs
using JSON
using AutoHashEquals

using Catlab.Graphs.BasicGraphs: TheoryGraph
using Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.CSetDataStructures: struct_acset
include(joinpath(@__DIR__, "../../CSetAutomorphisms.jl/src/CSetAutomorphisms.jl"))

"""Edges and vertices labeled by symbols"""
@present TheoryLabeledGraph <: TheoryGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end;

@acset_type LabeledGraph_(TheoryLabeledGraph, index=[:src,:tgt])
const LabeledGraph = LabeledGraph_{Symbol}

"""Forget about the labels"""
function to_graph(lg::LabeledGraph_)::Graph
  G = Graph(nparts(lg, :V))
  add_edges!(G, lg[:src], lg[:tgt])
  return G
end

@auto_hash_equals struct Cone
  d::LabeledGraph
  apex::Symbol
  legs::Vector{Pair{Int, Symbol}}
end

@auto_hash_equals struct FLS
  name::Symbol
  schema::LabeledGraph
  cones::Vector{Cone}
  eqs::Vector{Pair{Vector{Symbol}, Vector{Symbol}}}
end

cone_to_dict(c::Cone) = Dict([
  "d"=>generate_json_acset(c.d),
  "apex"=>string(c.apex),"legs"=>c.legs])
dict_to_cone(d::Dict)::Cone = Cone(
  parse_json_acset(LabeledGraph,d["d"]), Symbol(d["apex"]),
  [parse(Int, k)=>Symbol(v) for (k, v) in map(only, d["legs"])])
"""TO DO: add cone and eq info to the hash...prob requires CSet for FLS"""
Base.hash(F::FLS) = canonical_hash(to_graph(F.schema))
to_json(F::FLS) = JSON.json(Dict([
  :name=>F.name, :schema=>generate_json_acset(F.schema),
  :cones => [cone_to_dict(c) for c in F.cones],
  :eqs => [Dict([:p=>p,:q=>q]) for (p,q) in F.eqs]]))
function fls_from_json(s::String)::FLS
  p = JSON.parse(s)
  return FLS(Symbol(p["name"]), parse_json_acset(LabeledGraph, p["schema"]), [dict_to_cone(d) for d in p["cones"]], [map(Symbol, pq["p"])=>map(Symbol, pq["q"]) for pq in p["eqs"]])
end

add_srctgt(x::Symbol) = Symbol("src_$(x)") => Symbol("tgt_$(x)")

function grph_to_crel(name::Symbol,fls::LabeledGraph)::StructACSet
  pres = Presentation(FreeSchema)
  nv = length(fls[:vlabel])
  alledge = vcat([add_srctgt(e) for e in fls[:elabel]]...)
  xobs = [Ob(FreeSchema, s) for s in [fls[:vlabel]...,fls[:elabel]...]]
  for x in xobs
    add_generator!(pres, x)
  end
  for (i,(e, src, tgt)) in enumerate(zip(fls[:elabel],fls[:src], fls[:tgt]))
    s, t = add_srctgt(e)
    add_generator!(pres, Hom(s, xobs[nv+i], xobs[src]))
    add_generator!(pres, Hom(t, xobs[nv+i], xobs[tgt]))
  end
  name_ = Symbol("rel_$name")
  expr = struct_acset(name_, StructACSet, pres, index=alledge)
  eval(expr)
  return Base.invokelatest(eval(name_))
end

function grph_to_cset(name::Symbol, fls::LabeledGraph)::StructACSet
  pres = Presentation(FreeSchema)
  xobs = [Ob(FreeSchema, s) for s in fls[:vlabel]]
  for x in xobs
    add_generator!(pres, x)
  end
  for (e, src, tgt) in zip(fls[:elabel], fls[:src], fls[:tgt])
    add_generator!(pres, Hom(e, xobs[src], xobs[tgt]))
  end
  expr = struct_acset(name, StructACSet, pres, index=fls[:elabel])
  eval(expr)
  return Base.invokelatest(eval(name))
end

function crel_to_cset(F::FLS,J::StructACSet)
  res = grph_to_cset(F.name, F.schema)
  for o in F.schema[:vlabel]
    add_parts!(res, o, nparts(J, o))
  end
  for m in F.schema[:elabel]
    msrc, mtgt = add_srctgt(m)
    md, mcd = zip(sort(collect(zip(J[msrc], J[mtgt])))...)
    collect(md) == collect(1:length(md)) || error("nonfunctional $J")
    set_subpart!(res, m, mcd)
    0 ∉ res[m] || error("$J\n$m\n$res\n$md\n$mcd")
  end
  return res
end

"""
Initialize a relation on a schema from either a model or a dict of cardinalities
for each object.
"""
function initrel(F::FLS,
                 I::Union{Nothing, Dict{Symbol, Int}, StructACSet}=nothing,
                 )::StructACSet
  if !(I isa StructACSet)
    dic = deepcopy(I)
    I = grph_to_cset(F.name, F.schema)
    for (k, v) in (dic === nothing ? [] : collect(dic))
      add_parts!(I, k, v)
    end
  end
  J = grph_to_crel(F.name, F.schema)
  # Initialize data in J from I
  for o in F.schema[:vlabel]
    add_parts!(J, o, nparts(I, o))
  end
  for d in F.schema[:elabel]
    hs, ht = add_srctgt(d)
    for (i, v) in filter(x->x[2]!=0, collect(enumerate(I[d])))
      n = add_part!(J, d)
    set_subpart!(J, n, hs, i)
    set_subpart!(J, n, ht, v)
    end
  end
  return J
end

function realobs(F::FLS)::Set{Symbol}
  return setdiff(Set(F.schema[:vlabel]), [c.apex for c in F.cones])
end
function relsize(F::FLS, I::StructACSet)::Int
  return sum([nparts(I, x) for x in realobs(F)])
end

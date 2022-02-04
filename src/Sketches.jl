module Sketches
export Sketch, LabeledGraph, Cone, dual, cone_query, free_obs, relsize,
       sketch_from_json, to_json, add_srctgt, sizes, zero_ob, one_ob, free_homs,
       constr_homs

"""Basic data structures for limit sketches"""

using Catlab.Present, Catlab.Graphs, Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: TheoryGraph
using Catlab.CategoricalAlgebra.CSetDataStructures: struct_acset
import Catlab.Graphs: src, tgt
using CSetAutomorphisms

using JSON
using AutoHashEquals
using DataStructures: DefaultDict
import Base: isempty

"""Edges and vertices labeled by symbols"""
@present TheoryLabeledGraph <: TheoryGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end;

@acset_type LabeledGraph_(
  TheoryLabeledGraph, index=[:src,:tgt]) <: AbstractGraph
const LabeledGraph = LabeledGraph_{Symbol}

"""Forget about the labels"""
function to_graph(lg::LabeledGraph_)::Graph
  G = Graph(nparts(lg, :V))
  add_edges!(G, lg[:src], lg[:tgt])
  return G
end

"""Data of a cone (or a cocone)"""
@auto_hash_equals struct Cone
  d::LabeledGraph
  apex::Symbol
  legs::Vector{Pair{Int, Symbol}}
  function Cone(d::LabeledGraph, apex::Symbol, legs::Vector{Pair{Int, Symbol}})
    l1, _ = zip(legs...) # l2 might have duplicates, e.g. monomorphism cone
    length(Set(l1)) == length(legs) || error("nonunique legs $legs")
    return new(d, apex, legs)
  end
end

"""
A finite-limit, finite-colimit sketch. Auto-generates data types for C-sets
(representing models, i.e. functors from the schema to Set) and C-rels (for
representing premodels, which may not satisfy equations/(co)limit constraints)
"""
@auto_hash_equals struct Sketch
  name::Symbol
  schema::LabeledGraph
  cones::Vector{Cone}
  cocones::Vector{Cone}
  eqs::Vector{Tuple{Symbol, Vector{Symbol}, Vector{Symbol}}}
  cset::Type
  cset_pres::Presentation
  crel::Type
  crel_pres::Presentation
  function Sketch(name::Symbol, schema::LabeledGraph, cones::Vector{Cone},
                  cocones::Vector{Cone}, eqs::Vector)

    function grph_to_cset(name::Symbol, sketch::LabeledGraph
                         )::Pair{Type, Presentation}
      pres = Presentation(FreeSchema)
      xobs = [Ob(FreeSchema, s) for s in sketch[:vlabel]]
      for x in xobs
        add_generator!(pres, x)
      end
      for (e, src, tgt) in zip(sketch[:elabel], sketch[:src], sketch[:tgt])
        add_generator!(pres, Hom(e, xobs[src], xobs[tgt]))
      end
      expr = struct_acset(name, StructACSet, pres, index=sketch[:elabel])
      eval(expr)
      return eval(name) => pres
    end

    function grph_to_crel(name::Symbol,sketch::LabeledGraph
                         )::Pair{Type,Presentation}
      name_ = Symbol("rel_$name")
      pres = Presentation(FreeSchema)
      nv = length(sketch[:vlabel])
      alledge = vcat([add_srctgt(e) for e in sketch[:elabel]]...)
      xobs = [Ob(FreeSchema, s) for s in [sketch[:vlabel]...,sketch[:elabel]...]]
      for x in xobs
        add_generator!(pres, x)
      end
      for (i,(e, src, tgt)) in enumerate(zip(sketch[:elabel],sketch[:src], sketch[:tgt]))
        s, t = add_srctgt(e)
        add_generator!(pres, Hom(s, xobs[nv+i], xobs[src]))
        add_generator!(pres, Hom(t, xobs[nv+i], xobs[tgt]))
      end
      expr = struct_acset(name_, StructACSet, pres, index=alledge)
      eval(expr)
      return eval(name_) => pres
    end

    function check_eq(p::Vector,q::Vector)::Nothing
      # Get sequence of edge numbers in the schema graph
      pe, qe = [[only(incident(schema, edge, :elabel)) for edge in x]
                for x in [p,q]]
      ps, qs = [isempty(x) ? nothing : schema[:src][x[1]] for x in [pe, qe]]
      isempty(qe) || ps == qs || error(
        "path eq don't share start point \n\t$p ($ps) \n\t$q ($qs)")
      pen, qen = [isempty(x) ? nothing : schema[:tgt][x[end]] for x in [pe,qe]]
      isempty(qe) || pen == qen || error(
        "path eq don't share end point \n\t$p ($pen) \n\t$q ($qen)")
      !isempty(qe) || ps == pen|| error(
        "path eq has self loop but p doesn't have same start/end $p \n$q")
      all([schema[:tgt][p1]==schema[:src][p2]
           for (p1, p2) in zip(pe, pe[2:end])]) || error(
             "head/tail mismatch in p $p \n$q")
      all([schema[:tgt][q1]==schema[:src][q2]
           for (q1, q2) in zip(qe, qe[2:end])]) || error(
             "head/tail mismatch in q $p \n$q")
      return nothing
    end

    function check_cone(c::Cone)::Nothing
      vert = only(incident(schema, c.apex, :vlabel))
      for (v, l) in c.legs
        edge = only(incident(schema, l, :elabel))
        schema[:src][edge] == vert || error("Leg does not come from apex $c")
        schema[:vlabel][schema[:tgt][edge]] == c.d[:vlabel][v] || error(
          "Leg $l -> $v does not go to correct vertex $c")
        is_homomorphic(c.d, schema) || error(
          "Cone diagram does not map into schema $c")
      end
    end

    function check_cocone(c::Cone)::Nothing
      vert = only(incident(schema, c.apex, :vlabel))
      for (v, l) in c.legs
        edge = only(incident(schema, l, :elabel))
        schema[:tgt][edge] == vert || error(
          "Leg $l does not go to apex $(c.apex)")
        schema[:vlabel][schema[:src][edge]] == c.d[:vlabel][v] || error(
          "Leg $l -> $v does not go to correct vertex $c")
        is_homomorphic(c.d, schema) || error(
          "Cone diagram does not map into schema $c")
      end
    end

    [check_eq(p,q) for (_, p, q) in eqs]
    [check_cone(c) for c in cones]
    [check_cocone(c) for c in cocones]
    cset_type, cset_pres = grph_to_cset(name, schema)
    crel_type, crel_pres = grph_to_crel(name, schema)

    return new(name, schema, cones, cocones, eqs, cset_type, cset_pres,
               crel_type, crel_pres)
  end
end

"""Dual sketch. Optionally rename obs/morphisms and the sketch itself"""
function dual(s::Sketch, n::Symbol=Symbol(),
     obs::Vector{Pair{Symbol, Symbol}}=Pair{Symbol, Symbol}[])
  d = Dict(obs)
  eqsub = ps -> reverse([get(d, p, p) for p in ps])
  Sketch(isempty(string(n)) ? Symbol("$(s.name)"*"_dual") : n,
         dualgraph(s.schema, d), [dual(c, d) for c in s.cocones],
         [dual(c,d) for c in s.cones],
         [(n, eqsub(p), eqsub(q)) for (n, p, q) in s.eqs])
end

dual(c::Cone, obs::Dict{Symbol, Symbol}) =
  Cone(dualgraph(c.d, obs), get(obs,c.apex,c.apex),
       [(i => get(obs, x, x)) for (i, x) in c.legs])


function dualgraph(lg::LabeledGraph, obd::Dict{Symbol, Symbol})
  g = deepcopy(lg)
  set_subpart!(g, :src, lg[:tgt])
  set_subpart!(g, :tgt, lg[:src])
  set_subpart!(g, :vlabel, replace(z->get(obd, z, z), g[:vlabel]))
  set_subpart!(g, :elabel, replace(z->get(obd, z, z), g[:elabel]))
  return g
end

src(S::Sketch, e::Symbol) = S.schema[:vlabel][S.schema[:src][
  only(incident(S.schema, e, :elabel))]]
tgt(S::Sketch, e::Symbol) = S.schema[:vlabel][S.schema[:tgt][
  only(incident(S.schema, e, :elabel))]]

cone_to_dict(c::Cone) = Dict([
  "d"=>generate_json_acset(c.d),
  "apex"=>string(c.apex),"legs"=>c.legs])

dict_to_cone(d::Dict)::Cone = Cone(
  parse_json_acset(LabeledGraph,d["d"]), Symbol(d["apex"]),
  Pair{Int,Symbol}[parse(Int, k)=>Symbol(v) for (k, v) in map(only, d["legs"])])

"""TO DO: add cone and eq info to the hash...prob requires CSet for Sketch"""
Base.hash(S::Sketch) = canonical_hash(to_graph(S.schema); pres=TheoryGraph)
to_json(S::Sketch) = JSON.json(Dict([
  :name=>S.name, :schema=>generate_json_acset(S.schema),
  :cones => [cone_to_dict(c) for c in S.cones],
  :cocones => [cone_to_dict(c) for c in S.cocones],
  :eqs => [Dict([:name=>n,:p=>p,:q=>q]) for (n,p,q) in S.eqs]]))

function sketch_from_json(s::String)::Sketch
  p = JSON.parse(s)
  Sketch(Symbol(p["name"]), parse_json_acset(LabeledGraph, p["schema"]),
    [dict_to_cone(d) for d in p["cones"]],
    [dict_to_cone(d) for d in p["cocones"]],
    [(Symbol(pq["name"]), map(Symbol, pq["p"]),
                map(Symbol, pq["q"])) for pq in p["eqs"]])
end

add_srctgt(x::Symbol) = Symbol("src_$(x)") => Symbol("tgt_$(x)")

function free_obs(S::Sketch)::Set{Symbol}
  setdiff(Set(S.schema[:vlabel]), [c.apex for c in vcat(S.cones, S.cocones)])
end

function free_homs(S::Sketch)::Set{Symbol}
  free_ob = free_obs(S)
  homs = [S.schema[e, :elabel] => S.schema[e, [:src, :vlabel]]
          for e in parts(S.schema, :E)]
  Set([e for (e, s) in homs if s ∈ free_ob])
end

function constr_homs(S::Sketch)::Set{Symbol}
  leg_homs = Set(last.(vcat([c.legs for c in vcat(S.cones,S.cocones)]...)))
  setdiff(Set(S.schema[:elabel]), free_homs(S) ∪ leg_homs)
end

function relsize(S::Sketch, I::StructACSet)::Int
  return sum([nparts(I, x) for x in free_obs(S)])
end

function sizes(S::Sketch, I::StructACSet; real::Bool=false)::String
  obs = sort(real ? collect(free_obs(S)) : S.schema[:vlabel])
  join(["$o: $(nparts(I, o))" for o in obs],", ")
end

function get_eq(S::Sketch,name::Symbol)::Pair{Vector{Symbol}, Vector{Symbol}}
  return only([p=>q for (n,p,q) in S.eqs if n==name])
end


zero_ob(S::Sketch) = [c.apex for c in S.cocones if nv(c.d) == 0]
one_ob(S::Sketch) = [c.apex for c in S.cones if nv(c.d) == 0]

end # module


# """
# Query that returns all instances of the base pattern. External variables
# are labeled by the legs of the cone.
# """
# function cone_query(c::Cone)::StructACSet
#   vars = [Symbol("x$i") for i in nparts(c.d, :V)]
#   typs = ["$x(_id=x$i)" for (i, x) in enumerate(c.d[:vlabel])]
#   bodstr = vcat(["begin"], typs)
#   for (e, s, t) in zip(c.d[:elabel], c.d[:src], c.d[:tgt])
#     push!(bodstr, "$e(src_$e=x$s, tgt_$e=x$t)")
#   end
#   push!(bodstr, "end")
#   exstr = "($(join(["$(v)_$i=x$k" for vs in values(vars)
#                     for (i, (k,v)) in enumerate(c.legs)],",") ))"
#   ctxstr = "($(join(vcat(["x$i::$x"
#                           for (i, x) in enumerate(c.d[:vlabel])],),",")))"
#   ex  = Meta.parse(exstr)
#   ctx = Meta.parse(ctxstr)
#   hed = Expr(:where, ex, ctx)
#   bod = Meta.parse(join(bodstr, "\n"))
#   if false
#     println("ex $exstr\n ctx $ctxstr\n bod $(join(bodstr, "\n"))")
#   end
#   res = parse_relation_diagram(hed, bod)
#   return res
# end
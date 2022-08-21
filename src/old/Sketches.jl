module Sketches
export Sketch, S0, LabeledGraph, Cone, Defined, d0, dual, free_obs, relsize, sizes,
       sketch_from_json, to_json, add_srctgt, sizes, zero_ob, one_ob, hom_set,
       hom_in,hom_out,elabel, non_id

"""Basic data structures for limit sketches"""

using Catlab.Present, Catlab.Graphs, Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: TheoryReflexiveGraph, AbstractGraph
using Catlab.CategoricalAlgebra.CSetDataStructures: struct_acset
import Catlab.Theories: dual
import Catlab.Graphs: src, tgt, topological_sort, refl, inneighbors,
                      outneighbors
using CSetAutomorphisms

using JSON
using AutoHashEquals
using DataStructures: DefaultDict
import Base: isempty
######################################
const Defined = Pair{Set{Symbol},Set{Symbol}}
const d0 = Set{Symbol}() => Set{Symbol}()

inneighbors(g::T, v::Int) where {T<:AbstractReflexiveGraph} =
  subpart(g, incident(g, v, :tgt), :src)
outneighbors(g::T, v::Int) where {T<:AbstractReflexiveGraph} =
  subpart(g, incident(g, v, :src), :tgt)


"""Edges and vertices labeled by symbols"""
@present TheoryLabeledGraph <: TheoryReflexiveGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end;

@acset_type LabeledGraph_(
  TheoryLabeledGraph,
  index=[:src,:tgt,:vlabel, :elabel]
) <: AbstractReflexiveGraph

const LabeledGraph = LabeledGraph_{Symbol}

"""Forget about the labels"""
function to_graph(lg::LabeledGraph_)::Graph
  G = Graph(nparts(lg, :V))
  s, t= []
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
  eqs::Vector{LabeledGraph}
  cset::Type
  cset_pres::Presentation
  crel::Type
  crel_pres::Presentation
  function Sketch(name::Symbol, schema::LabeledGraph, cones::Vector{Cone},
                  cocones::Vector{Cone}, eqs::V) where V<:AbstractVector
    namechars = join(vcat(schema[:vlabel], schema[:elabel]))
    r = Set(refl(schema))
    e = "BAD SYMBOL in $schema"
    all([!occursin(x, namechars) for x in [",", "|"]]) || error(e)
    function grph_to_cset(name::Symbol, sketch::LabeledGraph
                         )::Pair{Type, Presentation}
      pres = Presentation(FreeSchema)
      xobs = [Ob(FreeSchema, s) for s in sketch[:vlabel]]
      for x in xobs
        add_generator!(pres, x)
      end
      z = zip(sketch[:elabel], sketch[:src], sketch[:tgt])
      for (i,(e, src, tgt)) in enumerate(z)
        if i ∉ r
          add_generator!(pres, Hom(e, xobs[src], xobs[tgt]))
        end
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
      alledge = vcat([add_srctgt(e) for (i,e)
                      in enumerate(sketch[:elabel]) if i ∉ r]...)
      labs = [sketch[:vlabel]...,
              [e for (i,e) in enumerate(sketch[:elabel]) if i ∉ r]...]
      xobs = [Ob(FreeSchema, s) for s in labs]
      for x in xobs
        add_generator!(pres, x)
      end
      z = collect(enumerate(zip(sketch[:elabel],sketch[:src], sketch[:tgt])))

      for (i,(_,(e, src_, tgt_))) in enumerate(filter(i->i[1]∉r, z))
          s, t = add_srctgt(e)
          add_generator!(pres, Hom(s, xobs[nv+i], xobs[src_]))
          add_generator!(pres, Hom(t, xobs[nv+i], xobs[tgt_]))
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
    if !(isempty(eqs) || first(eqs) isa LabeledGraph)
      [check_eq(p,q) for (p, q) in eqs]
      eqds = eqs_to_diagram(schema, eqs)
    else
      eqds = isempty(eqs) ? LabeledGraph[] : eqs
    end
    [check_cone(c) for c in cones]
    [check_cocone(c) for c in cocones]
    cset_type, cset_pres = grph_to_cset(name, schema)
    crel_type, crel_pres = grph_to_crel(name, schema)
    return new(name, schema, cones, cocones, eqds, cset_type, cset_pres,
               crel_type, crel_pres)
  end
end
const S0=Sketch(:dummy, LabeledGraph(),Cone[],Cone[],[])

struct SketchMorphism
  d::Sketch
  cd::Sketch
  h::ACSetTransformation # Graph transformation of schemas
end



"""Dual sketch. Optionally rename obs/morphisms and the sketch itself"""
function dual(s::Sketch, n::Symbol=Symbol(),
     obs::Vector{Pair{Symbol, Symbol}}=Pair{Symbol, Symbol}[])
  d = Dict(obs)
  eqsub = ps -> reverse([get(d, p, p) for p in ps])
  dname = isempty(string(n)) ? Symbol("$(s.name)"*"_dual") : n
  dschema = dualgraph(s.schema, d)
  dcones = [dual(c, d) for c in s.cocones]
  dccones = [dual(c,d) for c in s.cones]
  eqs = vcat(diagram_to_eqs.(s.eqs)...)
  deqs = [[eqsub(p) for p in ps] for ps in eqs]
  Sketch(dname, dschema, dcones, dccones,deqs)
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
Base.hash(S::Sketch) = call_nauty(to_graph(S.schema))
to_json(S::Sketch) = JSON.json(Dict([
  :name=>S.name, :schema=>generate_json_acset(S.schema),
  :cones => [cone_to_dict(c) for c in S.cones],
  :cocones => [cone_to_dict(c) for c in S.cocones],
  :eqs => generate_json_acset.(S.eqs)]))

function sketch_from_json(s::String)::Sketch
  p = JSON.parse(s)
  Sketch(Symbol(p["name"]), parse_json_acset(LabeledGraph, p["schema"]),
    [dict_to_cone(d) for d in p["cones"]],
    [dict_to_cone(d) for d in p["cocones"]],
    [parse_json_acset(LabeledGraph,e) for e in p["eqs"]])
end

add_srctgt(x::Symbol) = Symbol("src_$(x)") => Symbol("tgt_$(x)")

"""Objects that are not the apex of some (co)cone"""
function free_obs(S::Sketch)::Set{Symbol}
  setdiff(Set(S.schema[:vlabel]), [c.apex for c in vcat(S.cones, S.cocones)])
end


zero_ob(S::Sketch) = [c.apex for c in S.cocones if nv(c.d) == 0]
one_ob(S::Sketch) = [c.apex for c in S.cones if nv(c.d) == 0]

"""List of arrows between two sets of vertices"""
function hom_set(S::Sketch, d_symbs, cd_symbs)::Vector{Symbol}
  symbs = [d_symbs, cd_symbs]
  d_i, cd_i = [vcat(incident(S.schema, x, :vlabel)...) for x in symbs]
  e_i = setdiff(
        (vcat(incident(S.schema, d_i, :src)...)
        ∩ vcat(incident(S.schema, cd_i, :tgt)...)),
        refl(S.schema) )
  return S.schema[e_i, :elabel]
end

hom_in(S::Sketch, t::Symbol) = hom_set(S, S.schema[:vlabel], [t])
hom_out(S::Sketch, t::Symbol) = hom_set(S, [t], S.schema[:vlabel])


const DD = DefaultDict{Pair{Int,Int},Set{Vector{Int}}}

"""Enumerate all paths of an acyclic graph, indexed by src+tgt"""
function enumerate_paths(G::HasGraph;
                         sorted::Union{AbstractVector{Int},Nothing}=nothing
                        )::DD
  sorted = isnothing(sorted) ? topological_sort(G) : sorted
  Path = Vector{Int}
  paths = [Set{Path}() for _ in 1:nv(G)] # paths that start on a particular V
  for v in reverse(topological_sort(G))
    push!(paths[v], Int[]) # add length 0 paths
    for e in incident(G, v, :src)
      push!(paths[v], [e]) # add length 1 paths
      for p in paths[G[e, :tgt]] # add length >1 paths
        push!(paths[v], vcat([e], p))
      end
    end
  end
  # Restructure `paths` into a data structure indexed by start AND end V
  allpaths = DefaultDict{Pair{Int,Int},Set{Path}}(()->Set{Path}())
  for (s, ps) in enumerate(paths)
    for p in ps
      push!(allpaths[s => isempty(p) ? s : G[p[end],:tgt]], p)
    end
  end
  return allpaths
end

"""Add path to commutative diagram without repeating information"""
function add_path!(schema::LabeledGraph, lg::LabeledGraph, p::Vector{Symbol},
                  all_p::Dict{Vector{Symbol}, Int},
                  eqp::Union{Nothing, Vector{Symbol}}=nothing,
                   )
  #all_p = isnothing(all_p) ? union(values(enumerate_paths(lg)...)) : all_p
  s = only(incident(schema, first(p), :elabel))

  for i in 1:length(p)
    if !haskey(all_p, p[1:i])
      e = only(incident(schema, p[i], :elabel))
      t = schema[e, [:tgt,:vlabel]]
      if isnothing(eqp) || i < length(p)
        new_v = add_part!(lg, :V; vlabel=t)
      else
        new_v = all_p[eqp]
      end
      s = i == 1 ? 1 : all_p[p[1:i-1]]
      add_part!(lg, :E; src=s, tgt=new_v, elabel=p[i])
      all_p[p[1:i]] = new_v
    end
  end
end

"""
Get per-object diagrams encoding all commutative diagrams which start at that
point, using the information of pairwise equations

eqs:: Vector{Tuple{Symbol, Vector{Symbol}, Vector{Symbol}}}
"""
function eqs_to_diagram(schema::LabeledGraph, eqs)::Vector{LabeledGraph}
  lgs = [LabeledGraph() for _ in 1:nv(schema)]
  all_ps = [Dict{Vector{Symbol}, Int}(Symbol[]=>1) for _ in 1:nv(schema)]
  for (i, root) in enumerate(schema[:vlabel])
    add_part!(lgs[i], :V; vlabel=root)
  end
  for (p1, p2) in eqs # TODO: support more than 2 eqs at once
    src_i = schema[only(incident(schema, first(p1), [:elabel])), :src]
    if haskey(all_ps[src_i], p2)
      add_path!(schema, lgs[src_i], p1, all_ps[src_i], Vector{Symbol}(p2))
    else
      add_path!(schema, lgs[src_i], p1, all_ps[src_i])
      add_path!(schema, lgs[src_i], p2, all_ps[src_i], p1)
    end
  end
  return lgs
end

function diagram_to_eqs(g::LabeledGraph)
  map(filter(x->length(x)>1, collect(values(enumerate_paths(g))))) do ps
    [g[p,:elabel] for p in ps]
  end
end

"""ignores the identity morphisms"""
elabel(S::Sketch) = elabel(S.schema)
elabel(C::Cone) = elabel(C.d)
elabel(G::LabeledGraph) = G[non_id(G), :elabel]
non_id(S::Sketch) = non_id(S.schema)
non_id(G::LabeledGraph) = setdiff(edges(G), G[:refl]) |> collect |> sort

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
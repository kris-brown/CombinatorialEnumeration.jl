module Sketches
export Sketch, LabeledGraph, Cone, hom_set, hom_in, hom_out,
       sketch_from_json, to_json, add_src, add_tgt, add_srctgt, dual, elabel,
       relsize, sizes, cone_leg,cone_legs, cocone_legs, cocone_leg,
       add_cone,add_cocone, add_path, labels, vlabel, add_pathrel, add_id, show_lg,
       enum_paths

using Catlab.Present, Catlab.Graphs, Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.Programs, Catlab.Graphics
using Catlab.CategoricalAlgebra.CSetDataStructures: AnonACSetType
import Catlab.Theories: dual
import Catlab.Graphs: src, tgt, topological_sort, inneighbors, outneighbors, enumerate_paths, Graph
import Catlab.CategoricalAlgebra: legs
using CSetAutomorphisms

using AutoHashEquals
using JSON
using DataStructures # DefaultDict, IntDisjointSets

# Reflexive graphs
##################

inneighbors(g::T, v::Int) where {T<:AbstractReflexiveGraph} =
  subpart(g, incident(g, v, :tgt), :src)
outneighbors(g::T, v::Int) where {T<:AbstractReflexiveGraph} =
  subpart(g, incident(g, v, :src), :tgt)


"""A finitely presented category (with designated id edges)"""
@present TheoryLabeledGraph <: SchReflexiveGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end;

@acset_type LabeledGraph_(
  TheoryLabeledGraph, index=[:src,:tgt,:vlabel,:elabel]
) <: AbstractReflexiveGraph

const LabeledGraph = LabeledGraph_{Symbol}
show_lg(x::LabeledGraph) = to_graphviz(x; node_labels=:vlabel, edge_labels=:elabel)

add_id(x::Symbol) = Symbol("id_$x")
rem_id(x::String) = x[4:end] # assumes add_id(x::Symbol) = "id_$x"

function add_id!(G::LabeledGraph)
  for v in vertices(G)
    if G[v, :refl] == 0
      e = add_edge!(G, v, v; elabel=add_id(G[v,:vlabel]))
      set_subpart!(G, v, :refl, e)
    end
  end
  return G
end

function rem_id(G::LabeledGraph)
  newG = LabeledGraph()
  copy_parts!(newG, G; V=vertices(G), E=non_id(G))
  return newG
end

src(G::LabeledGraph, f::Symbol) = G[only(incident(G, f, :elabel)), :src]
tgt(G::LabeledGraph, f::Symbol) = G[only(incident(G, f, :elabel)), :tgt]
vlabel(G::LabeledGraph) = G[:vlabel]
elabel(G::LabeledGraph) = G[non_id(G), :elabel]
labels(G::LabeledGraph) = vcat(G[:vlabel], elabel(G))
add_src(x::Symbol) = Symbol("src_$(x)")
add_tgt(x::Symbol) = Symbol("tgt_$(x)")
add_srctgt(x::Symbol) = add_src(x) => add_tgt(x)
add_cone(x::Int) = Symbol("Cone_$x")
add_cocone(x::Int) = Symbol("Cocone_$x")
add_path(n::Symbol, x::Symbol) = Symbol("$(n)_Path_$x")
add_path(i::Int) = Symbol("P$i")
add_pathrel(i::Int) = (Symbol("R_$i"), add_srctgt(Symbol("R_$i"))...)

elabel(G::LabeledGraph, st::Bool) =
  collect(zip([G[non_id(G), x] for x in
    [:elabel, [:src,:vlabel], [:tgt,:vlabel]]]...))
non_id(G::LabeledGraph) = setdiff(edges(G), G[:refl]) |> collect |> sort


# Cones
####################################

"""
Data of a cone (or a cocone)

d - a diagram in the schema for the finite limit sketch
    (note this actually a graph homomorphism, so edges map to edges, not paths)
apex - an object in the schema
legs - a list of pairs, where the first element selects an object in the diagram
       and the second element picks a morphism in the schema
"""
@auto_hash_equals struct Cone
  d::LabeledGraph
  apex::Symbol
  legs::Vector{Pair{Int, Symbol}}
  ulegs::Vector{Symbol}
  leg_inds::Dict{Symbol,Vector{Int}}
  is_dag::Bool
  uwd::StructACSet
  function Cone(d::LabeledGraph, apex::Symbol, legs::Vector{Pair{Int, Symbol}})
    length(Set(first.(legs))) == length(legs) || error("nonunique legs $legs")
    # check if vertex ordering is toposort. Do things differently if so?
    is_dag = all(e->src(d,e) <= tgt(d,e), edges(d))
    ulegs = unique(last.(legs))
    leg_inds = Dict(map(ulegs) do l
      l=>findall(==(l), last.(legs))
    end)
    return new(add_id!(d), apex, legs, ulegs, leg_inds, is_dag, cone_query(d, legs))
  end
end

Cone(s::Symbol) = Cone(LabeledGraph(), s, Pair{Int,Symbol}[])

legs(c::Cone) = c.legs
vlabel(C::Cone) = vlabel(C.d)
elabel(C::Cone) = elabel(C.d)
cone_leg(c::Int, i::Int) = Symbol("$(add_cone(c))_$i")
cone_legs(c::Int) = [cone_leg(c, i) for i in 1:nv(c.d)]
cocone_legs(c::Cone) = [cocone_leg(c, i) for i in 1:length(c.legs)]
cocone_leg(c::Int, i::Int) = Symbol("$(add_cocone(c))_$i")
cocone_leg(c::Int, i::Int, st) = let s = cocone_leg(c, i);
                                                   (s, add_srctgt(s)...) end
cocone_apex(c::Int) = Symbol("$(add_cocone(c))_apex")
elabel(C::Cone, st::Bool) = elabel(C.d, true)

# Path equations
################

const DD = DefaultDict{Pair{Int,Int},Set{Vector{Int}}}
const Pth = Vector{Int}

function Graph(C::T) where {T<:HasGraph}
  G = Graph()
  copy_parts!(G, C)
  return G
end

"""Return a dictionary with (src,tgt) keys and a list of paths between them"""
function enum_paths(G::HasGraph)
  ep = enumerate_paths(Graph(G))
  return Dict(map(collect(Iterators.product(vertices(G),vertices(G)))) do (i,j)
    (i,j) => ep[incident(ep, i, :src) ∩ incident(ep, j, :tgt), :eprops]
  end)
end

"""Add path to commutative diagram without repeating information"""
function add_path!(schema::LabeledGraph, lg::LabeledGraph, p::AbstractVector{Symbol},
                  all_p::Dict{Vector{Symbol}, Int},
                  eqp::Union{Nothing, AbstractVector{Symbol}}=nothing,
                   )
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
function eqs_to_diagrams(schema::LabeledGraph, eqs)
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
  return Dict(zip(vlabel(schema),add_id!.(lgs)))
end

function diagram_to_eqs(g::LabeledGraph)
  map(filter(x->length(x)>1, collect(values(enum_paths(rem_id(g)))))) do ps
    [g[p,:elabel] for p in ps]
  end
end

# Sketches
##########
@present SchSingleton(FreeSchema) begin P1::Ob end
@acset_type Singleton(SchSingleton)

"""
A finite-limit, finite-colimit sketch. Auto-generates data types for C-sets
(representing models, i.e. functors from the schema to Set) and C-rels (for
representing premodels, which may not satisfy equations/(co)limit constraints)
"""
@auto_hash_equals struct Sketch
  schema::LabeledGraph
  cones::Vector{Cone}
  cocones::Vector{Cone}
  eqs::Dict{Symbol, LabeledGraph}
  cset::Type
  crel::Type
  function Sketch(schema::LabeledGraph; cones=Cone[],
                  cocones=Cone[], eqs=Vector{Symbol}[]) where V<:AbstractVector
    add_id!(schema)
    namechars = join(vcat(schema[:vlabel], schema[:elabel]))
    e = "BAD SYMBOL in $schema"
    all([!occursin(x, namechars) for x in [",", "|"]]) || error(e)

    if isempty(eqs)
      eqds = Dict(map(vlabel(schema)) do v
        d = LabeledGraph(); add_part!(d,:V; vlabel=v)
        v => add_id!(d)
      end)
    else
      if (first(eqs) isa AbstractVector)
        [check_eq(schema, p,q) for (p, q) in eqs]
        eqds = eqs_to_diagrams(schema, eqs)
      else
        length(eqs) == nv(schema) || error("Bad eq input $eqs")
        eqds = Dict(zip(vlabel(schema),eqs))
      end
    end
    [check_cone(schema, c) for c in cones]
    [check_cocone(schema, c) for c in cocones]
    cset_type = grph_to_cset(schema)
    crel_type = grph_to_crel(schema)
    return new(schema, cones, cocones, eqds, cset_type, crel_type)
  end
end

vlabel(S::Sketch) = vlabel(S.schema)
elabel(S::Sketch) = elabel(S.schema)
elabel(S::Sketch, st::Bool) = elabel(S.schema, true)
labels(S::Sketch) = vcat(S.schema[:vlabel], elabel(S))
non_id(S::Sketch) = non_id(S.schema)

"""Convert a presentation of a schema (as a labeled graph) into a C-Set type"""
function grph_to_pres(sketch::LabeledGraph)::Presentation
  pres = Presentation(FreeSchema)
  xobs = [Ob(FreeSchema, s) for s in sketch[:vlabel]]

  for x in xobs
    add_generator!(pres, x)
  end
  getob(s::Symbol) = let ss=pres.generators[:Ob];
    ss[findfirst(==(s), Symbol.(string.(ss)))] end

  for (e, src, tgt) in elabel(sketch, true)
    add_generator!(pres, Hom(e, getob(src), getob(tgt)))
  end
  return pres
end

function pres_to_grph(p::Presentation)::LabeledGraph
  g = LabeledGraph()
  for v in p.generators[:Ob] add_part!(g, :V; vlabel=Symbol(v)) end
  for e in p.generators[:Hom]
    add_edge!(g, only(incident(g,Symbol(dom(e)), :vlabel)),
                 only(incident(g,Symbol(codom(e)), :vlabel));
                 elabel=Symbol(e))
  end
  return g
end

grph_to_cset(S::LabeledGraph) = AnonACSetType(grph_to_pres(S))
  # ; index=collect(elabel(S)))

"""
Get a C-Set type that can store the information of premodels

This includes a *relation* for each morphism (not a function)
As well as data related to (co)cones, path eqs, and equivalence classes.

For each object, we need another object which is the quotiented object via an
equivalence relation.

For each cocone, we need a *relation* for each diagram object for each element
in the apex object.

For each set of path equations (indexed by start object), we need (for each
element in the start object) a *relation* for each object in the commutative
diagram, signaling which values are possibly in the path.


"""
function grph_to_crel(sketch::LabeledGraph;
                      cones=Cone[], cocones=Cone[], path_eqs=LabeledGraph[]
                      )::Type
  pres = Presentation(FreeSchema)
  getob(s::Symbol) = let ss=pres.generators[:Ob];
                         ss[findfirst(==(s), Symbol.(string.(ss)))] end

  # add objects
  [add_generator!(pres, Ob(FreeSchema, v)) for v in sketch[:vlabel]]

  # add morphisms as relations
  for (e, src_, tgt_) in elabel(sketch, true)
    s, t = add_srctgt(e)
    g = add_generator!(pres, Ob(FreeSchema, e))
    add_generator!(pres, Hom(s, g, getob(src_)))
    add_generator!(pres, Hom(t, g, getob(tgt_)))
  end

  return AnonACSetType(pres,index=Symbol.(string.(pres.generators[:Hom])))
end


"""Validate path eq"""
function check_eq(schema::LabeledGraph, p::AbstractVector,q::AbstractVector)::Nothing
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

"""Validate cone data"""
function check_cone(schema::LabeledGraph, c::Cone)::Nothing
  vert = only(incident(schema, c.apex, :vlabel))
  for (v, l) in c.legs
    edge = only(incident(schema, l, :elabel))
    schema[:src][edge] == vert || error("Leg does not come from apex $c")
    schema[:vlabel][schema[:tgt][edge]] == c.d[:vlabel][v] || error(
      "Leg $l -> $v does not go to correct vertex $c")
    is_homomorphic(c.d, schema) || error(
      "Cone diagram does not map into schema $c \n\n$(schema)")
  end
end

"""Validate cocone data"""
function check_cocone(schema::LabeledGraph, c::Cone)::Nothing
  vert = only(incident(schema, c.apex, :vlabel))
  for (v, l) in c.legs
    edge = only(incident(schema, l, :elabel))
    schema[:tgt][edge] == vert || error(
      "Leg $l does not go to apex $(c.apex)")
    schema[:vlabel][schema[:src][edge]] == c.d[:vlabel][v] || error(
      "Leg $l -> $v does not go to correct vertex $c")

    is_homomorphic(c.d, schema) || error(
      "Cone diagram $(c.d) \ndoes not map into schema\n $schema")
  end
end

# const S0=Sketch(:dummy, LabeledGraph()) # placeholder sketch

function project(S::Sketch, crel::StructACSet, c::Cone)
  crel = deepcopy(crel)
  for v in setdiff(vlabel(S),vlabel(c)) ∪ setdiff(elabel(S),elabel(c))
    rem_parts!(crel, v, parts(crel, v))
  end
  return crel
end

# Don't yet know if this stuff will be used
##########################################
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
hom_in(S::Sketch, t::Vector{Symbol}) = vcat([hom_in(S,x) for x in t]...)
hom_out(S::Sketch, t::Vector{Symbol}) = vcat([hom_out(S,x) for x in t]...)

"""Dual sketch. Optionally rename obs/morphisms and the sketch itself"""
function dual(s::Sketch,obs::Vector{Pair{Symbol,Symbol}}=Pair{Symbol,Symbol}[])
  d = Dict(obs)
  eqsub = ps -> reverse([get(d, p, p) for p in ps])
  dschema = dualgraph(s.schema, d)
  dcones = [dual(c, d) for c in s.cocones]
  dccones = [dual(c,d) for c in s.cones]
  eqs = vcat(diagram_to_eqs.(values(s.eqs))...)
  deqs = [[eqsub(p) for p in ps] for ps in eqs]
  Sketch(dschema, cones=dcones, cocones=dccones,eqs=deqs)
end

dual(c::Cone, obs::Dict{Symbol, Symbol}) =
  Cone(dual(dualgraph(c.d, obs)), get(obs,c.apex,c.apex),
       [(nv(c.d)-i+1 => get(obs, x, x)) for (i, x) in c.legs])

"""Reverse vertex indices"""
function dual(lg::LabeledGraph)
  G = deepcopy(lg)
  n = nv(lg)+1
  set_subpart!(G, :vlabel,reverse(lg[:vlabel]))
  set_subpart!(G, :refl,reverse(lg[:refl]))
  [set_subpart!(G, y,  [n-x for x in lg[y]]) for y in [:src,:tgt]]
  return G
end

"""Flip edge directions. Optionally rename symbols"""
function dualgraph(lg::LabeledGraph, obd::Dict{Symbol, Symbol})
  g = deepcopy(lg) # reverse vertex order
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
  :schema=>generate_json_acset(S.schema),
  :cones => [cone_to_dict(c) for c in S.cones],
  :cocones => [cone_to_dict(c) for c in S.cocones],
  :eqs => [generate_json_acset(S.eqs[v]) for v in vlabel(S)]]))

function sketch_from_json(s::String)::Sketch
  p = JSON.parse(s)
  Sketch(parse_json_acset(LabeledGraph, p["schema"]),
    cones=[dict_to_cone(d) for d in p["cones"]],
    cocones=[dict_to_cone(d) for d in p["cocones"]],
    eqs=[parse_json_acset(LabeledGraph,e) for e in p["eqs"]])
end

function relsize(S::Sketch, I::StructACSet)::Int
  return sum([nparts(I, x) for x in S.schema[:vlabel]])
end

"""Pretty print the sizes of objects in a (pre)model"""
function sizes(S::Sketch, I::StructACSet; )::String
  join(["$o: $(nparts(I, o))" for o in S.schema[:vlabel]],", ")
end

function sizes(::Sketch, I::StructACSet{S}, more::Bool)::String where {S}
  join(["$o: $(nparts(I, o))" for o in ob(S)], ", ")
end


"""
Query that returns all instances of the base pattern. External variables
are labeled by the legs of the cone.

If the apex of the cone has multiple legs with the same morphism, then by
functionality the junctions they point to must be merged, which we enforce.
However, this assumes the model is valid. For instance, the monomorphism
cone constraint would never detect that a morphism isn't mono if we perform
this optimization, so perhaps we should never do this?

Maybe we just use the optimized query depending on whether certain tables/fks
are frozen.
"""
function cone_query(d::LabeledGraph, legs; optimize=false)::StructACSet
  verbose = false
  vars = [Symbol("x$i") for i in nparts(d, :V)]
  typs = ["$x(_id=x$i)" for (i, x) in enumerate(d[:vlabel])]
  bodstr = vcat(["begin"], typs)
  for (i,e) in filter(x->x[1]∉refl(d), collect(enumerate(d[:elabel])))
    s=src(d, i); t=tgt(d,i); push!(bodstr, "$e(src_$e=x$s, tgt_$e=x$t)")
  end
  push!(bodstr, "end")
  exstr = "($(join(["$(v)_$i=x$k" for vs in values(vars)
                    for (i, (k,v)) in enumerate(legs)],",") ))"
  ctxstr = "($(join(vcat(["x$i::$x"
                          for (i, x) in enumerate(d[:vlabel])],),",")))"
  ex  = Meta.parse(exstr)
  ctx = Meta.parse(ctxstr)
  hed = Expr(:where, ex, ctx)
  bod = Meta.parse(join(bodstr, "\n"))
  if verbose println("ex $exstr\n ctx $ctxstr\n bod $(join(bodstr, "\n"))") end
  res = parse_relation_diagram(hed, bod)
  if optimize
    # Merge junctions which
    μl = [minimum(findall(==(l), last.(legs))) for l in last.(legs)]
    μj = vcat(μl, length(legs)+1 : nparts(res,:Junction))
    μb = vcat(μl, length(legs)+1 : nparts(res,:Box))
    μp = vcat(μl, length(legs)+1 : nparts(res,:Port))
    for j in [:junction, :outer_junction]
      set_subpart!(res,j,μj[res[j]])
    end
    set_subpart!(res, :box, μb[res[:box]])
    res2 = typeof(res)()
    # There is a bug: cannot delete from a UWD w/o an error
    copy_parts!(res2, res;
      Junction=[i for i in parts(res, :Junction) if i ∈ μj],
      Box=[i for i in parts(res, :Box) if i ∈ μb],
      Port=[i for i in parts(res, :Port) if i ∈ μp],
      OuterPort=parts(res,:OuterPort))
    return res2
  else
    return res
  end
end

cone_query(c::Cone) = cone_query(c.d, c.legs)



# function cocone_to_cset(n::Symbol, schema::LabeledGraph, c::Cone, i::Int)
    # name = Symbol("$(n)_cocone_$i")
  # pres = Presentation(FreeSchema)

  # obs = Dict([v=>add_generator!(pres, Ob(FreeSchema, Symbol("$v")))
  #             for v in Set(c.d[:vlabel])])
  # ap = add_generator!(pres, Ob(FreeSchema, :apex))

  # for (j,k) in enumerate(c.d[:vlabel])
  #   cc, ccs, cct = cocone_leg(i, j, true)
  #   grel = add_generator!(pres, Ob(FreeSchema, cc))
  #   add_generator!(pres, Hom(ccs, grel, ap))
  #   add_generator!(pres, Hom(cct, grel, obs[k]))
  # end
  # expr = struct_acset(name, StructACSet, pres, index=pres.generators[:Hom])
  # eval(expr)
  # return eval(name)
# end

# function eq_to_type(n::Symbol, p::LabeledGraph, x::Symbol)
#   name = add_path(n,x)
#   pres = Presentation(FreeSchema)
#   obs = [add_generator!(pres, Ob(FreeSchema, add_path(i)))
#          for (i, v) in enumerate(p[:vlabel])]

#   for (i,k) in collect(enumerate(p[:vlabel]))
#     pob, psrc, ptgt = add_pathrel(i)
#     gob = add_generator!(pres, Ob(FreeSchema, pob))
#     add_generator!(pres, Hom(psrc, gob, obs[1]))
#     add_generator!(pres, Hom(ptgt, gob, obs[i]))
#   end
#   expr = struct_acset(name, StructACSet, pres, index=pres.generators[:Hom])
#   eval(expr)
#   return eval(name)
# end
"""
For each cone, we have a cone object which keeps track of, for each element in
the apex object, which tuple of elements in the diagram objects are matched. We
only need one table for each distinct *type* of object in the diagram, not one
for each vertex in the diagram.
"""
# function cone_to_cset(n::Symbol, schema::LabeledGraph, c::Cone, i::Int)
  # name = Symbol("$(n)_cone_$i")
  # pres = Presentation(FreeSchema)
  # obs = Dict([v=>add_generator!(pres, Ob(FreeSchema, Symbol("$v")))
  #             for v in Set(c.d[:vlabel])])
  # ap = add_generator!(pres, Ob(FreeSchema, :apex))

  # for (j,k) in enumerate(c.d[:vlabel])
  #   add_generator!(pres, Hom(cone_leg(i, j), ap, obs[k]))
  # end
  # expr = struct_acset(name, StructACSet, pres, index=pres.generators[:Hom])
  # eval(expr)
  # return eval(name)
# end

end # module
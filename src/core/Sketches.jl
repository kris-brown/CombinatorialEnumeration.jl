module Sketches
export Sketch, Cone, hom_set, hom_in, hom_out,
       sketch_from_json, to_json, add_src, add_tgt, add_srctgt, dual, elabel,
       relsize, sizes, cone_leg,cone_legs, cocone_legs, cocone_leg,
       add_cone,add_cocone, add_path, labels, vlabel, add_pathrel, add_id, show_lg,
       add_eqs!, grph_to_cset, project, mkFinFunctorPres

using Catlab.Present, Catlab.Graphs, Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.Programs, Catlab.Graphics
using Catlab.CategoricalAlgebra.FinCats: FinCatPresentation
using Catlab.CategoricalAlgebra.CSetDataStructures: AnonACSetType
import Catlab.Theories: dual
import Catlab.CategoricalAlgebra: legs
import Catlab.Graphs: src, tgt
using CSetAutomorphisms

using AutoHashEquals
using JSON
using DataStructures # DefaultDict, IntDisjointSets

using ..LGraphs, ..SketchCSets
using ..SketchCSets: SchLGraph, LabeledSketchCSettoLGraph, 
                     LabeledSketchCSetToLG, c_vocab, cc_vocab
import ..SketchCSets: vlabel, elabel, mkLabeledSketchCSet
import ..LGraphs: mkFinCatPresentation, add_eq!
                     


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
  d::LGraph
  apex::Symbol
  legs::Vector{Pair{Int, Symbol}}
  ulegs::Vector{Symbol}
  leg_inds::Dict{Symbol,Vector{Int}}
  is_dag::Bool
  uwd::StructACSet
  function Cone(d::LGraph, apex::Symbol, legs::Vector{Pair{Int, Symbol}})
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

Cone(s::Symbol) = Cone(LGraph(), s, Pair{Int,Symbol}[])

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
  schema::LGraph
  cones::Vector{Cone}
  cocones::Vector{Cone}
  eqs::Dict{Symbol, LGraph}
  cset::Type
  crel::Type
  zero_obs::Set{Symbol}
  function Sketch(schema::LGraph; cones=Cone[],
                  cocones=Cone[], eqs=Vector{Symbol}[])
    add_id!(schema)
    namechars = join(vcat(schema[:vlabel], schema[:elabel]))
    e = "BAD SYMBOL in $schema"
    all([!occursin(x, namechars) for x in [",", "|"]]) || error(e)

    if isempty(eqs)
      eqds = Dict(map(vlabel(schema)) do v
        d = LGraph(); add_part!(d,:V; vlabel=v)
        v => add_id!(d)
      end)
    else
      if (first(eqs) isa AbstractVector)
        for eqs_ in eqs 
          for (p,q) in zip(eqs_,eqs_[2:end])
            check_eq(schema, p,q)
          end
        end
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
    z_obs = get_zero_obs(schema, [c.apex for c in cocones if nv(c.d)==0])
    return new(schema, cones, cocones, eqds, cset_type, crel_type, z_obs)
  end
end

vlabel(S::Sketch) = vlabel(S.schema)
elabel(S::Sketch) = elabel(S.schema)
elabel(S::Sketch, st::Bool) = elabel(S.schema, true)
labels(S::Sketch) = vcat(S.schema[:vlabel], elabel(S))
non_id(S::Sketch) = non_id(S.schema)
function get_zero_obs(S::LGraph, zero_obs::AbstractVector)
  change = true
  while change  # Maps into zero obs are zero obs
    change = false
    for z in zero_obs
      for h in hom_in(S, z)
        sh = S[src(S,h),:vlabel]
        if sh ∉ zero_obs
          push!(zero_obs, sh); change = true
        end
      end
    end
  end
  return Set(zero_obs)
end

"""Convert a presentation of a schema (as a labeled graph) into a C-Set type"""
function grph_to_pres(sketch::LGraph)
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

"""Presentation -> CSet type"""
function grph_to_cset(S::LGraph)
  p =  grph_to_pres(S)
  AnonACSet(p) |> typeof 
end
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
function grph_to_crel(sketch::LGraph;
                      cones=Cone[], cocones=Cone[], path_eqs=LGraph[]
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

  return AnonACSet(pres,index=Symbol.(string.(pres.generators[:Hom]))) |> typeof
end


"""Validate path eq"""
function check_eq(schema::LGraph, p::AbstractVector,q::AbstractVector)::Nothing
  !(isempty(p) || isempty(q)) || error("cannot have empty path: use add_id(::Symbol)")
  # Get sequence of edge numbers in the schema graph
  pe, qe = map([p,q]) do x 
    [only(incident(schema, edge, :elabel)) for edge in x]
  end
  ps, qs = [isempty(x) ? nothing : schema[:src][x[1]] for x in [pe, qe]]
  ps == qs || error("path eq don't share start point \n\t$p ($ps) \n\t$q ($qs)")
  pen, qen = [schema[:tgt][x[end]] for x in [pe,qe]]
  pen == qen || error("path eq don't share end point \n\t$p ($pen) \n\t$q ($qen)")
  all([schema[:tgt][p1]==schema[:src][p2]
       for (p1, p2) in zip(pe, pe[2:end])]) || error(
         "head/tail mismatch in p $p \n$q")
  all([schema[:tgt][q1]==schema[:src][q2]
       for (q1, q2) in zip(qe, qe[2:end])]) || error(
         "head/tail mismatch in q $p \n$q")
  return nothing
end

"""Validate cone data"""
function check_cone(schema::LGraph, c::Cone)::Nothing
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
function check_cocone(schema::LGraph, c::Cone)::Nothing
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

function project(S::Sketch, crel::StructACSet, c::Cone)
  crel = deepcopy(crel)
  for v in setdiff(vlabel(S),vlabel(c)) ∪ setdiff(elabel(S),elabel(c))
    rem_parts!(crel, v, parts(crel, v))
  end
  return crel
end

"""
Add 
"""
add_eqs!(S::Sketch, eqs) = [add_eq!(S::Sketch, pth) for pth in eqs]
function add_eq!(S::Sketch, pths)
  root = src(S, first(first(pths)))
  S.eqs[root] = reorder_dag(quotient_eqgraph(add_eq!(S.eqs[root], 1, S.schema, pths)...))
end

# Don't yet know if this stuff will be used
##########################################
"""List of arrows between two sets of vertices"""

function hom_set(S::LGraph, d_symbs, cd_symbs)::Vector{Symbol}
  symbs = [d_symbs, cd_symbs]
  d_i, cd_i = [vcat(incident(S, x, :vlabel)...) for x in symbs]
  e_i = setdiff(
        (vcat(incident(S, d_i, :src)...)
        ∩ vcat(incident(S, cd_i, :tgt)...)),
        refl(S) )
  return S[e_i, :elabel]
end

hom_in(S::LGraph, t::Symbol) = hom_set(S, S[:vlabel], [t])
hom_out(S::LGraph, t::Symbol) = hom_set(S, [t], S[:vlabel])
hom_in(S::LGraph, t::Vector{Symbol}) = vcat([hom_in(S,x) for x in t]...)
hom_out(S::LGraph, t::Vector{Symbol}) = vcat([hom_out(S,x) for x in t]...)

hom_set(S::Sketch, d_symbs, cd_symbs) = hom_set(S.schema, d_symbs, cd_symbs)
hom_in(S::Sketch, t::Symbol) = hom_in(S.schema, t)
hom_out(S::Sketch, t::Symbol) = hom_out(S.schema, t)
hom_in(S::Sketch, t::Vector{Symbol}) = hom_in(S.schema, t)
hom_out(S::Sketch, t::Vector{Symbol}) = hom_out(S.schema, t)

# TODO:
# Dualization seems like it could be a simple data migration from Sketch to
# itself, swapping Cone and Cocone and all srcs with tgts.

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
  Pair{Int64, Symbol}[(nv(c.d)-i+1 => get(obs, x, x)) for (i, x) in c.legs])

"""Reverse vertex indices"""
function dual(lg::LGraph)
  G = deepcopy(lg)
  n = nv(lg)+1
  set_subpart!(G, :vlabel,reverse(lg[:vlabel]))
  set_subpart!(G, :refl,reverse(lg[:refl]))
  [set_subpart!(G, y,  [n-x for x in lg[y]]) for y in [:src,:tgt]]
  return G
end

"""Flip edge directions. Optionally rename symbols"""
function dualgraph(lg::LGraph, obd::Dict{Symbol, Symbol})
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
  parse_json_acset(LGraph,d["d"]), Symbol(d["apex"]),
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
  Sketch(parse_json_acset(LGraph, p["schema"]),
    cones=[dict_to_cone(d) for d in p["cones"]],
    cocones=[dict_to_cone(d) for d in p["cocones"]],
    eqs=[parse_json_acset(LGraph,e) for e in p["eqs"]])
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
function cone_query(d::LGraph, legs; optimize=false)::StructACSet
  verbose = false
  vars = [Symbol("x$i") for i in nparts(d, :V)]
  typs = ["$x(_id=x$i)" for (i, x) in enumerate(d[:vlabel])]
  bodstr = vcat(["begin"], typs)
  for (i,e) in filter(x->x[1]∉refl(d), collect(enumerate(d[:elabel])))
    s=src(d, i); t=tgt(d,i); push!(bodstr, "$e(src_$e=x$s, tgt_$e=x$t)")
  end
  push!(bodstr, "end")
  com = nv(d) == 1 ? "," : ""
  exstr = "($(join(["$(v)_$i=x$k" for vs in values(vars)
                    for (i, (k,v)) in enumerate(legs)],",") ))"
  ctxstr = "($(join(vcat(["x$i::$x"
                          for (i, x) in enumerate(d[:vlabel])],),","))$com)"
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



# Conversion between Julia structs and above structures
########################################################

"""Sketch -> FinCatPresentation"""
mkFinCatPresentation(S::Sketch) = mkFinCatPresentation(S.schema)

"""Hom(LabeledFinCatCSet) -> Hom(FinCatPresentation)"""
function mkFinFunctorPres(f::ACSetTransformation)
  df, cdf = [dom(f), codom(f)]
  d, cd = mkFinCatPresentation.([df, cdf])
  cdrefl = Dict([v=>id(Ob(FreeSchema, cdf[i,:vlabel]))
                 for (i,v) in enumerate(codom(f)[:refl])])
  cdnonrefl = setdiff(edges(codom(f)), collect(keys(cdrefl)))
  vmap = Dict{Symbol,Symbol}(map(enumerate(collect(f[:V]))) do (i,v)
    df[i,:vlabel] => cdf[v,:vlabel]
  end)
  emap = Dict(map(filter(ie->ie[1] ∉ df[:refl], collect(enumerate(collect(f[:E]))))) do (i, e)
      df[i, :elabel] => get(cdrefl, e, cdf[e, :elabel])
  end)
  return FinFunctor(vmap, Dict{Symbol, Symbol}(emap), d, cd)
end


# Conversion to combinatorial data structures
#############################################

"""Sketch -> LabeledSketchCSet"""
function mkLabeledSketchCSet(S::Sketch)
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

"""Presentation -> Sketch"""
Sketch(P::Presentation) = P |> FinCat |> Sketch
"""FinCatPresentation -> Sketch"""
Sketch(P::FinCatPresentation)  = P |> mkLabeledFinCatCSet |> Sketch
"""LabeledFinCatCSet -> Sketch"""
Sketch(P::LabeledFinCatCSet)  = P |> LabeledSketchCSettoLGraph |> Sketch

"""LabeledSketchCSet -> Sketch"""
function Sketch(S::LabeledSketchCSet)
  vs, es = S[:vlabel], S[:elabel]
  schema = LabeledSketchCSetToLG(S)   # Get schema

  # Get eqs
  eqs = vcat(map(vertices(S)) do v
    d = LGraph()
    cvs, ces = [incident(S, v, f) for f in [:dV, :dE]]
    filter!(e -> S[e,:deMap] ∉ S[:refl], ces)
    add_vertices!(d, collect(S[cvs,[:dvMap,:vlabel]]))
    add_parts!(d, :E, length(ces); elabel=es[S[ces,:deMap]],
              src=[findfirst(==(x),cvs) for x in S[ces,:dSrc]],
              tgt=[findfirst(==(x),cvs) for x in S[ces,:dTgt]])
    diagram_to_eqs(rem_id(d))
  end...)

  # Get (co)cones
  cones, cocones = map([c_vocab, cc_vocab]) do (
        cone, _, _, _, csrc, ctgt, capex, cleg, clegtgt,
        clegedge, c_v,c_e, cvmap, cemap)
    map(parts(S,cone)) do c_id
      cvs, ces = [incident(S,c_id,f) for f in [c_v,c_e]]
      cd = LGraph()
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

# function cocone_to_cset(n::Symbol, schema::LGraph, c::Cone, i::Int)
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

# function eq_to_type(n::Symbol, p::LGraph, x::Symbol)
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
# function cone_to_cset(n::Symbol, schema::LGraph, c::Cone, i::Int)
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
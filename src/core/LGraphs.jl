module LGraphs 

"""
Reflexive graphs with symbols labeling the edges and vertices
"""

export LGraph, add_id, add_id!, rem_id, vlabel, elabel, add_src,
       add_srctgt, pres_to_grph, show_lg, mkFinCatPresentation,
       enum_paths, diagram_to_eqs, eqs_to_diagrams, add_eq!,
       quotient_eqgraph,reorder_dag

using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra, Catlab.Graphics
import Catlab.Graphs: src, tgt, inneighbors, outneighbors, Graph, add_vertex!, add_vertices!
using DataStructures: DefaultDict 

"""Cast anything to Graph"""
function Graph(C::T) where {T<:HasGraph}
  G = Graph()
  copy_parts!(G, C)
  return G
end

"""Methods missing in Catlab: TODO upstream?"""
inneighbors(g::T, v::Int) where {T<:AbstractReflexiveGraph} =
  subpart(g, incident(g, v, :tgt), :src)
outneighbors(g::T, v::Int) where {T<:AbstractReflexiveGraph} =
  subpart(g, incident(g, v, :src), :tgt)

"""A finitely presented category (with designated id edges)"""
@present SchLGraph <: SchReflexiveGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end;
  
@acset_type LGraph_(SchLGraph, index=[:src,:tgt,:vlabel,:elabel]) <: AbstractReflexiveGraph
const LGraph = LGraph_{Symbol}

  
# LGraph utilities 
########################
show_lg(x::LGraph) = to_graphviz(x; node_labels=:vlabel, edge_labels=:elabel)

"""Default name for id edge"""
add_id(x::Symbol) = Symbol("id_$x")
rem_id(x::String) = x[4:end] # assumes add_id(x::Symbol) = "id_$x"

function add_id!(G::LGraph)
  for v in vertices(G)
    if G[v, :refl] == 0
      e = add_edge!(G, v, v; elabel=add_id(G[v,:vlabel]))
      set_subpart!(G, v, :refl, e)
    end
  end
  return G
end

function rem_id(G::LGraph)
  newG = LGraph()
  copy_parts!(newG, G; V=vertices(G), E=non_id(G))
  return newG
end

src(G::LGraph, f::Symbol) = G[only(incident(G, f, :elabel)), :src]
tgt(G::LGraph, f::Symbol) = G[only(incident(G, f, :elabel)), :tgt]
vlabel(G::LGraph) = G[:vlabel]
elabel(G::LGraph) = G[non_id(G), :elabel]
labels(G::LGraph) = vcat(G[:vlabel], elabel(G))
add_src(x::Symbol) = Symbol("src_$(x)")
add_tgt(x::Symbol) = Symbol("tgt_$(x)")
add_srctgt(x::Symbol) = add_src(x) => add_tgt(x)
add_cone(x::Int) = Symbol("Cone_$x")
add_cocone(x::Int) = Symbol("Cocone_$x")
add_path(n::Symbol, x::Symbol) = Symbol("$(n)_Path_$x")
add_path(i::Int) = Symbol("P$i")
add_pathrel(i::Int) = (Symbol("R_$i"), add_srctgt(Symbol("R_$i"))...)
function add_vertex!(G::LGraph, v::Symbol) 
  vi = add_vertex!(G; vlabel=v)
  G[G[vi,:refl], :elabel] = add_id(v)
  return vi
end
add_vertices!(G::LGraph, xs::Vector{Symbol}) = [add_vertex!(G,x) for x in xs]


elabel(G::LGraph, st::Bool) =
  collect(zip([G[non_id(G), x] for x in
    [:elabel, [:src,:vlabel], [:tgt,:vlabel]]]...))
non_id(G::LGraph) = setdiff(edges(G), G[:refl]) |> collect |> sort

# Graphs as Path Equations 
##########################

"""
Find all paths in a DAG
Return a dictionary with (src,tgt) keys and a list of paths between them
"""
function enum_paths(G::HasGraph)
  ep = enumerate_paths(Graph(G))
  return Dict(map(collect(Iterators.product(vertices(G),vertices(G)))) do (i,j)
    (i,j) => ep[incident(ep, i, :src) ∩ incident(ep, j, :tgt), :eprops]
  end)
end

"""
Interpret the labeled graph DAG as a commutative diagram and return the 
pairs of paths (as lists of labels) that have same src/tgt
"""
function diagram_to_eqs(g::LGraph)
  rg = rem_id(g)
  map(filter(x->length(x)>1, collect(values(enum_paths(rg))))) do ps
    [rg[p,:elabel] for p in ps]
  end
end


"""Add path to commutative diagram without repeating information"""
function add_path!(schema::LGraph, lg::LGraph, p::AbstractVector{Symbol},
                  all_p::Dict{Vector{Symbol}, Int},
                  eqp::Union{Nothing, AbstractVector{Symbol}}=nothing,
                   )
  s = only(incident(schema, first(p), :elabel))
  for i in 1:length(p)
    if !haskey(all_p, p[1:i])
      e = only(incident(schema, p[i], :elabel))
      t = schema[e, [:tgt,:vlabel]]
      if isnothing(eqp) || i < length(p)
        new_v = add_vertex!(lg, t)
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
Add a path to a graph given a list of (edgename, tgtname)
Start at designated root and return the index of the final vertex
"""
function add_path!(lg::LGraph, root::Int,
                   p::AbstractVector{Pair{Symbol,Symbol}})::Int
  i = root
  for (k,v) in p 
    i_new = add_vertex!(lg, v)
    add_edge!(lg, i, i_new; elabel=k)
    i = i_new
  end
  return i
end

"""Adds an equation to a labeled graph and returns the new graph + root"""
function add_eq!(lg::LGraph, root::Int, schema, ps_::Vector{Vector{Symbol}})::Pair{LGraph, Int}
  ps = add_tgt_to_pths(schema, ps_)
  ends = [add_path!(lg, root, p) for p in ps]
  endtype = last(last(first(ps)))
  n = length(ps)
  apx,foot = [add_id!(@acset(LGraph, begin V=N; vlabel=fill(endtype,N) end)) for N in [n,1]]
  l = homomorphism(apx,lg;initial=(V=ends,))
  r = homomorphism(apx,foot)
  h, _ = pushout(l,r)
  return codom(h) => h[:V](root)
end

"""Remove equivalent paths from a starting root node. BFS search."""
function quotient_eqgraph(lg::LGraph, root::Int)
  d = DefaultDict{Vector{Symbol}, Vector{Int}}(()->Int[])
  queue = [Symbol[]=>root]
  while !isempty(queue)
    p, v = pop!(queue)
    for e in setdiff(incident(lg, v, :src), [refl(lg,v)])
      lab, nxt = lg[e, :elabel], lg[e,:tgt]
      nxtp = vcat(p,[lab])
      push!(d[nxtp], nxt)
      push!(queue, nxtp=>nxt)
    end
  end
  apx, foot = LGraph(), LGraph()
  apxV, footV = Int[], Int[]
  for vs in filter(v -> length(v) > 1, values(d)|>collect)
    vlab = lg[first(vs),:vlabel]
    add_vertices!(apx, fill(vlab,length(vs)))
    fv = add_vertex!(foot, vlab)
    append!(apxV, vs); append!(footV, fill(fv, length(vs)))
  end
  l = homomorphism(apx, lg; initial=(V=apxV,))
  r = homomorphism(apx, foot; initial=(V=footV,))
  res = apex(pushout(l,r))
  # remove parallel arrows w same fk
  to_del = Int[]
  for s in vertices(res)
    e_ = incident(res, s, :src)
    for t in vertices(res)
      es = incident(res, t, :tgt) ∩ e_
      for l in unique(res[es,:elabel])
        el = findall(==(l), res[es,:elabel])
        append!(to_del, es[el[2:end]])
      end
    end
  end
  rem_parts!(res, :E, sort(to_del))
  return res
end

"""
Return an isomorphic graph such that vertex order is topologically sorted
"""
function reorder_dag(lg::LGraph)::LGraph
  lg = deepcopy(lg)
  ord = topological_sort(rem_id(lg))
  set_subpart!(lg, :vlabel, vlabel(lg)[ord])
  lg[:refl] = lg[:refl][ord]
  for x in [:src,:tgt] 
    lg[x] = [findfirst(==(v), ord) for v in lg[x]]
  end
  return lg
end


"""
Get per-object diagrams encoding all commutative diagrams which start at that
point, using the information of pairwise equations

eqs:: Vector{Tuple{Symbol, Vector{Symbol}, Vector{Symbol}}}
"""
function eqs_to_diagrams(schema::LGraph, eqs)
  # initialize commutative diagrams + their roots
  lgs = [add_id!(@acset(LGraph, begin V=1;vlabel=[v] end))=>1 for v in vlabel(schema)]
  for eq in eqs
    i = src(schema, first(first(eq)))
    # upgrade path eqs to include morphism codomain info
    lgs[i] = add_eq!(lgs[i]...,schema, Vector{Vector{Symbol}}(eq))
  end

  Dict(zip(vlabel(schema),[reorder_dag(quotient_eqgraph(x...)) for x in lgs]))
end

function add_tgt_to_pths(schema,pths)::Vector{Vector{Pair{Symbol,Symbol}}}
  map(pths) do p 
    map(p) do e 
      e=>schema[tgt(schema, e),:vlabel]
    end
  end
end

# Conversion to Julia structs 
#############################
function mkFinCatPresentation(S::LGraph)
  p = Presentation(FreeSchema)
  vs = Dict([v=>add_generator!(p, Ob(FreeSchema, v)) for v in vlabel(S)])
  for (e,s,t) in elabel(S,true)
    add_generator!(p, Hom(e, vs[s],vs[t]))
  end
  return FinCat(p)
end

# Conversion to combinatorial data structures
#############################################
"""Presentation -> LGraph"""
function pres_to_grph(p::Presentation)::LGraph
  g = LGraph()
  for v in p.generators[:Ob] add_part!(g, :V; vlabel=Symbol(v)) end
  for e in p.generators[:Hom]
    add_edge!(g, only(incident(g,Symbol(dom(e)), :vlabel)),
                  only(incident(g,Symbol(codom(e)), :vlabel));
                  elabel=Symbol(e))
  end
  return g
end
  

end # module 

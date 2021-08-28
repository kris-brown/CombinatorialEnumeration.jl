using Catlab.CategoricalAlgebra
using Catlab.Present
using Catlab.Theories
using Catlab.WiringDiagrams
using Catlab.Programs
using Catlab.Programs.RelationalPrograms: parse_relation_context, parse_relation_call

using Catlab.CategoricalAlgebra.FinSets
using Catlab.CategoricalAlgebra.CSetDataStructures: AttributedCSet
using DataStructures: IntDisjointSets, find_root!, in_same_set
using Dates

struct Schema
  arities::Dict{Symbol, Int}
end

ids = x -> Symbol("id_$x")
arg = (x, y) -> Symbol("$(x)_$y")

"""
We can slightly complicate this by splitting V up into an object for each color
and arities can be a list of symbols.
"""
function schema_to_csettype(sch::Schema)
  pres = Presentation(FreeSchema)

  Id, Name = [FreeSchema.Data{:generator}([x], []) for x in [:Id, :Name]]
  add_generator!(pres, Id)
  add_generator!(pres, Name)

  relobs = [Ob(FreeSchema, s) for s in keys(sch.arities)]
  vob = Ob(FreeSchema, :V)

  add_generator!(pres, vob)
  add_generator!(pres, FreeSchema.Attr{:generator}([:id_V, vob, Id], [vob, Id]))
  add_generator!(pres, FreeSchema.Attr{:generator}([:sort, vob, Name], [vob, Name]))

  for x in relobs
    add_generator!(pres, x)
    add_generator!(pres, FreeSchema.Attr{:generator}(
      [ids(x.args[1]), x, Id], [x, Id]))
  end

  for (n, (s, a)) in enumerate(sch.arities)
    relob = relobs[n]
    for src_sym in 1:a
      add_generator!(pres, Hom(arg(s,src_sym), relob, vob))
    end
  end

  cset = ACSetType(pres, unique_index=vcat([:id_V],
                   map(ids, collect(keys(sch.arities)))))
  return ACSetType(pres){Int, Symbol}, cset{Int, Symbol}
end

"""
Dependency: When the body pattern is seen, the result pattern is asserted to
exist and eqs hold between subsets of the body variables.
"""
struct Dep
  name :: Symbol
  body :: ACSet
  res :: ACSet
  eqs :: Set{Set{Int}}
end

function Dep(name::Symbol, body::ACSet,res::ACSet)::Dep
  return Dep(name, body,res,Set{Set{Int}}())
end

mutable struct Sequence{State,Params}
  state::State
  params::Params
  func::Function
end

"""
Give a sequence of rules to run. The last iteration of rules will be repeated.
"""
function seq(s::Vector{Vector{Symbol}})::Function
  !isempty(s) || error("s cannot be empty")
  function f(Σ, i, _, _, _)
    ds = s[min(i, end)]
    return isempty(ds) ? Σ : [getdep(Σ, d) for d in ds]
  end
  return f
end



allseq = seq([Symbol[]])

function sizes(x::ACSet{CD}) where {CD}
  [o=>nparts(x,o) for o in ob(CD)]
end

getdep(Σ::Set{Dep}, name::Symbol)::Dep = only([d for d in Σ if d.name==name])


function maxes(x::ACSet{CD})::Dict{Symbol, Int} where {CD}
  Dict([o => max0(x[ids(o)]) for o in ob(CD)])
end

function merge_maxes(d1::Dict{Symbol, Int},
                     d2::Dict{Symbol, Int})::Dict{Symbol, Int}
  Dict([o => max(d1[o], d2[o]) for o in keys(d1)])
end

Base.isempty(dI::ACSet) = sum(nparts(dI, o)
  for o in filter(!=(:V), ob(typeof(dI).parameters[1]))) == 0

"""Adds content of y to x"""
function addstuff!(X::ACSet{CD}, Y::ACSet{CD})::Nothing where {CD}
  xids = Set(X[:id_V])
  xmap = Int[]
  for (vi, vsrt) in Y.tables[:V]
    if vi ∈ xids
      nxt = only(incident(X, vi, :id_V))
    else
      nxt = add_part!(X, :V, id_V=vi, sort=vsrt)
    end
    push!(xmap, nxt)
  end
  mxs= maxes(X)
  for o in filter(!=(:V), ob(CD))
    oseen = Set([collect(r)[1:end-1] for r in X.tables[o]])
    for r in Y.tables[o]
      cr = collect(r)
      newx = xmap[cr[1:end-1]]
      if newx ∉ oseen
        push!(oseen, newx)
        push!(newx, cr[end]+mxs[o])
        add_part!(X, o; Dict(zip(keys(r), newx))...)
      end
    end
  end
  return nothing
end

function Base.union(x::ACSet{CD}, y::ACSet{CD})::ACSet{CD} where {CD}
  if nparts(x, :V) == 0 return y
  elseif nparts(y,:V) ==0 return x
  end

  overlap = AttributedCSet{typeof(x).parameters...}()
  o_ids = Dict([let s = ids(o); o=>collect(x[s] ∩ y[s]) end
                for o in ob(CD)])
  o_indexes = filter(x->!isempty(x[2]), [o => vcat(incident(x, v, ids(o))...)
               for (o, v) in collect(o_ids)])
  if !isempty(o_indexes)
    copy_parts!(overlap, x; Dict(o_indexes)...)
  end
  inexact = collect(filter(!=(:id_V), map(ids, ob(CD))))
  fx = homomorphism(overlap,x)
  fy = homomorphism(overlap,y, inexact=inexact)
  !(fx===nothing) || error("overlap $overlap x $x")
  !(fy===nothing) || error("overlap $overlap y $y")
  res = apex(pushout(fx,fy))
  trim!(res)
  return res
end

function unionfind_to_dict(d::IntDisjointSets, idvec::Vector{Int})::Dict{Int,Int}
  dic, mins = Dict{Int, Int}(), Set{Int}()
  for i in 1:length(d)
    iid = idvec[i]
    for m in mins
      if in_same_set(d, i, m)
        dic[iid] = idvec[m]
        break
      end
    end
    if !haskey(dic, iid)
      push!(mins, i)
    end
  end
  return dic
end
"""
Apply a mapping to a DB instance. The mapping refers to V id's. {a ↦ b}
collapses the vertex identified by `a` into the vertex identified by `b`.
If `b` is not found in the DB instance, a vertex gets created for it.
"""
function appdict(d::Dict{Int,Int}, I::ACSet{CD})::ACSet{CD} where {CD}
  I_ = deepcopy(I)
  seenV = Set{Int}()
  for o in filter(!=(:V), ob(CD))
    del_list, seen = Int[], Set()
    for (i, r) in enumerate(I.tables[o])
      for (k, v) in filter(x->x[1]!=ids(o), collect(zip(keys(r), r)))
        v_id = I_[:id_V][v]
        new_v_id = get(d, v_id, v_id)
        new_v_ = incident(I_, new_v_id, :id_V)
        new_v = (isempty(new_v_)
                ? add_part!(I_, :V, id_V=new_v_id, sort=I_[:sort][v])
                : only(new_v_))
        push!(seenV, new_v)
        set_subpart!(I_, i, k, new_v)
      end
      new_r = collect(I_.tables[o][i])[1:end-1]
      if new_r in seen
        push!(del_list, i)
      else
        push!(seen, new_r)
      end
    end
    rem_parts!(I_, o, del_list)
  end
  rem_parts!(I_, :V, sort(collect(setdiff(parts(I_, :V), seenV))))
  return I_
end

function appdict!(d::Dict{Int,Int}, I::ACSet{CD})::Nothing where {CD}
  seenV = Set{Int}()
  for o in filter(!=(:V), ob(CD))
    del_list, seen = Int[], Set()
    for (i, r) in enumerate(I.tables[o])
      for (k, v) in filter(x->x[1]!=ids(o), collect(zip(keys(r), r)))
        v_id = I[:id_V][v]
        new_v_id = get(d, v_id, v_id)
        new_v_ = incident(I, new_v_id, :id_V)
        new_v = (isempty(new_v_)
                ? add_part!(I, :V, id_V=new_v_id, sort=I[:sort][v])
                : only(new_v_))
        push!(seenV, new_v)
        set_subpart!(I, i, k, new_v)
      end
      new_r = collect(I.tables[o][i])[1:end-1]
      if new_r in seen
        push!(del_list, i)
      else
        push!(seen, new_r)
      end
    end
    rem_parts!(I, o, del_list)
  end
  rem_parts!(I, :V, sort(collect(setdiff(parts(I, :V), seenV))))
  return nothing
end

appdict(d::Dict{Int,Int}, v::Vector{Int})::Vector{Int} = [get(d, x, x) for x in v]

max0 = x -> isempty(x) ? 0 : maximum(x)


"""Offset IDs componentwise"""
function offset(I::ACSet{CD}, maxes::Dict{Symbol, Int})::ACSet{CD} where {CD}
  res = deepcopy(I)
  for o in ob(CD)
    atr, off = ids(o), maxes[o]
    for i in sort(res[atr], rev=true)
      set_subpart!(res, only(incident(res, i, atr)), atr, i + off)
    end
  end
  return res
end

"""Creates a new version of add_on with fresh ids
I - a base that will have y added to it
mapping - a subset of node IDs in add_on are mapped to IDs in I
add_on - a pattern that will be added to I
"""
function fresh(mapping::Dict{Int,Int},
               add_on::ACSet{CD}, mxs::Dict{Symbol, Int})::ACSet where {CD}
  new_add_on1 = offset(add_on, mxs)
  μ = Dict([k+mxs[:V]=>v for (k, v) in pairs(mapping)])
  new_add_on2 = appdict(μ, new_add_on1)
  trim!(new_add_on2)
  return new_add_on2
end


"""Remove nodes that appear in no tuples. Remove duplicate tuples."""
function trim!(I::ACSet{CD})::Nothing where {CD}
  keep_v = Set{Int}()
  for o in filter(!=(:V), ob(CD))
    del_list, seen = Int[], Set()
    for (i, r) in enumerate(I.tables[o])
      vs = collect(r)[1:end-1]
      if vs in seen
        push!(del_list, i)
      else
        push!(seen, vs)
        union!(keep_v, vs)
      end
    end
    rem_parts!(I, o, del_list)
  end
  del_v = sort(collect(setdiff(parts(I, :V), keep_v)))
  rem_parts!(I, :V, del_v)
  return nothing
end

# function Base.iterate(IΣ::restricted_chase)::Tuple{Tuple{ACSet, Dict{Int,Int}}, chase_state}
#   iterate(IΣ, chase_state(IΣ.I, IΣ.I, 1))
# end

# function Base.iterate(IΣ::core_chase)::Tuple{Tuple{ACSet, Dict{Int,Int}}, core_chase_state}
#   iterate(IΣ, core_chase_state(IΣ.I, 1, Dict([k.name=>Dict([o=>Set{Int}()
#      for o in IΣ.It.body.body.parameters[1].parameters[1]]) for k in IΣ.Σ]), false))
# end


"""
Terminate determines how many chase iterations to do.
Sequence determines what dependencies to trigger each iteration
"""
function core_chase(I::ACSet{CD}, Σ::Set{Dep}, Select::Function=allseq,
                    Terminate::Function=(_,_,_,_)->false, maxi::Int=3) where {CD}
  m, seen = Dict{Int,Int}(), Dict{Symbol, Dict{Symbol, Set{Int}}}([
    d.name=>Dict([o=>Set{Int}() for o in ob(CD)]) for d in Σ])
  for i in 1:maxi
    println("--------Iteration $i--------")
    μ, N = IntDisjointSets(nparts(I, :V)), ACSet{typeof(I).parameters...}()
    for τ in Select(Σ, i, I, N, μ)
      core_apply_trigger!(I, τ, seen[τ.name], N, μ)
    end
    m = unionfind_to_dict(μ, I[:id_V])
    appdict!(m, I)
    appdict!(m, N)
    addstuff!(I, N)
    # I = findcore(I; loose=true)
    if Terminate(I, N, m, i)
      return (I, m)
    end
  end
  return (I, m)
end

# function Base.iterate(IΣ::restricted_chase, state::Union{Nothing,chase_state}
#                       )::Union{Nothing, Tuple{Tuple{ACSet, Dict{Int,Int}}, chase_state}}
#   if isempty(state.dI) # Termination condition
#     return nothing
#   else # Normal unpacking of state
#     I, ∆I, counter, s = state.I, state.dI, state.counter, IΣ.S
#     N, μ = IΣ.It() , IntDisjointSets(nparts(I, :V))
#   end
#   ∆I = I # until we figure out how to do triggerwise-∆I
#   println("counter $counter")
#   while true
#     τ = select(s, IΣ.Σ, counter, I, ∆I, N, μ)
#     if τ===nothing break end
#     N, μ =  apply_trigger(I, τ, ∆I, N, μ)
#   end
#   m = unionfind_to_dict(μ, I[:id_V])
#   I, ∆I = update_inst(I, ∆I, N, m)
#   return (I, m), chase_state(I, ∆I, counter+1) # output, new_state
# end
# Base.IteratorSize(::restricted_chase) = Base.IsInfinite()
# Base.IteratorSize(::core_chase) = Base.IsInfinite()

apply_trigger(I::ACSet, τ::Dep)=apply_trigger(
  I, τ, I, ACSet{typeof(I).parameters...}(), IntDisjointSets(nparts(I, :V)))

function update_inst(I::ACSet, ∆I::ACSet, N::ACSet, μ::Dict{Int,Int})
  ∆I = appdict(μ, N) # TODO understand what line 14 means
  # prune!(∆I, setdiff(Set(N[:id_V]), Set(I[:id_V])))
  I = union(appdict(μ, I), ∆I)
  return I, ∆I
end

# function apply_trigger(I::ACSet, τ::Dep, ∆I::ACSet, N::ACSet, μ::IntDisjointSets)
#   print("applying $(τ.name)")
#   q, ps = tgd_relation(τ.body,  Dict{Int,Int}())
#   trigs = (isempty(τ.body) ? [NamedTuple()] : query(I, q, ps))
#   println("$(length(trigs)) potential triggers")
#   for (i, trig) in enumerate(trigs)
#     print("$i ")
#     #println("potential trigger in I $trig")
#     # make sure trigger at least somewhat pertains to the 'unknown' subset of I
#     d = zip([parse(Int, string(k)[2:end]) for k in keys(trig)], trig)
#     d2 = Dict{Int,Int}([k=>I[:id_V][v] for (k,v) in d])

#     # ACTUALLY we should check that any of the relations intersect,
#     # not the vertices (?) Would require change to output of query. TODO
#     if isempty(τ.body) || !isempty(intersect(values(d2), ∆I[:id_V]))
#       # print("[relevant trigger]")
#       # Quotient by equivalences
#       for eqset in τ.eqs
#         eqids = [only(incident(I, d2[x], :id_V)) for x in eqset]
#         # println("unioning $eqids")
#         for (x, y) in zip(eqids, eqids[2:end])
#           union!(μ, x, y)
#         end
#       end

#       # Add to graph if needed
#       if nparts(τ.res, :V) > 0
#         q, ps = tgd_relation(τ.res, d2)
#         uI = appdict(unionfind_to_dict(μ, I[:id_V]), I ∪ N)
#         if isempty(query(uI, q, ps))  # THIS SHOULD JUST BE A IS_HOMOMORPHIC CHECK
#           # println("active tgd trigger w/ $d2")
#           newstuff = fresh(d2, τ.res, merge_maxes(maxes(N), maxes(I)))
#           # println("newstuff $newstuff")
#           N = N ∪ newstuff
#         end
#       end
#     end
#   end
#   println("")
#   return N, μ
# end

function core_apply_trigger!(I::ACSet{CD}, τ::Dep, seen::Dict{Symbol, Set{Int}},
                             N::ACSet, μ::IntDisjointSets)::Nothing where {CD}
  print("applying $(τ.name) on I = $(sizes(I)) and N = $(sizes(N))")
  strt = now()
  q, ps = tgd_relation(τ.body, Dict{Int,Int}())
  trigs = (isempty(τ.body) ? [NamedTuple()] : query(I, q, ps))
  println("$(length(trigs)) potential triggers (query time $(now()-strt))")
  strt = now()
  for (i, trig) in enumerate(trigs)
    #print("$i ")
    # make sure trigger at least somewhat pertains to the 'unknown' subset of I
    unseen = false
    d2 = Dict{Int,Int}()

    for (k, v) in zip(keys(trig), trig)
      ostr, istr = split(string(k), "__")
      o, i = Symbol(ostr), parse(Int, istr)
      idv = I[ids(o)][v]
      if o == :V
        d2[i] = I[:id_V][v]
        if !unseen
          for vid in I[:id_V]
            if in_same_set(μ, idv, vid) && idv ∉ seen[:V]
              unseen = true
              break
            end
          end
        end
      elseif !unseen && idv ∉ seen[o]
        unseen = true
      end
    end
    if isempty(τ.body) || unseen
      # print(" [relevant] ")
      # Quotient by equivalences
      for eqset in τ.eqs
        eqids = [only(incident(I, d2[x], :id_V)) for x in eqset]
        # print(" unioning $eqids ")
        for (x, y) in zip(eqids, eqids[2:end])
          union!(μ, x, y)
        end
      end
      #ttest = appdict(d2, τ.res)
      resids = Set(τ.res[:id_V])
      init = (V=Dict([(first(incident(τ.res, k, :id_V)) =>
                       first(incident(I, v, :id_V)))
                      for (k,v) in pairs(d2) if k ∈ resids]),)
      inex = collect(map(ids, ob(CD)))
      if !is_homomorphic(τ.res, I, initial=init, inexact=inex)
        # Add to graph if needed
        if nparts(τ.res, :V) > 0
          newstuff = fresh(d2, τ.res, merge_maxes(maxes(N), maxes(I)))
          # println("new V ids $(sort(collect(setdiff(newstuff[:id_V], I[:id_V]))))")
          addstuff!(N, newstuff)
        end
      end
    end
  end
  println("time: $(now()-strt)")
  return nothing
end

"""
Given a DB inst as a pattern, create a conjunctive query that returns its
matches. Optionally constrain particular vertices to have particular IDs.
"""
function tgd_relation(X::ACSet{CD}, bound::Dict{Int,Int})::Tuple{UndirectedWiringDiagram, NamedTuple} where {CD}
  vars = Dict([o=>[Symbol("$(o)__$i") for i in X[ids(o)]] for o in ob(CD)])
  typs = ["V(_id=$i, sort=s$i)" for i in vars[:V]]
  params = Set(["s$i=:$n" for (i, n) in zip(vars[:V], X[:sort])])
  bodstr = vcat(["begin"], typs)
  for (k, v) in collect(bound)
    bound_ind = findfirst(==(k), X[:id_V])
    if !(bound_ind===nothing)
      push!(bodstr, "V(_id=$(vars[bound_ind]),id_V=i$v)")
      push!(params, ("i$v=$v"))
    end
  end
  for o in filter(!=(:V), ob(CD))
    for row in X.tables[o]
      is = collect(enumerate(collect(row)))
      _, oid = pop!(is)
      push!(bodstr, "$o(_id=$(o)__$oid,$(join(["$(arg(o,i))=$(vars[:V][v])"
                                for (i, v) in is],",")))")
    end
  end
  push!(bodstr, "end")
  exstr = "($(join(["$v=$v" for vs in values(vars) for v in vs],",") ))"
  ctxstr = "($(join(vcat(
    ["s$v::Symbol" for v in vars[:V]],
    ["$v::$k" for (k, vs) in pairs(vars) for v in vs],
    collect(Set(["i$v::Int" for v in values(bound)]))
    ),",")))"
  pstr = "($(join(params,",")),)"
  ex  = Meta.parse(exstr)
  ctx = Meta.parse(ctxstr)
  hed = Expr(:where, ex, ctx)
  bod = Meta.parse(join(bodstr, "\n"))
  # println("ex $exstr\n ctx $ctxstr\n bod $bodstr\n params $pstr")
  ps = isempty(bound) ? NamedTuple() : eval(Meta.parse(pstr))
  res = parse_relation_diagram(hed, bod)
  # Remove isolated junctions
  iso = setdiff(parts(res, :Junction), res[:junction])
  isempty(iso ∩ res[:outer_junction]) || error("$res")
  rem_parts!(res, :Junction, iso)
  return res, ps
end

function findcore(I::ACSet{CD}; loose::Bool=false)::ACSet{CD} where {CD}
  println("STARTING CORE SEARCH")
  strt = now()
  inexact = collect(filter(!=(:id_V), map(ids, ob(CD))))

  hs = [h.components[:V].func for h in (loose
          ? [homomorphism(I, I, inexact=inexact)]
          : homomorphisms(I, I, inexact=inexact))]
  minh = sort(hs, by=x->length(Set(x)))[1]
  μ = Dict(zip(I[:id_V], I[:id_V][minh]))
  res = appdict(μ, I)
  println(map(sizes, [I, res]))
  println("core dt = $(now()-strt)")
  return res
end

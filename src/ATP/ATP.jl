using Catlab.WiringDiagrams
using Catlab.Present
using Catlab.Theories
using Catlab.CategoricalAlgebra.CSets
using Catlab.CategoricalAlgebra.StructuredCospans
using Catlab.Present: translate_generator
using Catlab.CategoricalAlgebra.FinSets
using Catlab.Theories: attr, adom
using Catlab.CategoricalAlgebra.DPO
using Catlab.CategoricalAlgebra.DPO: rewrite_match_data

using AutoHashEquals
using DataStructures: IntDisjointSets, find_root, in_same_set

WD = WiringDiagram#{Any,Any,Any,Any}
WDPair = Pair{WiringDiagram{Any,Any,Any,Any},
        WiringDiagram{Any,Any,Any,Any}}
include(joinpath(@__DIR__,"Chase.jl"))

"""
Stick a junction in pass through wires
"""
function passthru_fix!(wd::WiringDiagram)::Nothing
  d = wd.diagram
  for pt in parts(d, :PassWire)
    i = d[:pass_src][pt]
    b = add_box!(wd, Junction(d[:outer_in_port_type][i], 1, 1))
    add_wires!(wd, [(input_id(wd), i) => (b,1),
            (b,1) => (output_id(wd), d[:pass_tgt][pt])])
  end
  rem_parts!(d, :PassWire, parts(d, :PassWire))
  return nothing
end

@auto_hash_equals struct Eq
  name::Symbol
  l::WiringDiagram
  r::WiringDiagram
  rev::Bool
  function Eq(n,l,r,v)
    for ext in [:OuterInPort, :OuterOutPort]
      err = "$n has different # of $ext in left and right patterns"
      @assert nparts(l.diagram, ext) == nparts(r.diagram, ext) err
    end
    map(passthru_fix!, [l, r])
    map(add_junctions!, [l, r])
    #check_wd(l, "$n: Left\n")
    #check_wd(r, "$n: Left\n")
    return new(n,l,r,v)
  end
end
Eq(n,l,r) = Eq(n,l,r,true)
function Base.isless(x::Eq, y::Eq)::Bool
  return Base.isless(x.name, y.name)
end
flip(x::Eq)::Eq = x.rev ? Eq(Symbol("$(x.name)_rev"), x.r, x.l, x.rev) : error("Cannot flip $(x.name)")


"""
"""
struct EqTheory
  gens :: Set{Box{Symbol}}
  eqs :: Set{Eq}
  function EqTheory(gs::Set{Box{Symbol}}, es::Set{Eq})
    es = deepcopy(es)
    esyms = Set{Symbol}()
    for eq in es
      check_eq(gs, eq)
      push!(esyms, eq.name)
    end
    # Create total intro and singlevalued axioms for each gen if not in e
    for gen in gs
      si, ss = [Symbol(string(gen.value)*x) for x in ["_intro", "_sv"]]
      si in esyms || push!(es, intro_rule(gen))
      ss in esyms || push!(es, singlevalued_rule(gen))
    end
    return new(gs,es)
  end
end
function Base.show(io::IO, ::MIME"text/plain", t::EqTheory)
  println("generators: $(join([g.value for g in t.gens], " "))")
  println("equations: $(join([eq.name for eq in t.eqs], " "))")
end
ϵ_box(x::Symbol) = Junction(x, 1, 0)
δ_box(x::Symbol) = Junction(x, 1, 2)
μ_box(x::Symbol) = Junction(x, 2, 1)

function intro_rule(gen::Box{Symbol})::Eq
  l, r = [WiringDiagram(gen.input_ports, Symbol[]) for _ in 1:2]
  rb = add_box!(r, gen)
  for (i, typ) in enumerate(gen.input_ports)
    b = add_box!(l, ϵ_box(typ))
    add_wire!(l, (input_id(l), i)=>(b,1))
    add_wire!(r, (input_id(r), i)=>(rb,i))
  end
  for (i, typ) in enumerate(gen.output_ports)
    b = add_box!(r, ϵ_box(typ))
    add_wire!(r, (rb, i)=>(b, 1))
  end
  return Eq(Symbol(string(gen.value)*"_intro"), l, r, false)
end

function singlevalued_rule(gen::Box{Symbol})::Eq
  op = gen.output_ports
  no = length(op)
  l, r = [WiringDiagram(gen.input_ports, [op...,op...]) for _ in 1:2]
  lb1, lb2 = add_boxes!(l, [gen, gen])
  rb = add_box!(r, gen)

  for (i, typ) in enumerate(gen.input_ports)
    lδ = add_box!(l, δ_box(typ))
    add_wires!(l, Pair[
      (input_id(l), i)=>(lδ,1),
      (lδ, 1) => (lb1, i),
      (lδ, 2) => (lb2, i)])
    add_wire!(r, (input_id(r), i)=>(rb,i))
  end
  for (i, typ) in enumerate(op)
    rδ = add_box!(r, δ_box(typ))
    add_wires!(r, Pair[
      (rb, i)=>(rδ,1),
      (rδ, 1) => (output_id(r), i),
      (rδ, 2) => (output_id(r), i+no)])
    add_wires!(l, Pair[
      (lb1,i)=>(output_id(l), i),
      (lb2,i)=>(output_id(l), i+no)])
    end

  return Eq(Symbol(string(gen.value)*"_sv"), l, r, false)

end

"""

"""
function check_eq(Σ::Set{Box{Symbol}}, e::Eq)::Nothing
  for s in [:outer_in_port_type, :outer_out_port_type]
    e.l.diagram[s] == e.r.diagram[s] || error("Interfaces of $e don't match")
  end
  Σd = Dict{Symbol, Pair{Vector{Symbol}, Vector{Symbol}}}([
    b.value => (b.input_ports => b.output_ports) for b in Σ])
  check_wd(Σd, e.l, "$(e.name) left")
  check_wd(Σd, e.r, "$(e.name) left")
end
"""
Check that all terms in eqs are built from generators in gens / have
the right arity
"""
function check_wd(Σ::Dict{Symbol, Pair{Vector{Symbol},Vector{Symbol}}},
          wd::WD, err::String)::Nothing
  for b in boxes(wd)
    if haskey(Σ, b.value)
      ps = b.input_ports => b.output_ports
      e = err * "Wd $wd Box $b has mismatch with signature $Σ"
      ps == Σ[b.value] || error(e)
    else
      e = err * "Wd $wd Unknown box symbol $(b.value) for $Σ"
      b isa Junction || error(e)
    end
  end
end

function Base.union(t1::EqTheory, t2::EqTheory)::EqTheory
  return EqTheory(union(t1.gens, t2.gens), union(t1.eqs, t2.eqs))
end

function Base.union(t1::EqTheory, gens::Set{Box{Symbol}}, eqs::Set{Eq})::EqTheory
  return EqTheory(union(t1.gens, gens), union(t1.eqs, eqs))
end

function add_eq(t::EqTheory, eqs...)::EqTheory
  return EqTheory(t.gens, union(t.eqs, eqs))
end

function Base.getindex(t::EqTheory, x::Symbol)::Eq
  for eq in t.eqs
    if eq.name == x
      return eq
    end
  end
  throw(KeyError(x))
end


"""
Defined only for monic morphisms
"""
function invert(x::ACSetTransformation)::ACSetTransformation
  function invert_comp(s::Symbol)::Vector{Int}
    res = Int[]
    for i in 1:nparts(codom(x), s)
      v = findfirst(==(i), collect(x.components[s]))
      if v === nothing
        push!(res, 1)
      else
        push!(res, v)
      end
    end
    return res
  end
  d = Dict([s=>invert_comp(s) for s in keys(x.components)])
  return ACSetTransformation(codom(x), dom(x); d...)
end

function δsd(x::Symbol)::WD
  wd = WiringDiagram([x], [x,x])
  add_box!(wd, δ_box(x))
  add_wires!(wd, Pair[
    (input_id(wd), 1) => (1,1),
    (1,1) => (output_id(wd), 1),
    (1,2) => (output_id(wd), 2)])
  return wd
end

function μsd(x::Symbol)::WD
  wd = WiringDiagram([x,x],[x])
  add_box!(wd, μ_box(x))
  add_wires!(wd, Pair[
    (input_id(wd), 1) => (1,1),
    (input_id(wd), 2) => (1,2),
    (1,1) => (output_id(wd), 1)])
  return wd
end

"""
Apply equality as a rewrite rule

repl = replace one side of an equality with the other, as opposed to just
adding the other side to a diagram.

forward = the searched pattern is the `l` side of the Eq

n = expected number of homomorphisms (default of -1 means allow any #)
"""
function apply_eq(sc_cset::ACSet{CD}, T::EqTheory,
          eq::Symbol; forward::Bool=true, repl::Bool=false,
          n::Int=1, monic::Bool=false,
          kw...
         )::ACSet{CD} where {CD}
  println("applying eq $eq to $([(o,nparts(sc_cset,o)) for o in ob(CD)])")
  rule = T[eq]
  partial = Dict{Symbol, Dict{Int,Int}}([k=>Dict(v)
                       for (k, v) in collect(kw)])
  # Orient the rule in the forward or reverse direction, determining which
  # side of the rule is the "L" pattern in the DPO rewrite
  @assert rule.rev || forward "Cannot apply $(rule.name) in reverse direction"
  l, r = map(wd_pad, forward ? (rule.l, rule.r) : (rule.r, rule.l))
  pat,_,Lmap = wd_to_cospan(l, T)[2:4]

  # l is either replaced with merging of l and r or, or just r
  r_, lrmap = repl ? (r, nothing) : branch(l, r)[1:2]
  R_,ccR,Rmap = wd_to_cospan(r_, T)[2:4]

  # Store interface data and then erase it from CSets
  vmap = Pair{Int,Int}[]
  for i in 1:nparts(pat, :_I)
    push!(vmap, pat[:_i][i] => R_[:_i][i])
  end
  for o in 1:nparts(pat, :_O)
    push!(vmap, pat[:_o][o] => R_[:_o][o])
  end
  vmapset = sort(collect(Set(vmap)))

  rem_IO!(pat)
  rem_IO!(R_)

  if repl
    I = hyptype(T)[4]()
    lnodes = [v[1] for v in vmapset]
    add_parts!(I, :V, length(vmapset), color=pat[:color][lnodes])
    L = ACSetTransformation(I, pat, V=lnodes)
    R = ACSetTransformation(I, R_, V=[v[2] for v in vmapset])
  else
    L = id(pat)
    R = construct_cospan_homomorphism(pat, R_, Lmap, lrmap, Rmap, ccR)
  end

  # Construct match morphism
  pdict = Dict(k=>[get(v, i, nothing) for i in 1:nparts(pat, k)]
           for (k, v) in collect(partial))
  println("about to look for homomorphisms")
  ms = filter(m->valid_dpo(L,m) && !redundant(m, L, R, vmapset), homomorphisms(
        pat, sc_cset, monic=monic, initial=pdict))
  println("found $(length(ms)) homomorphisms")
  # could we do a horizontal composition of structured cospan rewrites to
  # do all at once?
  mseq = []
  hcs = [h.components for h in ms]
  err = "expected $n matches, but found $(length(ms)): $(hcs)"
  n == -1 || length(ms) == n || error(err)
  if isempty(ms)
    return sc_cset
  end
  h = nothing

  for m in ms
     new_m = compose(vcat([m], mseq))
     _, g, _, h = rewrite_match_data(L,R,new_m)
     append!(mseq, [invert(g), h])
  end
  println("done rewriting")
  new_apex = codom(h)
  return new_apex
end

function redundant(m, L, R, vmapset)::Bool
  i = Dict([R[:V](r) => m[:V](L[:V](l)) for (l, r) in vmapset])
  red = is_homomorphic(codom(R), codom(m), initial=Dict([:V=>i]))
  if red println("REDUNDANT!") end
  return red
end

"""
A cospan homomorphism requires inputs and outputs to be isomorphic and for the
following diagram to commute
   X1
  ↗   ↖
I   ↓  O
  ↘   ↙
   X2
"""
function csp_homomorphic(sc_cset1, sc_cset2)::Bool
  return is_homomorphic(sc_cset1, sc_cset2, iso = [:_I, :_O])
end

"""
Remove the _I and _O components
"""
function rem_IO!(sc_cset::ACSet)::Nothing
  rem_parts!(sc_cset, :_I, 1:nparts(sc_cset,:_I))
  rem_parts!(sc_cset, :_O, 1:nparts(sc_cset,:_O))
end

"""
Remove redundant nodes of a hypergraph. Paradigmatic case:

 ↗[F]↘
•   •   ... this can be simplified to •→[F]→•
 ↘[F]↗

A less trivial case, two copies of the following w/ same input and output:
⟶ [F] ⟶ [G] ⟶
   ↑    ↓
  [e]    [X]

Perhaps a search over all pairs of hyperedge legs that emanate from the same
vertex? Homomorphism queries for each possible subhypergraph?
"""
function rem_dups!(sc_cset::ACSet)::Nothing
  # to do
end


"""
Construct a cospan homomorphism from the following data:
WD₁  ↪  WD₂
 ↟     ↟
CSP₁ → CSP₂
The maps from CSP to WD are effectively surjective because we keep track of the
connected components in the WD.
"""
function construct_cospan_homomorphism(csp1::ACSet, csp2::ACSet,
                     cspwd1::Dict{Symbol, Vector{Int}},
                     wd1wd2::Vector{Int},
                     cspwd2::Dict{Symbol, Vector{Int}},
                     cc2::Dict{Int,Int}
                     )::ACSetTransformation
  d = Dict{Symbol, Vector{Int}}()
  for (k, map1) in collect(cspwd1)
    mapping, map2 = Int[], [get(cc2, i, i) for i in cspwd2[k]]
    for (_, csp1box) in enumerate(map1)
      csp2box = wd1wd2[csp1box]
      csp2box_canonical = get(cc2, csp2box, csp2box)
      res = findfirst(==(csp2box_canonical), map2)
      push!(mapping, res)
    end
    d[k] = mapping
  end
  return ACSetTransformation(csp1, csp2; d...)
end

function branch(l::WD, r::WD)# ::WD
  ld, rd = l.diagram, r.diagram
  nin, nout = [nparts(ld, x) for x in [:OuterInPort, :OuterOutPort]]
  intypes, outtypes = ld[:outer_in_port_type], ld[:outer_out_port_type]
  res = WiringDiagram(intypes, outtypes)
  inboxes = [add_box!(res, δ_box(s)) for s in intypes]
  outboxes = [add_box!(res, μ_box(s)) for s in outtypes]
  subbox = Box(intypes, outtypes)
  b1, b2 = [add_box!(res, subbox) for _ in 1:2]
  for i in 1:nin
    add_wires!(res, Pair[
      (input_id(res), i) => (inboxes[i], 1),
      (inboxes[i], 1) => (b1, i),
      (inboxes[i], 2) => (b2, i)])
  end
  for i in 1:nout
    add_wires!(res, Pair[
      (outboxes[i], 1) => (output_id(res), i),
      (b1, i) => (outboxes[i], 1),
      (b2, i) => (outboxes[i], 2)])
  end
  subboxes = [[δsd(s) for s in intypes]...,
        [μsd(s) for s in outtypes]..., l, r]
  start = nin+nout
  lb, rb = [nparts(x, :Box) for x in [ld, rd]]
  lboxrange = collect(start+1:start+lb)
  rboxrange = collect(start+lb+1:start+lb+rb)
  ores = ocompose(res, subboxes)
  @assert start+lb+rb == nparts(ores.diagram, :Box)
  return ores, lboxrange, rboxrange
end

"""
Prove an inequality in a relational theory
Return homomorphism as witness, if any
Takes in set of generators Σ, equations I, wiring diagram csets c1 and c2.
If oriented, then rewrites are only applied in the forward direction.
"""
function prove_(T::EqTheory, c1::WD, c2::WD;
         n::Int=3, oriented::Bool=false)::Pair{Bool, WD}
  d1 = wd_to_cospan(c1, T)[2]
  d2 = wd_to_cospan(c2, T)[2]
  h = homomorphism(d2, d1)
  if !(h===nothing)
    return h
  end
  for _ in 1:n
    for eq in sort(collect(T.eqs)) #, rev=true)
      println("applying $(eq.name)")
      d1 = apply_eq(d1, T, eq.name; n=-1)
      if !oriented && eq.rev  # apply both rewrite rules
        println("applying $(eq.name) reverse")
        d1 = apply_eq(d1, T, eq.name; forward=false, n=-1)
      end
      h = homomorphism(d2, d1)
    end
    if !(h===nothing)
      return true => h
    end
  end
  return false => d1 # return d1 if debugging
end


"""
Given a signature, create an OpenCSetType for hypergraphs including a distinct
hyperedge for each arity (distinguished by # and type of in/outputs).

TODO: return a specific ACSet HΣ for the signature, where being homomorphic to
HΣ means that a diagram satisfies the signature.
"""
function hyptype(Σ::EqTheory)
  arities = Dict{Pair{Vector{Symbol}, Vector{Symbol}}, Set{Symbol}}()
  for op in Σ.gens
    ar = op.input_ports => op.output_ports
    if haskey(arities, ar)
      push!(arities[ar], op.value)
    else
      arities[ar] = Set([op.value])
    end
  end
  pres = Presentation(FreeSchema)
  name = FreeSchema.Data{:generator}([:Name], [])
  add_generator!(pres, name)
  obsyms = [:V]
  for (i, o) in keys(arities)
    push!(obsyms, hypsyms(i,o)[1])
  end
  xobs = [Ob(FreeSchema, s) for s in obsyms]

  for x in xobs
    add_generator!(pres, x)
  end

  v = xobs[1]
  add_generator!(pres, FreeSchema.Attr{:generator}(
    [:color, xobs[1], name], [xobs[1], name]))

  for (n, (i, o)) in enumerate(keys(arities))
    x = xobs[n+1]
    _, lab, src, tgt = hypsyms(i, o)
    add_generator!(pres, FreeSchema.Attr{:generator}(
      [lab, x, name], [x, name]))

    for src_sym in src
      add_generator!(pres, Hom(src_sym, x, v))
    end
    for tgt_sym in tgt
      add_generator!(pres, Hom(tgt_sym, x, v))
    end
  end
  acst = ACSetType(pres, index=[])
  obtype, sctype = OpenACSetTypes(acst, :V)

  # Explicit cospan CSet
  _I, _O = Ob(FreeSchema, :_I), Ob(FreeSchema, :_O)
  add_generator!(pres, _I)
  add_generator!(pres, _O)
  add_generator!(pres, Hom(:_i, _I, xobs[1]))
  add_generator!(pres, Hom(:_o, _O, xobs[1]))
  cspcset = ACSetType(pres, index=[])
  return acst{Symbol}, obtype{Symbol}, sctype{Symbol}, cspcset{Symbol}
end

function hypsyms(Σ::EqTheory, s::Symbol
                 )::Tuple{Symbol, Symbol, Vector{Symbol}, Vector{Symbol}}
    b = only([g for g in Σ.gens if s==g.value])
    return hypsyms(b.input_ports, b.output_ports)
end
function hypsyms(i::Vector{Symbol}, j::Vector{Symbol}
        )::Tuple{Symbol, Symbol, Vector{Symbol}, Vector{Symbol}}
  str = x -> join(map(string,x),"_")
  istr, jstr = map(str, [i,j])
  ename = Symbol("E__$(istr)__$jstr")
  lab = Symbol("l__$(istr)__$jstr")
  src = [Symbol("s__$(istr)__$(jstr)__$i_ind") for i_ind in eachindex(i)]
  tgt = [Symbol("t__$(istr)__$(jstr)__$j_ind") for j_ind in eachindex(j)]
  return ename, lab, src, tgt
end


"""
Add a empty node between each generator and the outerbox and a node between each
generator. This should be an idempotent function. (todo: add tests for this)
"""
function wd_pad(sd::WD)::WD
  # check_wd(sd, "$sd pad\n")
  sd = deepcopy(sd)
  d = sd.diagram
  in_delete, out_delete, w_delete = Set{Int}(), Set{Int}(), Set{Int}()
  for (ps,pt,_) in d.tables[:PassWire]
    typ = d[:outer_in_port_type][ps]
    new_b = add_part!(d, :Box, value=typ, box_type=Junction{Nothing, Symbol})
    new_ip = add_part!(d, :InPort, in_port_box=new_b, in_port_type=typ)
    new_op = add_part!(d, :OutPort, out_port_box=new_b, out_port_type=typ)
    add_part!(d, :InWire, in_src=ps, in_tgt=new_ip, in_wire_value=nothing)
    add_part!(d, :OutWire, out_src=new_op, out_tgt=pt, out_wire_value=nothing)
  end
  for b in filter(x->!(d[:box_type][x]<:Junction), parts(d, :Box))
    for ip in incident(d, b, :in_port_box)
      typ = d[:in_port_type][ip]
      new_b = add_part!(d, :Box, value=typ, box_type=Junction{Nothing, Symbol})
      new_op = add_part!(d, :OutPort, out_port_box=new_b, out_port_type=typ)
      in_tgts, in_srcs, srcs, tgts = Int[],Int[],Int[],Int[]
      for iw in incident(d, ip, :tgt)
        new_ip = add_part!(d, :InPort, in_port_box=new_b, in_port_type=typ)
        push!(srcs, d[:src][iw])
        push!(tgts, new_ip)
        push!(w_delete, iw)
      end
      for iw in incident(d, ip, :in_tgt)
        new_ip = add_part!(d, :InPort, in_port_box=new_b, in_port_type=typ)
        push!(in_srcs, d[:in_src][iw])
        push!(in_tgts, new_ip)
        push!(in_delete, iw)
      end
      add_parts!(d, :Wire, length(srcs), src=srcs, tgt=tgts, wire_value=nothing)
      for (is, it) in zip(in_srcs, in_tgts)
        add_part!(d, :InWire, in_src=is, in_tgt=it, in_wire_value=nothing)
      end
      #add_parts!(d, :InWire, length(in_srcs), in_src=in_srcs, in_tgt=in_tgts, wire_value=nothing)
      add_part!(d, :Wire, src=new_op, tgt=ip, wire_value=nothing)
    end

    for op in incident(d, b, :out_port_box)
      typ = d[:out_port_type][op]
      new_b = add_part!(d, :Box, value=typ, box_type=Junction{Nothing, Symbol})
      new_ip = add_part!(d, :InPort, in_port_box=new_b,in_port_type=typ)
      srcs, tgts, out_srcs, out_tgts = Int[],Int[],Int[],Int[]
      for ow in incident(d, op, :src)
        new_op = add_part!(d, :OutPort, out_port_box=new_b, out_port_type=typ)
        push!(tgts, d[:tgt][ow])
        push!(srcs, new_op)
        push!(w_delete, ow)
      end
      for ow in incident(d, op, :out_src)
        new_op = add_part!(d, :OutPort, out_port_box=new_b, out_port_type=typ)
        push!(out_tgts, d[:out_tgt][ow])
        push!(out_srcs, new_op)
        push!(out_delete, ow)
      end
      add_parts!(d, :Wire, length(tgts), tgt=tgts, src=srcs, wire_value=nothing)
      add_parts!(d, :OutWire, length(out_tgts), out_tgt=out_tgts, out_src=out_srcs, out_wire_value=nothing)
      add_part!(d, :Wire, tgt=new_ip, src=op, wire_value=nothing)
    end

  end

  # ips = add_parts!(d, :Box, nparts(d, :InPort), value=d[:in_port_type], box_type=Junction{Nothing, Symbol})
  # ops = add_parts!(d,  :Box, nparts(d, :OutPort), value=d[:out_port_type], box_type=Junction{Nothing, Symbol})

  # for (w, (s_port, t_port, _)) in enumerate(d.tables[:Wire])
  #   s_box = ops[s_port]
  #   t_box = ips[t_port]
  #   if d[:box_type][s_box] <: Box && d[:box_type][t_box] <: Box
  #     s_typ, t_typ = d[:out_port_type][s_port], d[:in_port_type][t_port]
  #     new_in = add_part!(d, :InPort, in_port_box=s_box, in_port_type=s_typ)
  #     new_out = add_part!(d, :OutPort, out_port_box=t_box, out_port_type=t_typ)
  #     add_part!(d, :Wire, src=s_port, tgt=new_in, wire_value=nothing)
  #     add_part!(d, :Wire, src=new_out, tgt=t_port, wire_value=nothing)
  #     push!(w_delete, w)
  #   end
  # end
  # no FKs point to a wire, so we can freely delete them
  rem_parts!(d, :Wire, sort(collect(w_delete)))
  rem_parts!(d, :InWire, sort(collect(in_delete)))
  rem_parts!(d, :OutWire, sort(collect(out_delete)))
  rem_parts!(d, :PassWire, parts(d, :PassWire))
  return sd
end

"""
For a Wiring Diagram with labeled ports, a given box has an arity (and coarity)
"""
function get_arity(sd::WD, i::Int)::Pair{Vector{Symbol}, Vector{Symbol}}
  d = sd.diagram
  ss = [:in_port_box => :in_port_type, :out_port_box => :out_port_type]
  ip, op = [d[y][incident(d, i, x)] for (x, y) in ss]
  return ip => op
end

"""
Convert wiring diagram to cospan
All components connected by Frobenius generators are condensed together.

TODO don't assume all outerinports have a unique inwire
"""
function wd_to_cospan(sd::WD, Σ::EqTheory)# ::Tuple{StructuredCospan, ACSet}
  sd = wd_pad(sd)
  d = sd.diagram
  aptype, _, sctype, sccsettype = hyptype(Σ)

  # For each component in apex, keep track of which box each part comes from
  mapping = Dict([sym => Int[] for sym in ob(aptype.body.body.parameters[1])])

  # Isolate box indices that correspond to Frobenius nodes
  nodes = [i for (i, v) in enumerate(d[:box_type]) if v<:Junction]
  # Determine connected components by iterating over all wires/OuterPorts
  conn_comps = IntDisjointSets(nparts(d, :Box))
  for (srcport, tgtport, _) in d.tables[:Wire]
    srcbox, tgtbox = d[:out_port_box][srcport], d[:in_port_box][tgtport]
    if srcbox in nodes && tgtbox in nodes
      union!(conn_comps, srcbox, tgtbox)
    end
  end
  for op in parts(d, :OuterOutPort)
    bs = d[:out_port_box][d[:out_src][incident(d, op, :out_tgt)]]
    for (x,y) in zip(bs, bs[2:end])
      union!(conn_comps, x, y)
    end
  end
  for op in parts(d, :OuterInPort)
    bs = d[:in_port_box][d[:in_tgt][incident(d, op, :in_src)]]
    for (x,y) in zip(bs, bs[2:end])
      union!(conn_comps, x, y)
    end
  end

  # Get hyperedge-specific info given a box index
  hs = i -> hypsyms(get_arity(sd, i)...)

  # Total # of connected components
  n = conn_comps.ngroups - (nparts(d, :Box) - length(nodes))  # N IS 1 TOO MANY
  nodetypes = Union{Nothing, Symbol}[nothing for _ in 1:n]

  # Representative box index for each connected component
  cclist = sort(collect(Set([find_root(conn_comps,i) for i in nodes])))

  mapping[:V] = cclist
  # Map each boxid (that is Frobenius) to boxid that is its representative
  vert_dict = Dict([i=>findfirst(==(find_root(conn_comps,i)), cclist)
            for i in nodes])
  apx = aptype()
  add_parts!(apx, :V, n)
  box_dict = Dict{Int,Int}()
  for (box, (val, btype)) in enumerate(zip(d[:value], d[:box_type]))
    if btype <: Box
      etype, lab, _, _ = hs(box)
      eind = add_part!(apx, etype; Dict([lab => val])...)
      box_dict[box] = eind
      push!(mapping[etype], box)
    end
  end

  for (srcport, tgtport, _) in d.tables[:Wire]
    srcbox, tgtbox = d[:out_port_box][srcport], d[:in_port_box][tgtport]
    if !(srcbox in nodes && tgtbox in nodes)
      if srcbox in nodes || tgtbox in nodes
        # true if wire is vert -> hyperedge, false if hyperedge -> vert
        srcnode = srcbox in nodes
        vert, hypedge, hypport, = (srcnode
                      ? (srcbox, tgtbox, tgtport)
                      : (tgtbox, srcbox, srcport))

        typ1 = d[:out_port_type][srcport]
        typ2 = d[:in_port_type][tgtport]
        err = "inconsistent ports $srcport ($typ1) -> $tgtport ($typ2)"
        typ1 == typ2 || error(err)
        prevtyp = nodetypes[vert_dict[vert]]
        if !(prevtyp === nothing)
          prevtyp == typ1 || error("inconsistent types")
        end
        nodetypes[vert_dict[vert]] = typ1

        _, _, ins, outs = hs(hypedge)

        part, porttype, portbtype = (srcnode
                        ? (ins, :InPort, :in_port_box)
                        : (outs, :OutPort, :out_port_box))
        boxports = [i for i in 1:nparts(d, porttype)
              if d[portbtype][i] == hypedge]
        port_ind = findfirst(==(hypport), boxports)

        box_ind = box_dict[hypedge]
        set_subpart!(apx, box_ind, part[port_ind], vert_dict[vert])
      else
      end
    end
  end

  # Assemble structured cospan legs
  indata = [i=>d[:in_port_box][
    d[:in_tgt][incident(d, i, :in_src)[1]] ]  for i in parts(d, :OuterInPort)]
  outdata = [i=>d[:out_port_box][
    d[:out_src][incident(d, i, :out_tgt)[1]] ]  for i in parts(d, :OuterOutPort)]
  lft = FinFunction(Int[vert_dict[i[2]] for i in indata],n)
  rght = FinFunction(Int[vert_dict[i[2]] for i in outdata],n)

  for (v, c) in [zip(collect(lft), d[:outer_in_port_type])...,
           zip(collect(rght), d[:outer_out_port_type])...]
    prevtyp = nodetypes[v]
    if !(prevtyp === nothing)
      prevtyp == c || error("inconsistent types")
    end
    nodetypes[v] = c
  end
  set_subpart!(apx, :color, nodetypes)

  # assemble StructuredCospan
  sc = sctype(apx, lft, rght)

  # Copy over apex data to ACSet representing entering s.c. structure
  cset = sccsettype()
  cd, ad = aptype.body.body.parameters[1:2]
  for o in ob(cd)
    add_parts!(cset, o, nparts(apx, o))
  end
  for h in [hom(cd)..., attr(ad)...]
    set_subpart!(cset, h, apx[h])
  end

  # Represent leg data within the acset
  add_parts!(cset, :_I, length(indata))
  add_parts!(cset, :_O, length(outdata))
  set_subpart!(cset, :_i, collect(lft))
  set_subpart!(cset, :_o, collect(rght))

  return sc, cset, vert_dict, mapping
end

function cospan_to_wd(csp::ACSet{CD})::WD where{CD}
  obs = ob(CD)
  nin, nout = [nparts(csp, x) for x in [:_I, :_O]]
  intypes, outtypes = [csp[:color][csp[x]] for x in [:_i, :_o]]

  res = WiringDiagram(intypes, outtypes)

  boxdict = Dict()
  for o in obs[2:end-2] # skip V, _I, and _O
    _, o_nin_, o_nout_ = Base.split(string(o), "__")
    o_intypes, o_outtypes = arity = [
      map(Symbol, filter(!isempty, Base.split(x, "_"))) for x in [o_nin_, o_nout_]]
    lab = hypsyms(o_intypes, o_outtypes)[2]
    # arity = o_nin => o_nout
    boxdict[arity] = Int[]
    for j in 1:nparts(csp, o)
      bx = Box(csp[lab][j], o_intypes, o_outtypes)
      push!(boxdict[arity], add_box!(res, bx))
    end
  end

  @assert obs[1] == :V
  for i in 1:nparts(csp, :V)
    v_in  =Tuple{Int, Union{Nothing, Int}}[
        (-inp, nothing) for inp in 1:nin if csp[:_i][inp] == i]
    v_out = Tuple{Int, Union{Nothing, Int}}[
        (-oup, nothing) for oup in 1:nout if csp[:_o][oup] == i]
    for ((o_nin, o_nout), hypboxes) in collect(boxdict)
      _, _, osrc, otgt  = hypsyms(o_nin, o_nout)
      for (hypind, hypbox) in enumerate(hypboxes)
        for (srcport, srcpart) in enumerate(osrc)
          if csp[srcpart][hypind] == i
            push!(v_out, (hypbox, srcport))
          end
        end
        for (tgtort, tgtart) in enumerate(otgt)
          if csp[tgtart][hypind] == i
            push!(v_in, (hypbox, tgtort))
          end
        end
      end
    end
    b = add_box!(res, Junction(csp[:color][i], 1, 1))

    for (_, (v_i, port)) in enumerate(v_in)
      src = v_i < 0 ? (input_id(res),-v_i) : (v_i, port)
      add_wire!(res, src => (b, 1)) # replace 1 w/ indx for distinct ports
    end
    for (_, (v_o, port)) in enumerate(v_out)
      tgt = v_o < 0 ?  (output_id(res),-v_o) : (v_o, port)
      add_wire!(res, (b, 1) => tgt) # see above
    end
  end
  return res
end

function label(wd::WiringDiagram;
         w::Union{Vector{Pair{Int, String}}, Vector{String}}=String[],
         i::Union{Vector{Pair{Int, String}}, Vector{String}}=String[],
         o::Union{Vector{Pair{Int, String}}, Vector{String}}=String[],
        )::WiringDiagram

  wd_ = deepcopy(wd)
  d = wd_.diagram
  function to_vec(x::Union{Vector{Pair{Int, String}}, Vector{String}}, s::Symbol)
    return x[1] isa String ? x : [get(Dict(x), i, nothing)
                   for i in 1:nparts(d, s)]
  end
  set_subpart!(d, :in_port_type, repeat([nothing], nparts(d, :InPort)))
  set_subpart!(d, :out_port_type, repeat([nothing], nparts(d, :OutPort)))
  set_subpart!(d, :outer_in_port_type, repeat([nothing], nparts(d, :OuterInPort)))

  if !isempty(w)
    v = to_vec(w, :Wire)
    for (i, val) in enumerate(v)
      set_subpart!(d, d[:tgt][i], :in_port_type, val)
      set_subpart!(d, d[:src][i], :out_port_type, val)
    end
  end
  if !isempty(o)
    set_subpart!(d, [d[:out_src][i] for i in 1:nparts(d, :OutWire)],
             :out_port_type, to_vec(o, :OutWire))
  end
  if !isempty(i)
    set_subpart!(d, :outer_in_port_type, to_vec(i, :InWire))
  end
  return wd_
end


"""
Is there a path from input to output that only passes through the designated
boxes? Propagate reachability information backwards, then check if inputs
are included.
"""
function path_exists(wd::WD, bs::Set{Int})::Vector{Float64}
  reachable = Set()
end

"""
For all possible subsets of boxes, compute its cost (sum up primcosts) and
check if it is a feasible computation (inputs are connected to outputs).

Return a WD with only the boxes of the minimum cost feasible WD.
"""
function mincost(wd::WD, primcosts::Dict{Symbol, Float64})::WD
  wd = deepcopy(wd)
  all_boxes = Set(boxes(wd))
  res = [b for b in powerset(all_boxes) if path_exists(wd, sub_set)]
  mcost, mind = findmin([sum([primcosts[wd[:box_value][bx] for bx in bxs]])
              for bxs in res])
  # keep just the boxes in min cost boxes
  keepboxes = Set(res[mind])
  rem_boxes!(wd, sort([b for b in all_boxes if b ∉ keepboxes]))
  return wd
end

function to_schema(Σ::EqTheory)::Schema
  return Schema(Dict([b.value => length(b.input_ports)+length(b.output_ports)
            for b in Σ.gens]))
end

"""A cospan of hypergraph ACset is converted to a relational db instance"""
function to_db_inst(Σ::EqTheory, csp::ACSet{CD})::ACSet where {CD}
  csettype, _ = schema_to_csettype(to_schema(Σ))
  res = csettype()
  add_parts!(res, :V, nparts(csp, :V), id_V=collect(parts(csp, :V)), sort=csp[:color])
  for o in filter(x->x ∉ [:V, :_I, :_O], ob(CD))
    for (i, r_) in enumerate(csp.tables[o])
      r = collect(r_)
      R = r[end]
      ats = [arg(R, i)=>v for (i, v) in enumerate(r[1:end-1])]
      add_part!(res, R; Dict(vcat([ids(R)=>i],ats))...)
    end
  end
  return res
end

function from_db_inst(Σ::EqTheory, I::ACSet, ins::Vector{Int}=Int[],
                      outs::Vector{Int}=Int[])::ACSet
  res = hyptype(Σ)[4]()
  add_parts!(res, :V, nparts(I, :V), color=I[:sort])
  for g in [x.value for x in Σ.gens]
    t, l, i, o = hypsyms(Σ, g)
    io = vcat(i,o)
    for r in I.tables[g]
      d = Dict{Symbol, Any}(zip(io, r))
      d[l] = g
      add_part!(res, t; d...)
    end
  end
  add_parts!(res, :_I, length(ins),  _i=[only(incident(I, i, :id_V)) for i in ins])
  add_parts!(res, :_O, length(outs), _o=[only(incident(I, i, :id_V)) for i in outs])
  return res
end


"""
External wires in L are variables `x` that are shared between the body
and the result. Internal nodes (not touched by an external wire) of L are
variables that are not used in the result.

External wires in R must be given the same ID as found in the corresponding L
instance. Internal nodes in R must be given fresh IDs. If multiple external
wires in R map to the same node, this is an equality constraint. (just pick one
of the wire IDs to be the ID of this node)
"""
function to_dependency(Σ::EqTheory, csp::Eq)::Dep
  L = wd_to_cospan(csp.l, Σ)[2];
  R = wd_to_cospan(csp.r, Σ)[2];
  body = to_db_inst(Σ, L)
  res = to_db_inst(Σ, R)
  μ = Dict([k => k + nparts(body, :V) for k in res[:id_V]]) # fresh IDs
  groups = Dict{Int, Vector{Int}}([k=>Int[] for k in res[:id_V]])
  for (i, (vl, vr)) in enumerate(collect(zip(
      vcat(L[:_i], L[:_o]), vcat(R[:_i], R[:_o]))))
    id_L, id_R = body[:id_V][vl], res[:id_V][vr]
    μ[id_R]=id_L
    push!(groups[vr], id_L)
  end
  # Set μ to map each connected component to its min element
  eqs = Set([Set(vs) for vs in filter(x->length(x)>1, collect(values(groups)))])
  return Dep(csp.name, body, appdict(μ,res), eqs)
end



"""
Given two cospan of hypergraph ACSets, construct a termination condition
"""
function proven(Σ::EqTheory, start::ACSet, conclusion::ACSet)::Function
  function f(I::ACSet,_,μ::Dict{Int,Int},_)::Bool
    ins, outs = [appdict(μ,start[x]) for x in [:_i, :_o]]
    println("ins $ins outs $outs μ $(sort(collect(μ))[1:min(5, end)])")
    res = from_db_inst(Σ, I, ins, outs)
    b = csp_homomorphic(conclusion, res)
    println("homomorphism test $b")
    return b
  end
  return f
end

function prove(Σ::EqTheory, start::Union{ACSet,WD}, goal::Union{ACSet,WD};
               strat::Function=allseq, maxi::Int=3)
  start = start isa ACSet ? start : wd_to_cospan(start, Σ)[2];
  goal  = goal  isa ACSet ? goal  : wd_to_cospan(goal , Σ)[2];
  I = to_db_inst(Σ, start)
  eqs = vcat([to_dependency(Σ, e) for e in Σ.eqs],
             [to_dependency(Σ, flip(e)) for e in Σ.eqs if e.rev])
  pr = proven(Σ, start, goal)
  (res, μ) =  core_chase(I, Set(eqs), strat, pr, maxi)
  res2 = from_db_inst(Σ, res, appdict(μ, start[:_i]), appdict(μ, start[:_o]))
  return pr(res, nothing, μ,  nothing), res, μ, res2
end



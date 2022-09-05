module Models
export SketchModel, AuxData,
       create_premodel,
       crel_to_cset,
       cset_to_crel,
       validate!,
       Addition,
       Merge,
       Change,
       is_no_op,
       update_changes,
       update_change,
       exec_change,
       rem_dup_relations,
       has_map, fk, add_fk, ModelException
# to do: cut this down to only things end-users would use

using Catlab.CategoricalAlgebra, Catlab.Theories
import Catlab.CategoricalAlgebra: apex, left, right

using ..Sketches

import Base: union!, merge
using DataStructures
using AutoHashEquals

#----------------------------------#
# Should be upstreamed into catlab #
#----------------------------------#
is_surjective(f::FinFunction) =
  length(codom(f)) == length(Set(values(collect(f))))
is_injective(f::FinFunction)  =
  length(dom(f)) == length(Set(values(collect(f))))
function is_injective(α::ACSetTransformation{S}) where {S}
    for c in components(α)
      if !is_injective(c) return false end
    end
    return true
end
function is_surjective(α::ACSetTransformation{S}) where {S}
  for c in components(α)
    if !is_surjective(c) return false end
  end
  return true
end
image(f) = equalizer(legs(pushout(f,f))...)
coimage(f) = coequalizer(legs(pullback(f,f))...)
function epi_mono(f)
  Im, CoIm = image(f), coimage(f)
  iso = factorize(Im, factorize(CoIm, f))
  return ComposablePair(proj(CoIm) ⋅ iso, incl(Im))
end
#######

struct ModelException <: Exception
  msg::String
  ModelException(msg::String="") = new(msg)
end

# There is an list element for each element in the root table
# Those elements each are of length n, for the n objects in the path_eq diagram
# Each of those n elements is a list of the possible values that the table could
# be.
const EQ = Dict{Symbol,
                Vector{
                       Vector{
                              Union{
                                    Nothing,
                                    AbstractVector{Int}
                              }
                       }
                      }
                }

"""

Because we cannot yet compute cones incrementally, there is no reason to cache
any information related to cones.

eqs: Equivalence classes for each object in the model
Cocones: equivalence class across all objects in each cocone diagram
         includes a mapping to clarify which indices correspond to which elems
path_eqs: Data-structure capturing, which possible elements there are (for obj
          in the path eq diagram) for each element of the root object.
frozen: whether a table/FK can possibly change. Initially, non-limit objects
        are frozen. Limit objects become frozen when all the morphisms in their
        diagrams are frozen. Morphisms are frozen when they are from a frozen
        object and fully determined.
"""
@auto_hash_equals mutable struct AuxData
  eqs::Dict{Symbol, IntDisjointSets{Int}}
  # cones::Vector{Dict{Vector{Int},Union{Nothing,Int}}}
  cocones::Vector{Pair{IntDisjointSets{Int}, Vector{Tuple{Symbol,Int,Int}}}}
  path_eqs::EQ
  frozen::Pair{Set{Symbol},Set{Symbol}}
end

"""
Data of a premodel plus all the auxillary sketch constraint information
"""
@auto_hash_equals mutable struct SketchModel{S}
  model::StructACSet{S}
  aux::AuxData
end

"""
Create an empty premodel (C-Rel).
"""
function create_premodel(S::Sketch, n=Dict{Symbol, Int}(), freeze_obs=Symbol[])::SketchModel
  J = S.crel()
  keys(n) ⊆ vlabel(S) || error("bad key(s) $(keys(n)|>collect)") # validate
  freeze_obs ⊆ vlabel(S) || error("bad freeze obs $(freeze_obs)") # validate
  # handle one_obs
  one_obs = Set([c.apex for c in S.cones if nv(c.d)==0])
  for o in one_obs
    if haskey(n, o) n[o] == 1 || error("bad")
    else  n[o] = 1
    end
  end
  # handle zero obs
  zero_obs = Set([c.apex for c in S.cocones if nv(c.d)==0])

  change = true
  while change  # Maps into zero obs are zero obs
    change = false
    for z in zero_obs
      for h in hom_in(S, z)
        if src(S,h) ∉ zero_obs
          push!(zero_obs, src(S,h)); change = true
        end
      end
    end
  end

  for o in zero_obs
    if haskey(n, o) n[o] == 0 || error("bad o $o n[o] $(n[o])")
    else  n[o] = 0
    end
  end

  for (k,v) in collect(n) add_parts!(J, k, v) end

  lim_obs = Set([c.apex for c in vcat(S.cones,S.cocones)])
  freeze_obs = Set(freeze_obs ∪ one_obs ∪ zero_obs)
  freeze_arrs = Set{Symbol}([hom_out(S,collect(zero_obs))...,add_id.(vlabel(S))...])

  eqs = Dict([o=>IntDisjointSets(nparts(J, o)) for o in vlabel(S)])
  cocones = Vector{Pair{IntDisjointSets{Int}, Vector{Tuple{Symbol,Int,Int}}}}(
   map(S.cocones) do c
    tabs = vcat(map(enumerate(vlabel(c.d))) do (iv,v)
      Tuple{Symbol,Int,Int}[(v,iv,i) for i in parts(J,v)]
    end...)
    ids = IntDisjointSets(length(tabs))
    ldict = [l=>[ti for (ti, l_) in c.legs if l_==l] for l in unique(last.(c.legs))]
    for (l,ltabs) in filter(x->length(x[2])>1, ldict)
      ref_inds = findall(x->x[2]==first(ltabs), tabs)
      for ltab in ltabs[2:end]
        for (i,j) in zip(ref_inds, findall(x->x[2]==ltab, tabs))
          union!(ids, i, j)
        end
      end
    end

    return ids => tabs
  end)
  path_eqs = EQ(map(collect(S.eqs)) do (k,g)
    k=>map(parts(J,k)) do p
      map(enumerate(vlabel(g))) do (i,v)
        if i == 1 return [p]
        elseif v ∈ freeze_obs return parts(J,v)
        else return nothing
        end
      end
    end
  end)
  return SketchModel(J,AuxData(eqs,cocones,path_eqs, freeze_obs=>freeze_arrs))
end

"""
A premodel that does not have correct cone/cocone/patheq data.
Mainly for testing.
"""
function test_premodel(S::Sketch, J::StructACSet{Sc}; freeze=Symbol[]) where Sc
  for c in filter(c->nv(c.d) == 0, S.cones)
    if nparts(J, c.apex) == 0 add_part!(J, c.apex) end
  end
  J_ = create_premodel(S, Dict(k=>nparts(J,k) for k in vlabel(S)), freeze)
  Jrel = cset_to_crel(S,J)
  ad = Addition(S,J_,homomorphism(J_.model,Jrel;monic=true),id(J_.model))
  J_.model = codom(exec_change(S,J_.model,ad))
  # TODO fix cocones/patheqs to first appx?
  return J_
end


"""
Convert a premodel (C-Rel) to a model C-Set.
Elements that are not mapped by a relation are given a target value of 0.
If this happens at all, an output bool will be true
If the same element is mapped to multiple outputs, an error is thrown.
"""
crel_to_cset(S::Sketch, J::SketchModel) = crel_to_cset(S,J.model)

function crel_to_cset(S::Sketch, J::StructACSet)::Pair{StructACSet, Bool}
  res = S.cset()
  for o in S.schema[:vlabel]
    add_parts!(res, o, nparts(J, o))
  end
  partial = false
  for m in elabel(S)
    msrc, mtgt = add_srctgt(m)
    length(J[msrc]) == length(Set(J[msrc])) || error("nonfunctional $J")
    partial |= length(J[msrc]) != nparts(J, src(S, m))
    for (domval, codomval) in zip(J[msrc], J[mtgt])
      set_subpart!(res, domval, m, codomval)
    end
  end
  return res => partial
end

function cset_to_crel(S::Sketch, J::StructACSet{Sc}) where Sc
  res = S.crel()
  for o in ob(Sc)
    add_parts!(res, o, nparts(J,o))
  end
  for h in hom(Sc)
    for (i, v) in enumerate(J[h])
      if v != 0
        d = zip(add_srctgt(h),[i,v])
        add_part!(res, h; Dict(d)...)
      end
    end
  end
  res
end

"""
TODO:

There are certain things we wish premodels to abide by, regardless of state of
information propagation:
- Equivalence class morphisms are surjective
- The leg data in the (co)cone object is correct.
  (i.e. if the cone element says leg#1 is value x, then the foreign key
  (corresponding to leg#1) of corresponding apex element should be x.
- There is a bijection between elements in the apex of a (co)cone and the
  corresponding (co)cone object
"""
function validate!(S::Sketch, J_::SketchModel)
  J = J_.model
  for (c,Jc) in zip(S.cones, J_.cones)
    nparts(J, c.apex) == nparts(J, :apex) || error("Cone ob not in bijection")
    # todo
  end
  for (c,Jc) in zip(S.cocones, J_.cocones)
    nparts(J, c.apex) == nparts(Jc, :apex) || error("Cocone ob not in bijection")
    # todo
  end
end

# Changes
#########
abstract type Change{S} end
apex(c::Change{S}) where S = dom(c.l) # == dom(c.r)
left(c::Change{S}) where S = c.l
right(c::Change{S}) where S = c.r

"""
Add elements (but merge none) via a monic partial morphism L↩I↪R, where R is
the current model.
"""
struct Addition{S} <: Change{S}
  l :: ACSetTransformation{S}
  r :: ACSetTransformation{S}
  function Addition(S::Sketch, J::SketchModel,
                    l::ACSetTransformation{Sc},
                    r::ACSetTransformation{Sc}) where Sc
    dom(l)==dom(r) || error("addition must be a span")
    codom(r) == J.model || error("addition doesn't match")

    map(collect(union(J.aux.frozen...) ∩ (vlabel(S)∪elabel(S)))) do s
      nd, ncd = nparts(dom(l), s), nparts(codom(l),s)
      nd <= ncd || error("cannot add $s (frozen): $nd -> $ncd")
    end
    is_injective(l) || error("span L must be monic $(components(l))")
    is_injective(r) || error("span R must be monic $(components(r))")
    all(is_injective, [l,r]) || error("span must be monic")
    all(is_natural, [l, r]) || error("naturality")
    all(e->nparts(dom(l), e) == 0, elabel(S)) || error("No FKs in interface")
    new{Sc}(deepcopy(l),deepcopy(r))
  end
end

"""Easier constructor, when the addition has zero overlap with the old model"""
Addition(S, old::SketchModel{Sc}, new::StructACSet{Sc}) where Sc =
  Addition(S, old, create(new), create(old.model))
Addition(S, old::SketchModel) = Addition(S,old,S.crel())

function Base.show(io::IO, a::Addition{S}) where S
  body = join(filter(x->!isempty(x), map(ob(S)) do v
    n = nparts(codom(a.l), v) - nparts(dom(a.l), v)
    n <= 0 ? "" : "$v:$n"
  end), ",")
  print(io, "Addition($body)")
end

"""
We can merge elements (but add none) via a span L↞I↪R, where R is the current
model.

L contains the merged equivalence classes, and I contains the
elements of R that are being merged together.

NOTE: we immediately modify the IntDisjointSets to quotient the equivalence
classes, allowing the Merge information to be used immediately in inferring
(co)cones/patheqs/etc.

However, we don't immediately perform the merge. We want to know which two
distinct things got merged in the later procedure of inferring how (co)cones
*change* from the merge.
"""
struct Merge{S} <: Change{S}
  l::ACSetTransformation{S}
  r::ACSetTransformation{S}
  function Merge(S::Sketch, J::SketchModel{Sc},
                 d::Dict{Symbol,Vector{Vector{Int}}}) where Sc
    I, R = [S.crel() for _ in 1:2]
    dIR, dIJ = [DefaultDict{Symbol, Vector{Int}}(()->Int[]) for _ in 1:2]
    keys(d) ⊆ vlabel(S) || error(keys(d))
    for (k, vvs) in collect(d)
      allvs = vcat(vvs...)
      length(allvs) == length(Set(allvs)) || error("Merge not disjoint $k $vvs")
      minimum(length.(vvs)) > 1 || error("Merging single elem $k $vvs")
      add_parts!(I, k, length(allvs))
      for (r, vs) in enumerate(vvs)
        append!(dIJ[k], vs)
        append!(dIR[k], fill(add_part!(R, k), length(vs)))
        # Quotient the eq classes immediately
        for vs in filter(x->length(x)>1, vvs)
          for (v1, v2) in zip(vs, vs[2:end])
            union!(J.aux.eqs[k], v1, v2)
          end
        end
      end
    end
    ir = ACSetTransformation(I, R; dIR...)
    ij = ACSetTransformation(I, J.model; dIJ...)
    for v in vlabel(S)
      if nparts(I,v) == 1 error(I) end
    end

    map(collect(union(J.aux.frozen...)∩(vlabel(S)∪elabel(S)))) do s
      nd, ncd = nparts(dom(ir), s), nparts(codom(ir),s)
      nd == ncd || error("cannot merge/add $s (frozen): $nd -> $ncd")
    end

    is_surjective(ir) || error("ir $ir")
    is_injective(ij) || error("ij $ij")
    all(is_natural, [ir, ij]) || error("naturality")
    all(e->nparts(I, e) == 0, elabel(S)) || error("No FKs in interface")
    return new{Sc}(ir, ij)
  end
  function Merge(S::Sketch,_::SketchModel,l::ACSetTransformation{Sc},r::ACSetTransformation{Sc}) where Sc
    dom(l) == dom(r)
    is_surjective(l) || error("L $l")
    is_injective(r) || error("R $r")
    all(is_natural, [l, r]) || error("naturality")
    all(e->nparts(dom(l), e) == 0, elabel(S)) || error("No FKs in interface")
    new{Sc}(l,r)
  end
end

Merge(S, old::SketchModel) = Merge(S,old,Dict{Symbol,Vector{Vector{Int}}}())


function Base.show(io::IO, a::Merge{S}) where S
  body = join(filter(x->!isempty(x), map(ob(S)) do v
    n = [length(preimage(a.l[v], x)) for x in parts(codom(a.l), v)]
    isempty(n) ? "" : "$v:$(join(n,"|"))"
  end), ",")
  print(io, "Merge($body)")
end

"""
Apply a change to CSet. This does *not* update the eqs/(co)cones/patheqs. Just
returns a model morphism from applying the change.
"""
function exec_change(S::Sketch, J::StructACSet{Sc},e::Change
                     )::ACSetTransformation where {Sc}
  codom(e.r) == J || error("Cannot apply change. No match.")
  is_natural(e.r) || error(println.(pairs(components(e.r))))
  dom(e.l) == dom(e.r) || error("baddom")
  res = pushout(e.l, e.r) |> collect |> last
  return res ⋅ rem_dup_relations(S, codom(res))
end


function rem_dup_relations(S::Sketch, J::StructACSet)
  # Detect redundant duplicate relation rows
  md = Dict{Symbol, Vector{Vector{Int}}}()
  J2 = typeof(J)()
  dJJ = Dict{Symbol, Vector{Int}}(pairs(copy_parts!(J2, J; Dict([v=>parts(J,v) for v in vlabel(S)])...)))
  changed = false
  for d in elabel(S) # could be done in parallel
    dJJ[d] = Int[]
    dsrc, dtgt = add_srctgt(d)
    dic = Dict()
    for (i, st) in enumerate(zip(J[dsrc], J[dtgt]))
      if haskey(dic, st)
        changed |= true
      else
        dic[st] = add_part!(J2, d; Dict(zip([dsrc,dtgt], st))...)
      end
      push!(dJJ[d], dic[st])
    end
    md[d] = filter(v->length(v) > 1, collect(values(dic))) |> collect
  end
  if !changed return id(J) end
  return ACSetTransformation(J, J2; dJJ...)
end

"""
It seems like we could just postcompose the right leg of the span with the model
update (R₁→R₂), like so:

L ↩ I ↪ R₁ ⟶ R₂

However, this leaves us with a span L ↩ I ⟶ R₂, where the right leg is not
monic. We want to replace this with an equivalent span that is monic by merging
together elements in L that have been implicitly merged by the model update.

We first get the *image* of I in R₂, I', which is an epi-mono decomposition.
We then take a pushout to obtain our new monic span.

L  ↩ I
↡ ⌝  ↡  ↘
L' ↩ I'  ↪ R    (<-- this is the new, monic span)

This all applies equally to a span where the left leg is epi, not mono.
"""
function update_change(S::Sketch, ex::ACSetTransformation, l, r_)
  all(is_natural, [l,r_,ex]) || error("naturality")
  # The equivalence class data may have changed in the model due to on-the-fly
  # merging, but we can recover this by keeping the
  r = homomorphism(dom(r_), dom(ex); initial=Dict(
    k=>collect(components(r_)[k]) for k in labels(S)))
  R = r ⋅ ex
  I_I, I_R = epi_mono(R)
  _, I_L = pushout(l, I_I)
  return I_L, I_R
end
update_change(S::Sketch, J::SketchModel, ex, a::Addition) =  Addition(S, J, update_change(S, ex, a.l, a.r)...)
update_change(S::Sketch, J::SketchModel, ex, a::Merge) =  Merge(S, J, ex, update_change(S, ex, a.l, a.r)...)
update_changes(S::Sketch, J, ex, cs) = map(cs) do c
  res = update_change(S,J, ex, c)
  codom(res.r) == J.model || error("failed updated $c \n$ex")
  return res
end



eq_class(eq::IntDisjointSets, v::Int) = [i for i in 1:length(eq)
                                         if in_same_set(eq, i,v)]

"""
Check if there exists a map between x and y induced by equivalence classes, i.e.
by checking if there is a relation [X]<-X<-f->Y->[Y]
"""
function has_map(S::Sketch, J_::SketchModel, f::Symbol, x::Int, y::Int)::Bool
  J = J_.model
  from_map, to_map = add_srctgt(f)
  xs, ys = eq_class(J_.eqs[src(S,f)], x), eq_class(J_.eqs[tgt(S,f)], y)
  !isempty(vcat(incident(J,xs,from_map)...) ∩ vcat(incident(J,ys,to_map)...))
end

"""
Get something that `x` is related to by `f`, if anything
"""
function fk(S::Sketch, J::SketchModel, f::Symbol, x::Int)
  from_map, to_map = add_srctgt(f)
  xs = eq_class(J.aux.eqs[src(S,f)], x)
  fs = vcat(incident(J.model,xs,from_map)...)
  if isempty(fs) return nothing end
  return find_root!(J.aux.eqs[tgt(S,f)], J.model[first(fs), to_map])
end


"""
Get f(x) in a premodel (return an arbitrary element that is related by f).
Return nothing if f(x) is not yet defined.
"""
function fk(S::Sketch, J::StructACSet, f::Symbol, x::Int; inv=false)
  from_map, to_map = add_srctgt(f)
  for v in filter(v->f==add_id(v), vlabel(S)) return x end
  if inv to_map,from_map = from_map, to_map end
  fs = incident(J,x,from_map)
  if isempty(fs) return nothing end
  return J[first(fs), to_map]
end


"""Check if a morphism in a premodel is total, modulo equivalence classes"""
is_total(S::Sketch, J::SketchModel, e::Symbol) = is_total(S,J.model,J.aux.eqs,e)

function is_total(S::Sketch, J::StructACSet,
                  eqs::Dict{Symbol, IntDisjointSets{Int}}, e::Symbol)::Bool
  e_src =  add_src(e)
  sreps = unique([find_root!(eqs[src(S,e)],x) for x in J[e_src]])
  return length(sreps) == num_groups(eqs[src(S,e)])
end



fk_in(S::Sketch, J::SketchModel, f::Symbol, y::Int) = fk_in(S,J,f,[y])

function fk_in(S::Sketch, J::SketchModel, f::Symbol, ys::AbstractVector{Int})
  if isempty(ys) return [] end
  from_map, to_map = add_srctgt(f)
  ys = union([eq_class(J.aux.eqs[tgt(S,f)], y) for y in ys]...)
  fs = vcat(incident(J.model,ys,to_map)...)
  xs = [find_root!(J.aux.eqs[src(S,f)], x) for x in J.model[fs, from_map]]
  return xs |> unique
end

"""
If y is 0, this signals to add a *fresh* element to the codomain.
"""
function add_fk(S::Sketch,J::SketchModel,f::Symbol,x::Int,y::Int)
  verbose = false
  if verbose println("adding fk $f:#$x->#$y") end
  st =  y==0 ? [src(S,f)] :  [src(S,f),tgt(S,f)]
  st_same, xy_same = (src(S,f)==tgt(S,f)), (x == y)
  I = S.crel();
  if st_same&&xy_same
    add_part!(I, st[1])
    is_it = [1,1]
  else
    is_it =  [add_part!(I, x) for x in st];
  end
  L = deepcopy(I)
  if y == 0 is_it = [1,add_part!(L, tgt(S,f))] end
  add_part!(L, f; Dict(zip(add_srctgt(f), is_it))...)
  IL = homomorphism(I,L; initial=Dict(o=>parts(I,o) for o in vlabel(S)));
  d = st_same ? st[1]=> (xy_same ? [x] : [x,y]) : zip(st,[[x],[y]])
  IR = ACSetTransformation(I, J.model; Dict(d)...)
  Addition(S,J,IL,IR)
end


"""
Merge two Additions (or possibly Merges, but this hasn't been tested) which may
be partially overlapping in their maps into the model.

Let Iₒ be the overlap between the two I's, i.e. the pullback. We use this to
form the new I and R via pushouts. The map from the new I to the new L is given
by the universal property (as the maps to L are a "bigger" pushout square).
The map from new I to original R is also given by the same universal property,
where we form a commutative square using the original maps Iₙ->R.
   r₁
  I₁↪R         Iₒ ↪ I₁ ↪ L₁       Iₒ ↪ I₁ ---
  ↑⌝ ↑ r₂      ↓  ⌜ ↓    |        ↓  ⌜ ↓    |
  Iₒ↪I₂        I₂ ↪ newI |        I₂ ↪ newI | r₁
               ↓     !↘⌜ v        |     !↘⌜ v
               L₂ -----> newL      -------> R
                                       r₂
This doesn't generalize to multipushouts/multipullbacks as easily as one would
hope. If you have 3 Additions that have only pairwise overlap, Iₒ will be empty.
"""
merge(S::Sketch, J::SketchModel{X}, xs::AbstractVector{T}) where {X,T} =
  isempty(xs) ? T(S,J) : reduce((x,y)->merge(S,J,x,y), xs)

function merge(S::Sketch, J::SketchModel, a1::Change{Sc},a2::Change{Sc}) where Sc
  as = [a1,a2]
  T =  a1 isa Addition ? Addition : Merge
  ls, rs = left.(as), right.(as)
  Io = pullback(rs) # fail if a1 and a2 point to different models
  newI = pushout(legs(Io))
  ll = [compose(a,b) for (a,b) in zip(legs(Io), ls)]
  newL = pushout(ll)
  il = [compose(a,b) for (a,b) in zip(ls,legs(newL))]
  newIL = universal(newI, Multicospan(il))
  newIR = universal(newI, Multicospan(rs))
  return T(S,J,newIL,newIR)
end

# """
# Get the equivalence classes out of an equivalence relation. Pick the lowest
# value as the canonical representative.
# """
function eq_sets(eq::IntDisjointSets; remove_singles::Bool=false)::Set{Set{Int}}
  eqsets = DefaultDict{Int,Set{Int}}(Set{Int})
  for i in 1:length(eq)
    push!(eqsets[find_root!(eq, i)], i)
  end
  filt = v -> !(remove_singles && length(v)==1)
  return Set(filter(filt, collect(values(eqsets))))
end



"""
Applying some changes makes other changes redundant. This detects when we
can ignore a change
"""
is_no_op(ch::Change) = all(f->dom(f)==codom(f) && isperm(collect(f)),
                           collect(components(ch.l)))

function merge_eq(S::Sketch, J::StructACSet, eqclasses::Dict{Symbol, IntDisjointSets{Int}}
  )
  function eq_dicts(eq::Dict{Symbol, IntDisjointSets{Int}})::Dict{Symbol, Dict{Int,Int}}
    res = Dict{Symbol, Dict{Int,Int}}()
    for (k, v) in pairs(eq)
      d = Dict{Int, Int}()
      for es in eq_sets(v)
        m = minimum(es)
        for e in es
          d[e] = m
        end
      end
      res[k] = d
    end
    return res
  end
  verbose = false
  J = deepcopy(J)
  # Initialize a function mapping values to their new (quotiented) value
  μ = eq_dicts(eqclasses)

  # Initialize a record of which values are to be deleted
  delob = DefaultDict{Symbol, Vector{Int}}(Vector{Int})

  # Populate `delob` from `eqclasses`
  for (o, eq) in pairs(eqclasses)
    eqsets = eq_sets(eq; remove_singles=true)
    # Minimum element is the representative
    for vs in map(collect,collect(values(eqsets)))
      m = minimum(vs)
      vs_ = [v for v in vs if v!=m]
      append!(delob[o], collect(vs_))
    end
  end

  # Replace all instances of a class with its representative in J
  # could be done in parallel
  for d in elabel(S)
    dsrc, dtgt = add_srctgt(d)
    μsrc, μtgt = μ[src(S, d)], μ[tgt(S, d)]
    isempty(μsrc) || set_subpart!(J, dsrc, replace(J[dsrc], μsrc...))
    isempty(μtgt) || set_subpart!(J, dtgt, replace(J[dtgt], μtgt...))
  end

  # Detect redundant duplicate relation rows
  for d in elabel(S) # could be done in parallel
    dsrc, dtgt = add_srctgt(d)
    seen = Set{Tuple{Int,Int}}()
    for (i, st) in enumerate(zip(J[dsrc], J[dtgt]))
      if st ∈ seen
        push!(delob[d], i)
      else
        push!(seen, st)
      end
    end
  end
  # Remove redundant duplicate relation rows
  for (o, vs) in collect(delob)
    isempty(vs) || rem_parts!(J, o, sort(vs))
  end
  return J #μ
end

frozen_hom(S,J,h) =  h ∈ J.aux.frozen[2] || any(v->h==add_id(v), vlabel(S))



# """Imperative approach to this."""
# function exec_change!(S::Sketch, J::StructACSet,
#                       m::Dict{Symbol, Vector{Vector{Int}}})
#   # values to be deleted
#   delob = DefaultDict{Symbol, Vector{Int}}(Vector{Int})
#   for (k, vvs) in collect(m)
#     eqk, eqk_hom = add_equiv(k, true)
#     i = IntDisjointSets(nparts(J,eqk))
#     for vs in filter(x->length(x)>1, vvs)
#       for (v1, v2) in zip(vs, vs[2:end])
#         union!(i, J[v1, eqk_hom], J[v2, eqk_hom])
#       end
#     end
#     # Populate `delob` from `eqclasses`
#     eqsets = eq_sets(i; remove_singles=true)
#     for vs_ in sort.(collect.(collect(values(eqsets))))
#       v, vs, n = vs_[1], vs_[2:end], length(vs_)-1
#       append!(delob[k], vs) # Minimum element is the rep
#       # delete equivalence class members that are not equal to the rep's eq.c.
#       del_eqcs = sort(filter(e->e!=J[v, eqk_hom], J[vs, eqk_hom])|>collect)
#       append!(delob[eqk], del_eqcs)
#       for e in vcat(add_tgt.(hom_in(S, k)), add_src.(hom_out(S, k)))
#         set_subpart!(J, vcat(incident(J, vs, e)...), e, fill(v, n))
#       end
#     end
#   end
#   for (k, vs) in collect(delob)
#     rem_parts!(J, k, vs)
#   end
# end

"""
Relation tables need not have duplicate entries with the same src/tgt.
It is best to run this right after quotienting the equivalence classes.
"""
# function rem_dup_relations!(S::Sketch, J::StructACSet)
#   delob = DefaultDict{Symbol, Vector{Int}}(Vector{Int})
#   # Detect redundant duplicate relation rows
#   for d in elabel(S) # could be done in parallelShe
#     dsrc, dtgt = add_srctgt(d)
#     seen = Set{Tuple{Int,Int}}()
#     for (i, st) in enumerate(zip(J[dsrc], J[dtgt]))
#       if st ∈ seen
#         push!(delob[d], i)
#       else
#         push!(seen, st)
#       end
#     end
#   end
#   # Remove redundant duplicate relation rows
#   for (o, vs) in collect(delob)
#     isempty(vs) || rem_parts!(J, o, sort(vs))
#   end
# end


# union!(S::Sketch, J::StructACSet, tab::Symbol, i::Int, j::Int) =
#   union!(S,J,tab,[i,j])
# """
# Merge multiple elements of an *equivalence class* table.
# """
# function union!(::Sketch, J::StructACSet, tab::Symbol, xs::Vector{Int})
#   if length(xs) < 2  return false end
#   m = minimum(xs)
#   union_directed!(J, tab, m, [x for x in xs if x != m])
#   return true
# end
# """
# Merge eqclass elements `i < xs`
# Send everything that pointed to `xs` now to `i`.
# """
# function union_directed!(J::StructACSet, tab::Symbol, i::Int, xs::Vector{Int})
#   eq_tab, eq_hom = add_equiv(tab, true)
#   inc = vcat(incident(J, xs, eq_hom)...)
#   set_subpart!(J, inc, eq_hom, i)
#   rem_parts!(J, eq_tab, sort(xs))
# end

# add_rel!(S::Sketch, J::StructACSet, f::Symbol, i::Int, j::Int) =
#    add_part!(J, f; Dict(zip(add_srctgt(f), [i,j]))...)

end # module
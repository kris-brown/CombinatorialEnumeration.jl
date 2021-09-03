

# Chase Algorithm
#################

add_srctgt(x::Symbol) = Symbol("src_$(x)") => Symbol("tgt_$(x)")

"""Create a ACSet instance modeling a C-Rel from an instance of an ACSet"""
function crel(x::StructACSet{S}) where {S}
  name = Symbol("Rel_$(typeof(x).name.name)")
  os, hs, _, _, src, tgt = S.parameters
  pres = Presentation(FreeSchema)
  nv = length(os)
  alledge = Symbol[]
  xobs = [Ob(FreeSchema, sym) for sym in vcat(os...,hs...)]
  for x in xobs
    add_generator!(pres, x)
  end
  for (i,h) in enumerate(hs)
    s, t = add_srctgt(h)
    add_generator!(pres, Hom(s, xobs[nv+i], xobs[src[h]]))
    add_generator!(pres, Hom(t, xobs[nv+i], xobs[tgt[h]]))
    append!(alledge, [s,t])
  end
  expr = struct_acset(name, StructACSet, pres, index=alledge)
  eval(expr)
  rel = eval(name)
  J = Base.invokelatest(rel)

  # initialize the C-Rel with x which satisfies the laws
  for o in ob(S)
    add_parts!(J, o, nparts(x, o))
  end
  src, tgt = dom(S), codom(S)
  for (i, d) in enumerate(hom(S))
    hs, ht = add_srctgt(d)
    add_parts!(J, d, nparts(x, src[i]))
    set_subpart!(J, hs, parts(x, src[i]))
    set_subpart!(J, ht, x[d])
  end
  return J
end

"""Convert a C-Rel back to a C-Set, fail if relations are not functional"""
function uncrel(J::StructACSet, I::StructACSet{S}) where {S}
  res = typeof(I)()
  for o in ob(S)
    add_parts!(res, o, nparts(J, o))
  end
  for m in hom(S)
    msrc, mtgt = add_srctgt(m)
    md, mcd = zip(sort(collect(zip(J[msrc], J[mtgt])))...)
    collect(md) == collect(1:length(md)) || error("nonfunctional $J")
    set_subpart!(res, m, mcd)
  end
  return res
end

"""Evaluate a possibly composite composition on a subset of the domain"""
function eval_path(pth, J::StructACSet, xs::Set{Int})::Set{Int}
  pthkind = typeof(pth).parameters[1]  # Warning: uses implementation details
  if pthkind == :id
    return xs
  elseif pthkind == :generator
    args = [pth]
  elseif pthkind == :compose
    args = pth.args
  else
    error(pthkind)
  end
  # Iteratively update X to Y by searching through all (x,y) in R ⊆ X×Y
  for m in map(Symbol, args)
    msrc, mtgt = add_srctgt(m)
    if isempty(xs)
      return xs
    else
      newxs = Set{Int}()
      for (jx, jy) in zip(J[msrc], J[mtgt])
        if jx ∈ xs
          push!(newxs, jy)
        end
      end
      xs = newxs
    end
  end
  return xs
end

"""
Chase algorithm as described by Spivak and Wisnesky in "Fast Left-Kan Extensions
Using The Chase"

Todo: handle attributes
"""
function chase(F::Functor, I::StructACSet{IS}, codomI::StructACSet{S};
               n::Int=8, verbose::Bool=false)::StructACSet{S} where {IS, S}
  J = crel(codomI) # pre-model data structure, initialized with codomI
  η = Dict() # mapping into J from I

  # Further initialize J using the domain instance, I
  for c in generators(dom(F), :Ob)
    η[c] = add_parts!(J, Symbol(Ob(F)[c]), nparts(I, Symbol(c)))
  end
  changed = false # iterate until no change or n is reached
  for counter in 1:n
    if verbose
      println("----- ITERATION $counter ------")
    end

    # Initialize equivalence relations for each component
    eqclasses = Dict([o=>IntDisjointSets(nparts(J, o)) for o in ob(S)])
    changed = false

    # Action α: add new elements when a function is dangling
    fresh = Dict{Symbol, Set{Int}}([o=>Set{Int}() for o in ob(S)])
    for (d, ddom, dcodom) in zip(hom(S), dom(S), codom(S))
      dsrc, dtgt = add_srctgt(d)
      xs = setdiff(parts(J, ddom), J[dsrc] ∪ fresh[ddom])
      for x in xs  # no y such that (x,y) ∈ J(d) and no fresh x
        gx = add_part!(J, dcodom) # add a fresh symbol
        if verbose
          println("α: $d($ddom#$x) ADDED $dcodom $gx")
        end
        add_part!(J, d; Dict([dsrc=>x, dtgt=>gx])...)
        gx_ = push!(eqclasses[dcodom])
        push!(fresh[dcodom], gx)
        gx == gx_ || error("Unexpected mismatch: $eqclasses \n$J")
        changed = true
      end
    end

    # Action βd: add all coincidences induced by D (i.e. fire EGDs)
    for (p, q) in equations(codom(F))
      for x in parts(J, Symbol(dom(p)))
        for px in eval_path(p, J, Set([x]))
          for qx in eval_path(q, J, Set([x]))
            union!(eqclasses[Symbol(codom(p))], px, qx)
            if verbose && px != qx
              println("βF: $p=$q MERGED $(codom(p)) $px = $qx")
            end
            changed |= px != qx # flip iff changed = ⊥ AND px != qx
          end
        end
      end
    end

    # Action βF: add all coincidences induced by F. Naturality square constraint
    for mg in generators(dom(F), :Hom)
      m, Fm, Fmcodom = map(Symbol, [mg, Hom(F)[mg], Ob(F)[codom(mg)]])
      is_id = typeof(Hom(F)[mg]).parameters[1] == :id
      for (x, mx) in enumerate(I[m])
        mα = η[codom(mg)][mx]
        Fms, Fmt = add_srctgt(Fm)
        αx = η[dom(mg)][x]
        αm = is_id ? αx : J[Fmt][incident(J, αx, Fms)[1]]
        union!(eqclasses[Fmcodom], mα, αm)
        if verbose && mα != αm
          println("βF: $mg ($(dom(mg))#$x) MERGED $Fmcodom $mα = $αm")
        end
        changed |= mα != αm # flip iff changed = ⊥ AND mα != αm
      end
    end

    # Action δ: add all coincidences induced by functionality
    for (d, ddom, dcodom) in zip(hom(S), dom(S), codom(S))
      dsrc, dtgt = add_srctgt(d)
      for x in parts(J, ddom)
        eq_ys = collect(Set(J[dtgt][incident(J, x, dsrc)]))
        for (y1, y2) in zip(eq_ys, eq_ys[2:end])
          union!(eqclasses[dcodom], y1, y2)
          if verbose
            println("δ: $d($ddom#$x) MERGED $dcodom $y1 = $y2")
          end
          changed = true
        end
      end
    end

    # Action γ: merge coincidentally equal elements
    μ = Dict{Symbol, Vector{Pair{Int,Int}}}([o=>Pair{Int,Int}[] for o in ob(S)])
    delob = Dict{Symbol, Vector{Int}}([o=>Int[] for o in ob(S)])
    for (o, eq) in pairs(eqclasses)
      eqsets = Dict{Int,Set{Int}}()
      # Recover the equivalence classes from the union-find structure
      for x in parts(J, o)
        eqrep = find_root(eq, x)
        if haskey(eqsets, eqrep)
          push!(eqsets[eqrep], x)
        else
          eqsets[eqrep] = Set([x])
        end
      end
      if verbose
        println("eqset $o $(values(eqsets))")
      end
      # Minimum element is the representative
      for vs in values(eqsets)
        m = minimum(vs)
        delete!(vs, m)
        append!(μ[o], [v=>m for v in vs])
        append!(delob[o], collect(vs))
      end
    end
    # Replace all instances of a class with its representative in J and η
    for (d, ddom, dcodom) in zip(hom(S), dom(S), codom(S))
      dsrc, dtgt = add_srctgt(d)
      isempty(μ[ddom]) || set_subpart!(J, dsrc, replace(J[dsrc], μ[ddom]...))
      isempty(μ[dcodom]) || set_subpart!(J, dtgt, replace(J[dtgt], μ[dcodom]...))
      # remove redundant duplicate relation rows
      seen = Set()
      for (i, st) in enumerate(zip(J[dsrc], J[dtgt]))
        if st ∈ seen
          rem_part!(J, d, i)
        else
          push!(seen, st)
        end
      end
    end
    for (Iob, mapping) in collect(η)
      reps = μ[Symbol(Ob(F)[Iob])]
      if !isempty(reps)
        η[Iob] = replace(mapping, reps...)
      end
    end
    for (o, vs) in collect(delob)
      isempty(vs) || rem_parts!(J, o, sort(vs))
    end
    if !changed
      break # termination condition
    end
  end

  if changed
    error("Chase did not terminate with $n steps: $J")
  else
    return uncrel(J, codomI)
  end
end

# end # module

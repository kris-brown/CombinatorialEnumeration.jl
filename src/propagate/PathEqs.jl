using Catlab.Graphs

# Equations
###########

"""
Path Eq cached state involves lots of subsets, each of which can be
permuted, merged, or added to.

"""
function update_patheqs!(S::Sketch, J::SketchModel,f::CSetTransformation)
  μ = Dict(v=>[find_root!(J.aux.eqs[v],f[v](i)) for i in parts(dom(f), v)] for v in vlabel(S))
  verbose = false
  ntriv(v) = nv(S.eqs[v]) > 1
  if verbose println("updating path eqs w/ frozen obs $(J.aux.frozen[1])") end
  new_peqs = EQ(map(vlabel(S)) do v
    if verbose && ntriv(v) println("\tv $v") end
    return v => map(parts(J.model, v)) do p
      preim = preimage(f[v], p)
      if verbose && ntriv(v) println("\t\tp $p preim $preim") end
      if length(preim) == 0 # we have a new element
        vivv = collect(enumerate(vlabel(S.eqs[v])))
        res = Vector{Union{Nothing,Vector{Int}}}(map(vivv) do (vi, vv)
          if any(==(add_id(v)), S.eqs[v][setdiff(incident(S.eqs[v], vi, :tgt),S.eqs[v][:refl]), :elabel])
            return Int[p]
          elseif vv ∈ J.aux.frozen[1]
            return sort(collect(eq_reps(J.aux.eqs[vv])))
          else
            return nothing
          end
        end)
        res[1] = [p]
        return res
      elseif length(preim) == 1
        poss = J.aux.path_eqs[v][only(preim)]
        if verbose && ntriv(v) println("\t\tpreim=1 w/ corresponding poss $poss") end
        return map(zip(vlabel(S.eqs[v]), poss)) do (tab, tabposs)
          if isnothing(tabposs)
            if tab ∉ J.aux.frozen[1]
              return nothing
            else
              return parts(J.model, tab) |> collect
            end
          end
          new_elems = filter(x->isempty(preimage(f[tab],x)), parts(J.model,tab))
          if verbose && ntriv(v) println("\t\t\tconsidering $tab w/ μ($tabposs)+$new_elems= $(unique(μ[tab][tabposs]) ∪ new_elems)") end
          return unique(μ[tab][tabposs]) ∪ new_elems
        end
      else # we've merged elements
        pos_res = map(preim) do pre
          poss = J.aux.path_eqs[v][pre]
          return map(zip(vlabel(S.eqs[v]), poss)) do (tab, tabposs)
            μ[tab][tabposs]
          end
        end
        res = [sort(unique(union(x...))) for x in zip(pos_res...)]
        return res
      end
    end
  end)
  if verbose println("new path eqs $new_peqs") end

  J.aux.path_eqs = new_peqs
end

"""
Use set of path equalities starting from the same vertex to possibly resolve
some foreign key values.
"""
propagate_patheqs!(S::Sketch, J::SketchModel,f::CSetTransformation, c::Change) =
  vcat(Vector{Change}[propagate_patheq!(S, J,f, v, Set(vlabel(S))) for v in vlabel(S)]...)


"""
If we add an element, this can add possibilities.
If we add a relation, this can constrain the possible values.
"""
# function propagate_patheq!(S::Sketch, J::SketchModel,f::CSetTransformation,
#                            c::Change, v::Symbol)::Vector{Change}


"""
If f is now fully defined on *all* possibilities in the domain, then we can
restrict the possibilities of the codomain to the image under f.

If f is frozen, then we can pullback possibilities from a codomain and restrict
possibilities in the domain to the preimage.

If we discover, for any starting vertex, that there is an edge that has a
singleton domain and codomain, then we can add that FK via an Addition.
"""
function propagate_patheq!(S::Sketch, J::SketchModel, m, v::Symbol, tabs::Set{Symbol})
  res = Change[]
  G = S.eqs[v]
  fo, fh = J.aux.frozen
  verbose = 0 * (nv(S.eqs[v]) > 1 ? 1 : 0)

  if verbose > 1
    println("prop patheq of $v (initial changed tabs: $tabs) w/ $(J.aux.path_eqs[v])")
    show(stdout, "text/plain", first(crel_to_cset(S, J.model)))
  end
  while !isempty(tabs)
    tab = pop!(tabs)
    hs = union(Set.([hom_in(S, tab), hom_out(S, tab)])...)
    Gfks = [:elabel, :src, :tgt,[:src,:vlabel],[:tgt,:vlabel]]
    for tab_ind in findall(==(tab), vlabel(S.eqs[v]))
      if verbose > 1 println("changed tab $tab with tab ind $tab_ind") end

      # check all edges incident to the changed table
      for f_i in filter(e->G[e,:elabel] ∈ hs, edges(G))
        f, s, t, Stab, Ttab = [G[f_i,x] for x in Gfks]
        f_s, f_t = add_srctgt(f)
        Seq,Teq = [J.aux.eqs[x] for x in [Stab,Ttab]]
        if verbose > 1 println("\tcheck out edge #$f_i ($f:$Stab#$s->$Ttab#$t)") end

         # Things we can infer if map has been completely determined already
         # and if obs are frozen
         if is_total(S,J,f) && [Stab,Ttab] ⊆ fo
          im_eqs = Set([find_root!(Teq, u) for u in unique(J.model[f_t])])
          # every element in the image of f
          im = [p for p in parts(J.model, Ttab) if find_root!(Teq, p) ∈ im_eqs]
          # restrict possibilities of codom to image of f
          for (poss_root, poss) in enumerate(J.aux.path_eqs[v])
            if !isnothing(poss[t]) && poss[t] ⊈ im
              push!(tabs, Ttab)
              if verbose > 1 println("\t\t$tab#$poss_root: reducing codom of $f(#$f_i) to $(poss[t])∩$im (poss: $poss)") end
              intersect!(poss[t], im)
              msg = "Path eq imposs in tab $tab#$poss_root: reducing codom $f(#$f_i) to $(poss[t])∩$im \n poss: $(poss)"
              if isempty(poss[t]) throw(ModelException(msg)) end
            end
          end
          # restrict possibilities of dom to preimage of possibilities
          for poss in filter(poss->!any(isnothing, poss[[t,s]]), J.aux.path_eqs[v])
            preim_eqs = Set([find_root!(Seq,u) for u in J.model[vcat(incident(J.model, poss[t], f_t)...) , f_s]])
            preim = [p for p in parts(J.model, Stab) if find_root!(Seq, p)∈preim_eqs]
            if poss[s] ⊈ preim
              if verbose > 1 println("restricting dom to $(poss[s])∩$preim") end
              push!(tabs, Stab)
              intersect!(poss[s], preim)
              if isempty(poss[s]) throw(ModelException("Empty poss for $v eqs: poss $poss")) end
            end
          end
        end

        # Things that we can infer even if the map is not yet total
        # or if objects are not frozen.
        for (i, poss) in enumerate(J.aux.path_eqs[v])
          if verbose > 1 println("\t\tconsidering poss from $tab#$i: $poss") end

          # we can set the fk for f of a certain element
          if !isnothing(poss[s]) && length(poss[s]) == 1
            out = fk(S,J,f,only(poss[s])) # whether the fk is already set

            # fk is not set and there is only one possibility
            if isnothing(out) && !isnothing(poss[t]) && length(poss[t]) == 1
              if verbose > 0 println("\t\t***ADDING checking $v#$tab_ind. $f:$(only(poss[s]))->$(only(poss[t]))***") end
              push!(res, add_fk(S,J,f,only(poss[s]),only(poss[t])))

            # fk is set: we can reduce the possibilities of codom to one
            elseif !isnothing(out) && poss[t] != [out] # we can reduce the tgt to one thing
              if verbose > 1 println("\t\t\t$tab#$i we can infer $f from $(only(poss[s])) to $Ttab ($(poss[t]))") end
              if isnothing(poss[t]) || any(pt->in_same_set(J.aux.eqs[Ttab], out, pt), poss[t])
                poss[t] = [out];
              else
                throw(ModelException("Path eq impossibility"))
              end
               push!(tabs, Ttab)
            end
          end
        end
      end
    end
  end

  res
end

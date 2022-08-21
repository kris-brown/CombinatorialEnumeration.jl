
# Equations
###########

"""
With an update, elements can be permuted, merged, and added.
"""
function update_patheqs!(S::Sketch, J::SketchModel,f::CSetTransformation)
  μ = Dict(v=>[find_root!(J.eqs[v],f[v](i)) for i in parts(dom(f), v)] for v in vlabel(S))
  verbose = false
  ntriv(v) = nv(S.eqs[v]) > 1
  if verbose println("updating path eqs") end
  new_peqs = EQ(map(vlabel(S)) do v
    if verbose && ntriv(v) println("\tv $v") end
    return v => map(parts(J.model, v)) do p
      preim = preimage(f[v], p)
      if verbose && ntriv(v) println("\t\tp $p preim $preim") end
      if length(preim) == 0 # we have a new element
        res = [sort(collect(eq_reps(J.eqs[vv]))) for vv in vlabel(S.eqs[v])]
        res[1] = [p]
        return res
      elseif length(preim) == 1
        poss = J.path_eqs[v][only(preim)]
        if verbose && ntriv(v) println("\t\tpreim=1 w/ corresponding poss $poss") end
        return map(zip(vlabel(S.eqs[v]), poss)) do (tab, tabposs)
          new_elems = filter(x->isempty(preimage(f[tab],x)), parts(J.model,tab))
          if verbose && ntriv(v) println("\t\t\tconsidering $tab w/ μ($tabposs)+$new_elems= $(unique(μ[tab][tabposs]) ∪ new_elems)") end
          return unique(μ[tab][tabposs]) ∪ new_elems
        end
      else # we've merged elements
        pos_res = map(preim) do pre
          poss = J.path_eqs[v][pre]
          return map(zip(vlabel(S.eqs[v]), poss)) do (tab, tabposs)
            μ[tab][tabposs]
          end
        end
        res = [sort(unique(union(x...))) for x in zip(pos_res...)]
        return res
      end
    end
  end)
  J.path_eqs = new_peqs
end

"""
Use set of path equalities starting from the same vertex to possibly resolve
some foreign key values.
"""
propagate_patheqs!(S::Sketch, J::SketchModel,f::CSetTransformation, c::Change) =
  vcat(Vector{Change}[propagate_patheq!(S, J, f, c, v) for v in vlabel(S)]...)

"""
If we add an element, this can add possibilities.
If we add a relation, this can constrain the possible values.
"""
function propagate_patheq!(S::Sketch, J::SketchModel,f::CSetTransformation, c::Change, v::Symbol)::Vector{Change}
  # println("updating patheqs for $v")
  verbose = false && nv(S.eqs[v]) > 1
  res = Change[]
  to_check = Set{Symbol}()

  # ADDING OBJECTS
  for av in Set(vlabel(S.eqs[v]))
    added = [p for p in parts(J.model, av) if isempty(preimage(f[av], p))]
    if !isempty(added)
      if av == v
        # Effect of adding a root element is addressed in update_patheqs!
        # In the "if length(preim) == 0" branch
      else
        for (i, vvs) in enumerate(collect(J.path_eqs[v]))
          if !isempty(preimage(f[v], i))
            for (vl, poss) in zip(vlabel(S.eqs[v]), vvs)
              # what if poss==1 because things got merged, not b/c it was known?
              if vl == av && length(poss) > 1
                append!(poss, added)
                # println("added $added as possibilities for $v eq diagram, table $i. New poss: $poss")
              end
            end
          end
        end
      end
    end
  end
  # Adding edges
  for (e, srctab, tgttab) in Set(elabel(S.eqs[v], true))
    if nparts(codom(c.l), e) > 0
      union!(to_check, [srctab, tgttab])
    end
  end
  if verbose && !isempty(to_check) println("tables to check for updates: $v: $to_check") end
  return propagate_patheq!(S, J, v, to_check)
end


"""
If f is now fully defined on *all* possibilities in the domain, then we can
restrict the possibilities of the codomain to the image under f.

If f is frozen, then we can pullback possibilities from a codomain and restrict
possibilities in the domain to the preimage.

If we discover, for any starting vertex, that there is an edge that has a
singleton domain and codomain, then we can add that FK via an Addition.
"""
function propagate_patheq!(S::Sketch, J::SketchModel, v::Symbol, tabs::Set{Symbol})
  res = Change[]
  G = S.eqs[v]
  fo, fh = J.frozen
  verbose = false && nv(S.eqs[v]) > 1
  if verbose if v==:I println("prop patheq w/ $(J.path_eqs[v])") end end
  while !isempty(tabs)
    tab = pop!(tabs)
    hi, ho = Set.([hom_in(S, tab), hom_out(S, tab)])
    for tab_ind in findall(==(tab), vlabel(S.eqs[v]))
      if verbose println("changed tab $tab with tab ind $tab_ind") end

      for f_out in filter(e->G[e,:elabel] ∈ ho && G[e,[:tgt,:vlabel]] ∈ fo,
                          edges(G))
        f, s, t, Ttab = [G[f_out,x] for x in [:elabel, :src, :tgt, [:tgt,:vlabel]]]
        if verbose println("\tchecking out edge #$f_out ($f) into $Ttab") end
        for poss in J.path_eqs[v]
          if verbose println("\t\tconsidering poss $poss") end
          if length(poss[s]) == 1 # we can set the fk
            out = fk(S,J,f,only(poss[s]))
            if isnothing(out) && length(poss[t]) == 1
                push!(res, add_fk(S,J,f,only(poss[s]),only(poss[t])))
            elseif !isnothing(out) # we can set the tgt
              if verbose println("\t\t\twe can infer $f for root $(only(poss[1])) from $(only(poss[s])) to $Ttab ($(poss[t]))") end
              n_t = length(poss[t])
              intersect!(poss[t],[out])
              !isempty(poss[t]) || error("IMPOSSIBLE")
             if length(poss[t]) < n_t push!(tabs, Ttab) end
            end
          end
        end
      end
      for f_in in filter(e->G[e,:elabel] ∈ hi, edges(G))
        f, s, t, Stab, Ttab = [G[f_in,x]
          for x in [:elabel, :src, :tgt, [:src,:vlabel], [:tgt, :vlabel]]]
        f_s, f_t = add_srctgt(f)
        Seq, Teq = J.eqs[Stab], J.eqs[Ttab]
        if verbose println("\tchecking in edge #$f_in ($f) from $Stab") end
        if is_total(S,J,f)
          im_eqs = Set([find_root(Teq, u) for u in unique(J.model[f_t])])
          im = [p for p in parts(J.model, Ttab) if find_root!(Teq, p) ∈ im_eqs]
          # restrict possibilities of codom to image of f
          for poss in J.path_eqs[v]
            if poss[t] ⊈ im
              push!(tabs, Ttab)
              intersect!(poss[t], im)
            end
          end
          # restrict possibilities of dom to preimage of possibilities
          for poss in J.path_eqs[v]
            preim_eqs = Set([find_root(Seq,u) for u in J.model[vcat(incident(J.model, poss[t], f_t)...) , f_s]])
            preim = [p for p in parts(J.model, Stab) if find_root!(Seq, p)∈preim_eqs]
            if poss[s] ⊈ preim
              push!(tabs, Stab)
              intersect!(poss[s], preim)
            end
          end
        end
        for poss in J.path_eqs[v]
          if verbose println("\t\tposs $poss") end
          if f ∈ J.frozen[2]
            if verbose println("\t\tInferring backwards from completed morphism") end
            n_s = length(poss[s])
            intersect!(poss[s], fk_in(S,J,f,poss[t]))
            !isempty(poss[s]) || error("IMPOSSIBLE")
            if length(poss[s]) < n_s # made progress
              if length(poss[s]) == 1 == length(poss[t])
                push!(tabs, Stab)
                ps,pt = only.([poss[s],poss[t]])
                if !has_map(S,J,f,ps,pt)
                  push!(res, add_fk(S,J,f,ps,pt))
                end
              end
            end
          else # not frozen, but maybe we can infer something
            if length(poss[s])==length(poss[t])==1
              ps,pt = only.([poss[s],poss[t]])
              if !has_map(S,J,f,ps,pt)
                push!(res, add_fk(S,J,f,ps,pt))
              end
            end
          end
        end
      end
    end
  end
  res
end

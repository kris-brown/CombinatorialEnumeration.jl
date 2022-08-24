
# Functionality
###############

"""
Note which elements are equal due to relations actually representing functions

a₁ -> b₁
a₂ -> b₂
a₁ -> b₃
a₃ -> b₄

Because a₁ is mapped to b₁ and b₃, we deduce b₁=b₃. If the equivalence relation
has it such that a₂=a₃, then we'd likewise conclude b₂=b₄

---

If we merge elements in the domain of a function f, we look at all the elements
that share their equivalence classes. We look at all of the equivalence classes
that are mapped to by f and merge those.
"""
function quotient_functions!(S::Sketch, J::SketchModel, h::CSetTransformation,
                             m::Merge)
  L, I = codom(m.l), apex(m)
  res = Merge[]
  for v in vlabel(S)
    for eqc in parts(L, v)
      els = preimage(m.l[v], eqc)
      if length(els) > 1
        # get everything equivalent to these elements, *including* new info
        r_eqcs = Set([find_root!(J.eqs[v], e) for e in (m.r ⋅ h)[v](els)])
        r_els = findall(i->find_root!(J.eqs[v], i) ∈ r_eqcs, parts(J.model, v))
        for h in hom_out(S, v)
          s, t = add_srctgt(h)
          targ = tgt(S,h)
          ts = J.model[vcat(incident(J.model, r_els, s)...), t]
          t_eqcs = Set([find_root!(J.eqs[targ], i) for i in ts])
          if length(t_eqcs) > 1
            push!(res, Merge(S, J, Dict([targ=>[collect(t_eqcs)]])))
          end
        end
      end
    end
  end
  return res
end


"""
For each instance of a relation we add, we must check whether its domain has
been mapped to something. If it's mapped to something in a different equivalence
class, merge.
"""
function quotient_functions!(S::Sketch, J_::SketchModel, h::CSetTransformation,
                             ad::Addition)
  verbose = false
  if verbose println("quotienting with h=$(Any[k=>v for (k,v) in pairs(components(h)) if !isempty(collect(v))]) and ad $ad ")
    show(stdout,"text/plain",J_.model)
    println("addition L $(Any[k=>v for (k,v) in pairs(components(ad.l)) if !isempty(collect(v))])")
  end
  L, I = codom(ad.l), apex(ad)
  res = Merge[]
  J = J_.model
  for (d, srcobj, tgtobj) in elabel(S, true)
    dsrc, dtgt = add_srctgt(d)
    # We don't care about newly introduced srcs.
    # (But should we care about newly introduced srcs which have
    # multiple newly-introduced outgoing FKs?)
    for e in parts(L, d)
      if verbose println("d $d:$srcobj->$tgtobj #$e ad.l[srcobj] $(ad.l[srcobj])") end
      i_src = preimage(ad.l[srcobj], L[e, dsrc])
      if !isempty(i_src)
        # For such a relation, get the model element corresponding to the src
        s = (ad.r ⋅ h)[srcobj](only(i_src))
        rel = incident(J, s, dsrc) # get all the relations the source has already
        # Get the eq classes of things the source is related to
        t_eqcs = Set([find_root!(J_.eqs[tgtobj], t) for t in J[rel, dtgt]])
        if length(t_eqcs) > 1
          if verbose println("isrc $i_src t_eqcs $t_eqcs") end
          if tgtobj ∈ J_.frozen[1] throw(ModelException()) end
          push!(res, Merge(S, J_, Dict([tgtobj=>[collect(t_eqcs)]])))
        end
      end
    end
  end
  return res
end


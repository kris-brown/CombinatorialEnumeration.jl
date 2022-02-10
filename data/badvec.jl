using Test
include(joinpath(@__DIR__, "../../src/Sketch.jl"))
include(joinpath(@__DIR__, "../../src/Models.jl"))

"""
Vectors as a map from a finite, positive ℕ to some alphabet.

Creating an encoding where models have a *finite* ℕ is tricky. If you just
define ℕ=0+succ, you'll easily have models that are only valid when ℕ is
infinite. The two cospans below are both coproducts with 1, i.e. ℕ and Succ both
have a distinguished element (zero and the top element).

     s       m
   ℕ ⟵ Succ ← Mid     with next::ℕ→Succ and prev::succ→ℕ
    0 ↖ ↗ ⊤ ↖
       1    SelfNext


It was an iterative process to find this specification! There are
some weird, incorrect models that satisfy things that look like
they should work. For example, imagine a Mid number that maps to
itself via pred and next. Need a constraint that says: mapping
to yourself via next means you merge with ⊤. This requires an
extra cone object and two extra morphisms.

However, even with this, we can have a regular list with an additional PAIR of
elements which map to each other with succ and prev. Essentially, what we need
is to say that the transitive closure of `next` covers all of `Succ`. But this
kind of constraint is not expressible in the language of sketches, to my
knowledge.
"""
one = Symbol("1")

vecschema =  @acset LabeledGraph begin
  V = 6
  E = 9
  vlabel = [one, :ℕ, :Succ, :Mid, :A, :SelfNext]
  elabel = [:zero, :⊤, :succ, :prev, :next, :mid, :val, :s_next, :!]
  src    = [1,      1,  3,    3,     2,    4,    3,     6,        6]
  tgt    = [2,      3,  2,    2,     3,    3,    5,     3,        1]
end

"""Equalities"""
eqs =[(:next_prev_zero, [:zero, :next, :prev], [:zero]),
      (:next_prev_mid, [:mid, :succ, :next, :prev], [:mid, :succ]),
      (:next_top, [:⊤, :succ, :next], [:⊤]),
      (:prev_next, [:prev, :next], []),
      (:selfnext_is_top, [:!, :⊤], [:s_next])]

"""Cones"""
one_cone = Cone(LabeledGraph(), one, Pair{Int64, Symbol}[])
self_next = Cone(@acset(LabeledGraph, begin
  V=2; vlabel=[:ℕ, :Succ]; E=2; elabel=[:next,:succ]
  src=[1,2]; tgt=[2,1] end), :SelfNext, [2=>:s_next])

"""Cocones"""
ℕcoc = Cone(@acset(LabeledGraph, begin
  V = 2; vlabel = [one, :Succ] end), :ℕ, [1=>:zero, 2=>:succ])

Scoc = Cone(@acset(LabeledGraph, begin
  V = 2; vlabel = [one, :Mid] end), :Succ, [1=>:⊤, 2=>:mid])

vec_sketch = Sketch(:vec, vecschema, [one_cone, self_next],
                    [ℕcoc, Scoc], eqs)



"""
Convert a list sketch premodel into a model and then extract the lists in the
`s` table

In general, the cset structure doesn't prevent an infinite list; however, with
the colimit, limit, and diagram constraints, we can be sure this terminates.
Otherwise, we could do a DAG check on the s->s relation: incl⁻¹; pop; π₂
"""
function to_list(J_::StructACSet; premodel::Bool=false)::Vector{Int}
  J, check = premodel ? crel_to_cset(vec_sketch, J_) : J_ => true
  check || error("cannot take an incomplete model and extract lists")
  curr = only(J[:zero]) # index in ℕ
  res = Int[]
  for _ in 1:(nparts(J, :Succ))
    curr = only(incident(J, curr, :prev))
    push!(res, J[curr, :val])
    curr = J[curr, :succ]
  end
  curr == only(J[[:⊤, :succ]]) || error("problem with instance $J")
  return res
end

"""Produce a valid vec model that encodes a list of integers"""
function from_list(v::Vector{Int})::StructACSet
  J = vec_sketch.cset()
  n = length(v)
  n > 0 || error("Can only represent nonempty lists")
  [add_parts!(J, t, i) for (t, i) in
   [one=>1, :SelfNext=>1, :ℕ=>n+1, :Succ => n, :Mid => n-1, :A => maximum(v)]]
  set_subpart!(J, :val, v)
  set_subpart!(J, :zero, [1])
  set_subpart!(J, :⊤, [n])
  set_subpart!(J, :!, [1])
  set_subpart!(J, :s_next, [n])
  set_subpart!(J, :mid, collect(1:n-1))
  set_subpart!(J, :succ, collect(2:n+1))
  set_subpart!(J, :next, vcat(collect(1:n), [n]))
  set_subpart!(J, :prev, collect(1:n))
  return J
end

"""Produce an isomorphic C-Set where the ordering of N makes more sense"""
function reorder(x::StructACSet)::StructACSet
  res = deepcopy(x)
  topS = only(x[:⊤])
  Z = only(x[:zero])
  topN = only(x[[:⊤,:succ]])
  set_subpart!(res, :zero, [1])
  set_subpart!(res, :succ, 2:nparts(x, :ℕ))
  set_subpart!(res, :mid, 1:nparts(x, :Mid))
  [set_subpart!(res, f, [nparts(x, :Succ)]) for f in [:⊤, :s_next]]
  Morder = sort(parts(x, :Mid), by=i->x[i, :mid])
  Sorder = vcat(sort(setdiff(parts(x, :Mid), [topS]), by=i->x[i, :prev]), [topS])
  Norder = vcat([Z], sort(setdiff(parts(x, :ℕ), [Z, topN]),
                          by=i->findfirst(==(x[i, :next]), Sorder)), [topN])
  apply_perm(xs::Vector{Int}, p::Vector{Int}) = [p[i] for i in xs]
  perm_function(f, dom_perm, codom_perm) = apply_perm(
    dom_perm, apply_perm(f, codom_perm))
  isperm(Morder) || error("$Morder")
  isperm(Sorder) || error("$Sorder")
  isperm(Norder) || error("$Norder")
  set_subpart!(res, :next, perm_function(x[:next], Norder, Sorder))
  set_subpart!(res, :prev, perm_function(x[:prev], Sorder, Norder))
  set_subpart!(res, :succ, perm_function(x[:succ], Sorder, Norder))
  is_isomorphic(res, x) || error("Bad reordering")
  return res
end
# Example models
#---------------

# "1: 1, A: 1, Mid: 0, Succ: 1, ℕ: 2"
l1 = create_premodel(vec_sketch, from_list([1]))

# "1: 1, A: 3, Mid: 2, Succ: 3, ℕ: 4"
l321 = from_list([3,2,1])
@test to_list(l321) == [3,2,1]

# the truly empty cset has 1 which needs to be populated by limit constraint

# This doesn't satisfy colimit constraint on s (which needs an element)
# vec_one_model = vec_sketch.cset()
# add_part!(vec_one_model, one)
# vec_one = create_premodel(vec_sketch, vec_one_model)

# # This satisfies all constraints
# vec_zero_model = deepcopy(vec_one_model)
# add_part!(emp_model, :ℕ)
# set_subpart!(emp_model, :empty, [1])
# set_subpart!(emp_model, :last, [1])
# vec_zero = create_premodel(vec_sketch, emp_model)

# empty_vec_alph2_model = deepcopy(emp_model)
# add_parts!(empty_vec_alph2_model, :A, 2)
# empty_vec_alph2 = create_premodel(vec_sketch, empty_vec_alph2_model)

# # After populating the pairs, we are now missing the maps pop and push with `t`
# emp_vec_pairs_model = deepcopy(empty_vec_alph2_model)
# add_parts!(emp_vec_pairs_model, d_s, 2; π₁=[1,2], π₂=[1,1])
# empty_vec_pairs = create_premodel(vec_sketch, emp_vec_pairs_model)


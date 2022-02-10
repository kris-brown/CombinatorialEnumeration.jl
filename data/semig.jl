using Revise
using Catlab.CategoricalAlgebra
using ModelEnumeration
"""
Semigroups. An associative binary operation.
https://research-repository.st-andrews.ac.uk/handle/10023/945 Table 4.1
https://oeis.org/A027851: should be 1 5 24 188

n           | 1 | 2  | 3     | 4
# semi      | 1 | 8  | 113   | ?
# semi (iso)| 1 | 5  | 24    | 184 (not 188?!)
# cset      | 1 | 16 | 19683 | 4294967296

# looked @ | 1 |  ?  | 399
"""

p1p2, p2p3, idk, kid = map(Symbol, ["π₁×π₂","π₂×π₃","id×k","k×id"])
semig_schema = @acset LabeledGraph begin
  V = 3; E = 10; vlabel = [:s, :s2, :s3]
  elabel = [:k, :π₁, :π₂, :Π₁, :Π₂, :Π₃, p1p2, p2p3, idk, kid]
  src  = [2,  2,   2,   3,  3,   3,   3,   3,  3,   3]
  tgt  = [1,  1,   1,   1,  1,   1,   2,   2,  2,   2]
end

# s2 is pair
paircone = Cone(@acset(LabeledGraph, begin V = 2; vlabel = [:s, :s] end),
        :s2, [1=>:π₁, 2=>:π₂])

# s3 is triple
tripcone = Cone(@acset(LabeledGraph, begin V = 3; vlabel = [:s, :s, :s] end),
        :s3, [1=>:Π₁, 2=>:Π₂, 3=>:Π₃])

semieqs = [
  (:p1p2_p1, [p1p2, :π₁], [:Π₁]),
  (:p1p2_p2, [p1p2, :π₂], [:Π₂]),
  (:p2p3_p1, [p2p3, :π₁], [:Π₂]),
  (:p2p3_p2, [p2p3, :π₂], [:Π₃]),

  (:kid_p1, [kid, :π₁], [p1p2,:k]),
  (:kid_p2, [kid, :π₂], [:Π₃]),

  (:idk_p2, [idk, :π₂], [p2p3,:k]),
  (:idk_p1, [idk, :π₁], [:Π₁]),

  (:assoc, [idk, :k], [kid,:k]),
]
semig = Sketch(:semig, semig_schema, [paircone, tripcone], Cone[], semieqs);

function binfuns(i::Int)::Vector{Matrix{Int}}
  res = Matrix{Int}[]
  for x in Iterators.product([1:i for _ in 1:i^2]...)
    mat = reshape(collect(x), i, i)
    if isnothing(test_assoc(mat)) push!(res, mat); print(" $(length(res))") end
  end
  res
end

"""Find all possible extensions of an associative binfun bh 1 elem"""
function binfuns_rec(prev::Vector{Matrix{Int}})
  n, _ = size(prev[1])
  res = Matrix{Int}[]
  for p in prev
    # Need to consider existing i,j maps to the new elem
    for msk in Iterators.product([[false,true] for _ in 1:n^2]...)
      msk_ = reshape(collect(msk), n, n)
      newp = deepcopy(p)
      newp[msk_] .= (n+1)
      # Consider the products with the new element
      for x in Iterators.product([1:n+1 for _ in 1:(2*n+1)]...)
        x = vec(collect(x))
        newmat = hcat(vcat(newp, x[1:n]'),x[n+1:end])
        if isnothing(test_assoc(newmat))
          # ta = test_assoc(newmat)
          # isnothing(ta) || error("assoc last bad $newmat \n$ta")
          push!(res, newmat); print(" $(length(res))")
        end
      end
    end
  end
  return res
end

"""Doesn't check if it's actually associative"""
function from_matrix(m::Matrix{Int64})::StructACSet
  n, n_ = size(m)
  n == n_ || error("Need square matrix")
  k = vec(m)
  p1_p2 = vec(collect(Iterators.product(collect(1:n),collect(1:n))))
  p1p2d = Dict([v=>k for (k,v) in enumerate(p1_p2)])
  p1, p2, p3, p1p2_, p2p3_, idk_, kid_ = [Int[] for _ in 1:7]
  for (a,b,c) in Iterators.product(collect(1:n),collect(1:n),collect(1:n))
    push!(p1, a); push!(p2, b); push!(p3, c)
    push!(p1p2_, p1p2d[(a,b)]); push!(p2p3_, p1p2d[(b,c)])
    push!(idk_, p1p2d[(a, k[p1p2d[(b,c)]])])
    push!(kid_, p1p2d[(k[p1p2d[(a,b)]], c)])
  end
  n2, n3 = length(m), n^3
  I = semig.cset()
  add_parts!(I, :s, n)
  add_parts!(I, :s2, n2; π₁=first.(p1_p2), π₂=last.(p1_p2), k=k)
  add_parts!(I, :s3, n3; Π₁=p1,Π₂=p2, Π₃=p3,
             Dict([p1p2=>p1p2_, p2p3=>p2p3_, idk=>idk_, kid=>kid_])...)
  return I
end
"""Tests associativity of multiplications involving LAST element"""
function test_assoc_last(m::Matrix{Int})::Bool
  n,_ = size(m)
  if m[n,m[n,n]] != m[m[n,n],n]
    return false
  end
  for i in 1:n-1
    if m[i,m[n,n]] != m[m[i,n],n]
      return false
    elseif m[n,m[n,i]] != m[m[n,n],i]
      return false
    elseif m[n,m[i,n]] != m[m[n,i],n]
      return false
    end
  end
  for (i,j) in Iterators.product(1:n-1,1:n-1)
    if m[i,m[j,n]] != m[m[i,j],n]
      return false
    elseif m[i,m[n,j]] != m[m[i,n],j]
      return false
    elseif m[n,m[i,j]] != m[m[n,i],j]
      return false
    end
  end
  return true
end
"""Tests associativity"""
function test_assoc(m::Matrix{Int})::Union{Nothing, Tuple{Int,Int,Int}}
  n,_ = size(m)
  for (i,j,k) in Iterators.product(1:n,1:n,1:n)
    if m[i,m[j,k]] != m[m[i,j],k]
      return (i,j,k)
    end
  end
  return nothing
end

#
S = semig;
using CSetAutomorphisms


get_semis(i::Int) = [m for m in from_matrix.(binfuns(i)) if sat_eqs(S, create_premodel(S,m))]
s2,s3 = binfuns.([2,3]);
# s3_ = binfuns_rec(s2);
# s4_ = binfuns_rec(s3);
I2,I3 = [from_matrix.(xs) for xs in [s2,s3]];
# h2,h3,h3_ = [Set([canonical_hash(x;pres=S.cset_pres) for x in xs]) for xs in [I2,I3,I3_]];
# ns2,ns3,ns3_ = length.([s2,s3,s3_])
# nh2,nh3,nh3_ = length.([h2, h3,h3_])

#Jinit = create_premodel(S, [:s=>1]);
db = init_db(reset=true);
#chase_set(db, S, Pair{StructACSet, Defined}[Jinit=>init_defined(S, Jinit)], 2)
#ms = get_models(db, S, 1)

# I2_ = deepcopy(I2[1])
# fs = [p1p2, p2p3, idk, kid]
# for f in fs
#   set_subpart!(I2_, f, zeros(Int, 8))
# end
# J = create_premodel(S, I2_)
# eq = init_eq(S, J)
# J_old = deepcopy(J)
# d = Set([:s, :s2]) => setdiff(Set(S.schema[:elabel]), fs)
# path_eqs2!(S, J, eq, d)

Jinit = create_premodel(S, [:s=>2]);
chase_set(db, S, Pair{StructACSet, Defined}[Jinit=>init_defined(S, Jinit)], 2)
Jinit = create_premodel(S, [:s=>3]);
chase_set(db, S, Pair{StructACSet, Defined}[Jinit=>init_defined(S, Jinit)], 3)

ms = get_models(db, S, 3);


# WHY is s3 #15  not associative? kid_ = 2 not 3
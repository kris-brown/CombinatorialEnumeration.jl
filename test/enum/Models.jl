module TestModels

using Test
using CombinatorialEnumeration
using Catlab.CategoricalAlgebra
using CombinatorialEnumeration.Models: test_premodel

include(joinpath(@__DIR__, "../TestSketch.jl"));

# create_premodel
J = create_premodel(S)
@test all(x->nparts(J.model, x)  == (x == :I ? 1 : 0), S.schema[:vlabel])

# crel_to_cset for partial model
emp = @acset S.cset begin I=1; end
@test crel_to_cset(S, J) == (emp => true)

# Changes
#########
J = create_premodel(S)
newvals = @acset(S.crel, begin
  A=1;B=1;I=1;f=1;a=1;b=1;
  src_f=1;tgt_f=1;src_a=1;tgt_a=1;src_b=1;tgt_b=1 end)

ad = Addition(S,J,homomorphism(J.model, newvals), id(J.model))
@test (exec_change(S,J.model,ad) |> codom) == newvals


J = test_premodel(S,@acset(S.cset, begin
  A=5;B=5;f=[1,2,3,4,5] end))
J.aux.frozen = Set{Symbol}() => Set{Symbol}()
md = Dict([:A=>[[2,3],[4,5]], :B=>[[1,5]]])

J_ = deepcopy(J)
m = Merge(S, J_, md); # Model's eq classes are modified by




# constructing Merge
@test J_.aux.eqs[:A].parents == [1,2,2,4,4]
@test J_.aux.eqs[:B].parents == [1,2,3,4,1]
result = codom(exec_change(S, J_.model, m))
@test nparts(result, :A) == 3
@test nparts(result, :B) == 4

J = test_premodel(S,@acset(S.cset, begin A=1;B=1;f=1 end))
@test nparts(rem_dup_relations(S,J.model)|>codom, :f)==1

# Updating the addition of f->[b₁,b₂] with a merging of [a₁,a₂]
newvals = @acset(S.crel, begin
  A=2;B=2;I=1;f=2; Cone_I=1; Cone_I_apex=1
  src_f=[1,2];tgt_f=[1,2] end)
J = test_premodel(S,@acset(S.cset, begin A=2;I=1;Cone_I=1;Cone_I_apex=1;end))
J.aux.frozen = Set{Symbol}()=>Set{Symbol}()
J_orig = deepcopy(J)

ad = Addition(S,J, homomorphism(J.model, newvals; monic=true), id(J.model))
m = Merge(S, deepcopy(J), Dict(:A=>[[1,2]]))
J_update = exec_change(S,J.model,m);
J.model = codom(J_update)
ad2 = update_change(S, J, J_update, ad);
@test nparts(apex(ad), :A) == 2
@test nparts(apex(ad2), :A) == 1


# Merging overlapping additions
J = test_premodel(S, @acset(S.cset, begin A=2;B=2 end))
a1 = add_fk(S, J, :f, 1, 1)
a2 = add_fk(S, J, :g, 1, 2)
a3 = add_fk(S, J, :f, 1, 2)
a = merge(S,J,a1,a2)
@test codom(a.l) == @acset S.crel begin
  A=1;B=2;f=1;g=1;src_f=1;src_g=1;tgt_f=1;tgt_g=2 end
@test apex(a) == @acset S.crel begin A=1;B=2; end
a = merge(S,J,[a1,a2,a3])

# Merging overlapping merges
J = create_premodel(S,Dict(:A=>5,:B=>5))
md = Dict([:A=>[[2,3,5]], :B=>[[1,5]]])

J_ = deepcopy(J)
m = Merge(S, J_, md);

J_ = deepcopy(J)
md1 = Dict([:A=>[[2,3]]])
m1= Merge(S, J_, md1);
J_ = deepcopy(J)
md2 = Dict([:A=>[[3,5]]])
m2= Merge(S, J_, md2);
J_ = deepcopy(J)
md3 = Dict([:B=>[[1,5]]])
m3= Merge(S, J_, md3);

res_m = merge(S,J_, [m1,m2,m3])

end # module

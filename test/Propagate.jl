
module TestPropagate

using Revise
using Test
using ModelEnumeration
using DataStructures
using ModelEnumeration.Models: EQ, test_premodel

const no_freeze = Set{Symbol}()=>Set{Symbol}()

# Sketches
##########

# default test case
include(joinpath(@__DIR__, "TestSketch.jl"));

# Test model
#-----------
J0model = @acset S.cset begin
  A=3;B=3;E=3;C=3;I=1; a=1;b=1;f=[1,2,3];g=[1,2,3];c=[1,2,3];e=[1,2,3];
end

J0 = test_premodel(S,J0model,freeze=[:B])



# Test function propagation
#--------------------------
# Adding a (disjoint) aₙ -f,g-> bₙ
# This should add a new equalizer cone
R = @acset(S.crel, begin A=1;B=1;f=1;g=1;src_f=1;tgt_f=1;src_g=1;tgt_g=1 end)
ad = Addition(S, J0, R)
J0_ = deepcopy(J0)
m, ch = propagate!(S, J0_, ad)
@test codom(only(ch).l) == @acset S.crel begin A=1;E=1;e=1;src_e=1;tgt_e=1 end

# merge cone apexes
me = Merge(S, deepcopy(J0), Dict([:E=>[[1,2]]]))
J0_ = deepcopy(J0);
m, ch = propagate!(S, J0_, me)
@test codom(only(ch).l) == @acset S.crel begin A=1 end
@test apex(only(ch)) == @acset S.crel begin A=2 end

# merge A1 and A2: should induce merge of B1 and B2 as well as E1 and E2
J0 = test_premodel(S,J0model) # nothing frozen
me = Merge(S, deepcopy(J0), Dict([:A=>[[1,2]]]))
J0_ = deepcopy(J0)
m, ch = propagate!(S, J0_, me)
@test all(nparts(codom(c.l),v)==1 && nparts(apex(c),v)==2
          for (c,v) in zip(ch,[:B,:E]))


# Test path eq propagation
#-------------------------

Jpth_model = @acset S.crel begin A=3; B=3; I=1 end

Jpth = test_premodel(S,Jpth_model,freeze=[:A,:B])
adpth_ia = add_fk(S, Jpth, :a, 1, 1)

Jp = deepcopy(Jpth)
m, ch = propagate!(S,Jp,adpth_ia)
@test isempty(ch) # path_eqs are changed, but nothing we can do yet
@test Jpth.path_eqs[:I] == [[[1],[1,2,3],[1,2,3]]] # before
@test Jp.path_eqs[:I] == [[[1],[1,2,3],[1]]] # after
ads = merge(S,Jp, [
  add_fk(S, Jp, :f, i, j) for (i,j) in [1=>2, 2=>3, 3=>1]])
m, ch = propagate!(S, Jp, ads)
# we infer that I->B must be 1.
expect = @acset S.crel begin I=1;A=3;B=3;f=3;a=1;b=1;
  src_a=1;tgt_a=1;src_b=1;tgt_b=1; src_f=[1,2,3]; tgt_f=[1,2,3]end
@test is_isomorphic(codom(exec_change(S,Jp.model,only(ch))), expect)

# Test backwards inference given a frozen "f"
Jpth = test_premodel(S,Jpth_model,freeze=[:A,:B])

adpth_ib = add_fk(S, Jpth, :b, 1, 1)
Jp = deepcopy(Jpth)
m, ch = propagate!(S,Jp,adpth_ib)
ads = merge(S,Jp, [
  add_fk(S, Jp, :f, i, j) for (i,j) in [1=>2,2=>3,3=>1]])
m, ch = propagate!(S,Jp,ads)
@test is_isomorphic(codom(exec_change(S,Jp.model,only(ch))), expect)

# Pullback tests
################

"""pullback sketch (to test limits)
      π₁
   D - - > B
   |       |
π₂ |       | g
   v       v
   A  -->  C
      f
"""
pbschema = @acset LabeledGraph begin V=4; E=4;
  vlabel=[:A,:B,:C,:D]; elabel=[:f,:g,:π₁,:π₂]; src=[1,2,4,4];tgt=[3,3,1,2]
end
csp = @acset LabeledGraph begin V=3; E=2;
  vlabel=[:A,:B,:C]; elabel=[:f,:g]; src=[1,2]; tgt=[3,3]
end
PB = Sketch(:PB, pbschema; cones=[Cone(csp,:D,[1=>:π₁,2=>:π₂])])


# Initial data
#-------------
PBmodel = @acset PB.cset begin A=3;B=3;C=3;D=3;f=[1,1,3];g=[1,2,3];π₁=[1,2,3]; π₂=[1,1,3]
end

PB0 = test_premodel(PB, PBmodel)

# Changes
#--------

# Merging pb diagram elems
PB0_ = deepcopy(PB0);
me_PBC = Merge(PB, PB0_, Dict([:C=>[[2,3]]]))

# Merging pb apex elems
PB0_ = deepcopy(PB0);
me_PBD = Merge(PB, PB0_, Dict([:D=>[[2,3]]]))


# Pushout tests
###############

# pushout sketch (to test colimits)
PO = dual(PB)
POmodel = @acset PO.cset begin A=3;B=3;C=3;D=3;f=[1,1,3];g=[1,2,3];π₁=[1,2,3];π₂=[1,1,3]
end
PO0 = test_premodel(PO,POmodel)

# merge two elements in the diagram leg
#----------------------------------
PO0_ = deepcopy(PO0);
me_POA = Merge(PO, PO0_, Dict([:A=>[[2,3]]]))
PO0_ = deepcopy(PO0);
m, chs = propagate!(PO,PO0_,me_POA)
ch1,ch2 = chs
# there are two changes that result. We quotient D via functionality of π₁. We
# also quotient D because π₁ is a cocone leg and there are multiple apex
# elements that are pointed to by the same connected component
@test nparts(apex(ch1), :D) == 2
@test apex(ch1) == apex(ch2)
@test codom(ch1.l) == codom(ch2.l)
@test num_groups(PO0_.cocones[1][1]) == 2

# merge two elements in the diagram apex
#---------------------------------------
PO0_ = deepcopy(PO0);
me_POC = Merge(PO, PO0_, Dict([:C=>[[2,3]]]))
PO0_ = deepcopy(PO0);
m, ch = propagate!(PO,PO0_,me_POC)
@test num_groups(PO0_.cocones[1][1]) == 2
length(ch) == 3 # merge D due to cocone constraint, A/B due to functionality


# Add a FK which makes it impossible for two groups to be connected
#-----------------------------------------------------------------------
PO1model = @acset PO.cset begin A=1;B=2;C=1;D=1;π₁=[1];π₂=[1,1]
end

PO1 = test_premodel(PO,PO1model,freeze=[:A,:B,:C])

ad = add_fk(PO,PO1,:f,1,1)
PO1_ = deepcopy(PO1)
@test_throws(ModelException,propagate!(PO,PO1_,ad))

# Add a FK which leaves it possible for two groups to be connected
#-----------------------------------------------------------------------
ad_extraC = deepcopy(ad)
adL = deepcopy(codom(ad_extraC.l)); add_part!(adL, :C)
ad_extraC = Addition(PO, PO1, homomorphism(apex(ad), adL), ad.r)
PO1_ = deepcopy(PO1)
propagate!(PO,PO1_,ad_extraC)

end # module

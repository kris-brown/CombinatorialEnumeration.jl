
module TestPropagate

# using Revise
using Test
using ModelEnumeration
using DataStructures
using ModelEnumeration.Models: EQ

const no_freeze = Set{Symbol}()=>Set{Symbol}()

# Sketches
##########

# default test case
include(joinpath(@__DIR__, "TestSketch.jl"));

# Test model
#-----------
J0model = @acset S.crel begin
  A=3;B=3;E=3;C=3;I=1; a=1;b=1;f=3;g=3;c=3;e=3;
  src_f=[1,2,3]; tgt_f=[1,2,3]; src_g=[1,2,3]; tgt_g=[1,2,3]
  src_a=1; tgt_a=1; src_b=1; tgt_b=1;
  src_c=[1,2,3]; tgt_c=[1,2,3]; src_e=[1,2,3]; tgt_e=[1,2,3];
end
J0eqs = Dict([v=>IntDisjointSets(nparts(J0model, v)) for v in vlabel(S)])
J0cocones = [IntDisjointSets(6) => vcat([[x=>i for i in 1:3]
                                         for x in [:A,:B]]...),
             IntDisjointSets(0)=>Pair{Symbol,Int}[]]
for (i,j) in [1=>4,2=>5,3=>6]
  union!(J0cocones[1][1], i, j)
end

J0patheqs = EQ(map(collect(S.eqs)) do (v,d)
  v=> (v == :I ?  [[[1], [1,2,3],[1,2,3]]] : [[[p]] for p in parts(J0model, v)])
end)

J0 = SketchModel(J0model, J0eqs, J0cocones, J0patheqs, no_freeze)



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
me = Merge(S, deepcopy(J0), Dict([:A=>[[1,2]]]))
J0_ = deepcopy(J0)
m, ch = propagate!(S, J0_, me)
@test all(nparts(codom(c.l),v)==1 && nparts(apex(c),v)==2
          for (c,v) in zip(ch,[:B,:E]))


# Test path eq propagation
#-------------------------

Jpth_model = @acset S.crel begin A=3; B=3; I=1 end
Jpth_eqs = Dict([v=>IntDisjointSets(nparts(Jpth_model, v)) for v in vlabel(S)])
Jpth_cocones = [IntDisjointSets(9) => vcat([[x=>i for i in 1:3] for x in [:C,:A,:B]]...), IntDisjointSets(0)=>Pair{Symbol,Int}[]]
Jpth = SketchModel(Jpth_model, Jpth_eqs, Jpth_cocones, J0patheqs,
                   Set([:A,:B])=>Set{Symbol}())

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
exp = @acset S.crel begin I=1;A=3;B=3;f=3;a=1;b=1;
  src_a=1;tgt_a=1;src_b=1;tgt_b=1; src_f=[1,2,3]; tgt_f=[1,2,3]end
@test is_isomorphic(codom(exec_change(S,Jp.model,only(ch))), exp)

# Test backwards inference given a frozen "f"
adpth_ib = add_fk(S, Jpth, :b, 1, 1)
Jp = deepcopy(Jpth)
m, ch = propagate!(S,Jp,adpth_ib)
ads = merge(S,Jp, [
  add_fk(S, Jp, :f, i, j) for (i,j) in [1=>2,2=>3,3=>1]])
m, ch = propagate!(S,Jp,ads)
@test is_isomorphic(codom(exec_change(S,Jp.model,only(ch))), exp)

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
PBmodel = @acset PB.crel begin A=3;B=3;C=3;D=3;f=3;g=3;π₁=3;π₂=3
  src_f=[1,2,3];src_g=[1,2,3]; tgt_f=[1,1,3]; tgt_g=[1,2,3]
  src_π₁=[1,2,3]; src_π₂=[1,2,3]; tgt_π₁=[1,2,3]; tgt_π₂=[1,1,3]
end
PBeqs = Dict([v=>IntDisjointSets(3) for v in vlabel(PB)])
PBpatheqs =EQ([v=>[[[i]] for i in parts(PBmodel, v)] for v in vlabel(PB)])

PB0 = SketchModel(PBmodel, PBeqs, typeof(J0cocones)(), PBpatheqs, no_freeze)

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
POmodel = @acset PO.crel begin A=3;B=3;C=3;D=3;f=3;g=3;π₁=3;π₂=3
  src_f=[1,2,3];src_g=[1,2,3]; tgt_f=[1,1,3]; tgt_g=[1,2,3]
  src_π₁=[1,2,3]; src_π₂=[1,2,3]; tgt_π₁=[1,2,3]; tgt_π₂=[1,1,3]
end
POdata = [IntDisjointSets(9)=>vcat([[x=>i for i in 1:3] for x in [:C,:A,:B]]...)]
for (a,b) in [1=>4,1=>7,2=>5,2=>8,3=>6,3=>9]
  union!(POdata[1][1], a,b)
end
PO0 = SketchModel(POmodel, PBeqs, POdata, PBpatheqs, no_freeze)

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
PO1model = @acset PO.crel begin A=1;B=2;C=1;D=1;π₁=1;π₂=2
  src_π₁=1; src_π₂=[1,2]; tgt_π₁=1; tgt_π₂=1
end
PO1eqs = Dict([v=>IntDisjointSets(nparts(PO1model,v)) for v in vlabel(PB)])
PO1patheqs =EQ([v=>[[[i]] for i in parts(PO1model, v)] for v in vlabel(PB)])

PO1 = SketchModel(PO1model, PO1eqs, [IntDisjointSets(4)=>[:C=>1,:A=>1,:B=>1,:B=>2]], PO1patheqs,
                  Set([:A,:B,:C])=>Set{Symbol}())

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

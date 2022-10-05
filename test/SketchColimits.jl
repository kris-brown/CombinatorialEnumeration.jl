module TestSketchColimits


using Revise
using Test
using Catlab, Catlab.CategoricalAlgebra, Catlab.Present
using Catlab.Programs, Catlab.WiringDiagrams, Catlab.Graphics
using Catlab.Graphs: path_graph, Graph, SchReflexiveGraph
using Catlab.CategoricalAlgebra.FinCats: FinCatPresentation
using CombinatorialEnumeration
include(joinpath(@__DIR__, "TestSketch.jl"));


# Free category
###############
C = FinCat(path_graph(Graph, 3))
CC = mkFinCatCSet(C)
C_ = mkFinCatGraph(CC)
@test C == C_

# Category with equations
#########################
G = @acset(Graph, begin V=3;E=3;src=[1,1,2];tgt=[2,3,3]end);
C = FinCat(G, [[[1,3],[2]]]);
CC = mkFinCatCSet(C);
C_ = mkFinCatGraph(CC);
@test C == C_

G = @acset(Graph, begin V=2;E=2;src=[1,2];tgt=[2,1]end);
C = FinCat(G, [[[1,2],Path([], 1, 1)]]);
CC = mkFinCatCSet(C);
C_ = mkFinCatGraph(CC);
@test C == C_



# Labeled Category
##################
C = FinCat(SchReflexiveGraph)
CC = mkLabeledFinCatCSet(C)
C_ = mkFinCatPresentation(CC);
@test C == C_

# Schema <-> CSet
#################
SS = mkLabeledSketchCSet(S);
S_ = Sketch(SS);
@test is_isomorphic(S_.schema, S.schema)
@test is_isomorphic(S_.eqs[:I], S.eqs[:I])

# Glue FinCats together via pushout
##################################
Singl = FinCat(Graph(1));
G = @acset(Graph, begin V=3;E=3;src=[1,1,2];tgt=[2,3,3]end);
C = FinCat(G, [[[1,3],[2]]]);

F = Span([FinFunctor([i],[],Singl,C) for i in [1,3]]...);
res = pushout(F...);
@test all(is_functorial,res)
ares = apex(res)
@test length(equations(ares))==2

# Fincat colimits using oapply now

r = @relation (x,y) where (x::X,y::Y) begin R(x,y) end;
L,R = coapply(r, [F]); # same one as before

r = @relation (x,y,z) where (x::X, y::Y, z::Z) begin R(x,y); S(y,z); T(z,x) end;
# to_graphviz(r;box_labels=true)

res = coapply(r, [F,F,F]); # to_graphviz(apex(res).graph; prog="neato")

# with named presentations
@present SchOne(FreeSchema) begin X::Ob end
One = FinCat(SchOne)
C = FinCat(SchReflexiveGraph)
C2 = rename(C, Dict(:V=>:V2,:src=>:src2,:tgt=>:tgt2,:refl=>:refl2)) |> codom
F = Span([FinFunctor(Dict(:X=>:E),Dict(),One,c) for c in [C,C2]]...);

symbs1 = [:V,:E,:id_V,:id_E,:src,:tgt,:refl]
symbs = [Symbol("$x$y") for x in symbs1 for y in Symbol.(["","2","3"])]
tc = (Label=FinFunction(Dict([x=>x for x in symbs])),)
L,R = pushout(F...; tcs=[tc for _ in 1:2]);
@test all(is_functorial, [L,R])

r = @relation (x,y) where (x::X,y::Y) begin R(x,y) end;
L,R = coapply(r, [F]; tcs=[tc for _ in 1:2]); # same one as before

r = @relation (x,y,z) where (x::X, y::Y, z::Z) begin R(x,y); S(y,z); T(z,x) end;
# to_graphviz(r;box_labels=true)

C2 = rename(C, Dict(:V=>:V2,:src=>:src2,:tgt=>:tgt2,:refl=>:refl2)) |> codom
C3 = rename(C, Dict(:V=>:V3,:src=>:src3,:tgt=>:tgt3,:refl=>:refl3)) |> codom
F = Span([FinFunctor(Dict(:X=>:E),Dict(),One,c) for c in [C,C2]]...);
G = Span([FinFunctor(Dict(:X=>:E),Dict(),One,c) for c in [C2,C3]]...);
H = Span([FinFunctor(Dict(:X=>:E),Dict(),One,c) for c in [C3,C]]...);

res = coapply(r, [F,G,H]; tcs=[tc for _ in 1:3]);
# (presentation(apex(res)))|>to_graphviz

# Glue Sketches together via pushout
####################################
Singl = FinCat(Graph(1))

I = Sketch(@acset LabeledGraph begin V=3;E=3; vlabel=[:X, :I, :Z];elabel=[:x,:i,:z];src=[1,2,3];tgt=[1,2,3] end)
Sp = presentation(mkFinCatPresentation(S))
# Sp |> to_graphviz
rn = Dict([Symbol(x)=>Symbol("$(x)2") for x in [Sp.generators[:Ob];Sp.generators[:Hom];add_id.(Symbol.(Sp.generators[:Ob]))]])
S2 = rename(S, rn) |> codom;
B,Zg,Ig = Sp.generators[:Ob][[2,5,6]]
A2,Z2g,I2g = presentation(mkFinCatPresentation(S2)).generators[:Ob][[1,5,6]]
SketchMorphismL = SketchMorphism(I,S, Dict(:X=>:B, :I=>:I, :Z=>:Z), Dict(:x=>id(B),:i=>id(Ig), :z=>id(Zg)));
SketchMorphismR = SketchMorphism(I,S2, Dict(:X=>:A2,:I=>:I2, :Z=>:Z2), Dict(:x=>id(A2),:i=>id(I2g), :z=>id(Z2g)));
@test all(is_functorial,[x.f for x in [SketchMorphismL, SketchMorphismR]])
F = Span(SketchMorphismL,SketchMorphismR)
r = @relation (x,y) where (x::X,y::Y) begin R(x,y) end;
symbs1 = [vlabel(S);elabel(S);add_id.(vlabel(S))]
symbs = [Symbol("$x$y") for x in symbs1 for y in Symbol.(["","2"])]
tc_ = Dict([:B=>:M,:A2=>:M,:id_A2=>:id_M,:id_B=>:id_M,:I2=>:I,:Z2=>:Z,:id_I2=>:id_I,:id_Z2=>:id_Z])
tcs = [(Label=FinFunction(merge(Dict(x=>x for x in symbs), tc_)),) for _ in 1:2]
res = coapply(r, [F]; tcs=tcs);
# show_lg(apex(res).schema)

end # module

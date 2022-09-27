module TestSketchColimits

"""
REDO THIS AFTER COLIMITS OF LOOSEACSETTRANSFORMATIONS (w/ provided type comps)
IS IMPLEMENTED.
"""
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
SS = SketchCSet(S);
S_ = Sketch(SS, vlabel(S), elabel(S));
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
to_graphviz(r;box_labels=true);

res = coapply(r, [F,F,F]); # to_graphviz(apex(res).graph; prog="neato")

# with named presentations
@present SchOne(FreeSchema) begin X::Ob end
One = FinCat(SchOne)
C = FinCat(SchReflexiveGraph)
F = Span([FinFunctor(Dict(:X=>:E),Dict(),One,C) for _ in 1:2]...);
res = pushout(F...);
@test all(is_functorial, res)

r = @relation (x,y) where (x::X,y::Y) begin R(x,y) end;
res = coapply(r, [F]); # same one as before

r = @relation (x,y,z) where (x::X, y::Y, z::Z) begin R(x,y); S(y,z); T(z,x) end;
# to_graphviz(r;box_labels=true)

res = coapply(r, [F,F,F]);
# (presentation(apex(res)))|>to_graphviz

# Glue Sketches together via pushout
####################################
Singl = FinCat(Graph(1))


I = Sketch(@acset LabeledGraph begin V=1;E=1; vlabel=[:X];elabel=[:x];src=1;tgt=1 end)
A, B = presentation(mkFinCatPresentation(S)).generators[:Ob][1:2]
SketchMorphismL = SketchMorphism(I,S, Dict(:X=>:B), Dict(:x=>id(B)));
SketchMorphismR = SketchMorphism(I,S, Dict(:X=>:A), Dict(:x=>id(A)));
F = Span(SketchMorphismL,SketchMorphismR)
r = @relation (x,y) where (x::X,y::Y) begin R(x,y) end;
res = coapply(r, [F]); # need to figure how to get this to be multicospan of SketchMorphisms...
                       # requires coming up with a name for merged elements


end # module

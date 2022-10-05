using Revise
using Test
using Catlab.CategoricalAlgebra
using Catlab.Graphs: SchGraph
using CombinatorialEnumeration
using CombinatorialEnumeration.Sketches: non_id

function prod_sketch(A_ov,B_ov)

  C, D = map([A_ov, B_ov]) do (X, X_ov)
    X = deepcopy(X)
    for v in X_ov
      i = only(incident(X,v,:vlabel))
      add_edge!(X, i, i; elabel=Symbol("[$v]"))
    end
    return X
  end

  Ty = @acset LabeledGraph begin V=1; E=3; refl=3; src=1; tgt=1;
      vlabel=[:X]; elabel=[:G,:S,:i]
  end

  C_Ty, D_Ty = map(zip([C,D], [:G=>:S,:S=>:G])) do (X, (sym, opsym))
    bracketobs = (x->Symbol("[$x]")).(X[:vlabel])
    strat = [i for (i,e) in enumerate(X[:elabel]) if e ∈ bracketobs]
    tc = (Label=FinFunction(Dict([[v=>:X for v in X[:vlabel]]...,
                                  [e=>sym for e in X[non_id(X), :elabel]]...,
                                  [e=>:i for e in X[[:refl,:elabel]]]...,
                                  [e=>opsym for e in X[strat, :elabel]]...])),)
    only(homomorphisms(X,Ty; type_components=tc))
  end

  tcs = map([1,2]) do i
    prs = [[Symbol("($(Cv),$Dv)")=>[Cv,Dv][i]
          for (Cv, Dv) in vec(collect(Iterators.product(C[x], D[x])))]
          for x in [:vlabel, :elabel]]
    (Label=FinFunction(Dict(vcat(prs...))),)
  end

  pullback(C_Ty,D_Ty; tcs=tcs);
end

GrphS = Sketch(SchGraph).schema
res = prod_sketch(GrphS=>[:V,:E],GrphS=>[:V,:E]);


res = prod_sketch(GrphS=>[:V,:E],
                  JointSurj.schema=>[:A,:B,:C]);

                  
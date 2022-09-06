module TestSketchCat

using Revise
using CombinatorialEnumeration
using Catlab.Theories

include(joinpath(@__DIR__, "TestSketch.jl"));


Tschema = @acset LabeledGraph begin V=5; E=5+7; refl=8:12;
  vlabel=[:Aa,:Bb,:CE,:Zz,:Ii]
  elabel=[:fg,:hh,:cc,:ee,:zz,:aa,:bb,:idA,:idB,:idCE,:idZ,:idI,]
  src   =[1,  1,  2,  3,  4,  5,  5,  1,   2,    3,   4,   5]
  tgt   =[2,  2,  3,  1,  1,  1,  2,  1,   2,    3,   4,   5]
end

Teqs = [[[:bb], [:aa,:fg]]]
cone_g = @acset LabeledGraph begin V=3; E=3+2; refl=3:5; vlabel=[:Aa,:Aa,:Bb];
        elabel=[:fg,:fg,:idA,:idA,:idB]; src=[1,2,1,2,3,]; tgt=[3,3,1,2,3,] end

Tcones = [Cone(cone_g, :CE, [1=>:ee, 2=>:ee]), Cone(:Ii)]

cocone_g = @acset LabeledGraph begin V=3; E=3+2; refl=3:5; vlabel=[:Aa,:Bb,:Bb];
  elabel=[:fg,:fg,:idA,:idB,:idB,]; src=[1,1,1,2,3,]; tgt=[2,3,1,2,3,] end

Tcocones = [Cone(cocone_g, :CE, [2=>:cc, 3=>:cc]), Cone(:Zz)]

T = Sketch(:T_, Tschema; cones=Tcones, cocones=Tcocones, eqs=Teqs)

# no need to manually specify where id arrows go
f = homomorphism(to_refl(S.schema), to_refl(T.schema);
                 initial=(V=[1,2,3,3,4,5],
                          E=Dict([1=>1,2=>1,3=>3,4=>4,5=>5,6=>6,7=>7])))

# example map that squashes f and g together, as well as C and E.
ST = SketchHom(S,T,f)


end # module

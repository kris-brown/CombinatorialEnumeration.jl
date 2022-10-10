
using CombinatorialEnumeration
using Catlab.CategoricalAlgebra

"""
Example sketch with a path equation, equalizer, coequalizer, 0, and 1 object.

  e  f&g  c
E ↪ A ⇉ B ↠ C
   z↑ ↖a↑b
    Z  1
"""

schema = @acset LGraph begin V=6; E=6+7; refl=1:6;
  vlabel=[:A,:B,:C,:E,:Z,:I]
  elabel=[:id_A,:id_B,:id_C,:id_E,:id_Z,:id_I,:f,:g,:c,:e,:z,:a,:b]
  src   =[1,   2,   3,   4,   5,   6,   1, 1, 2, 4, 5, 6, 6]
  tgt   =[1,   2,   3,   4,   5,   6,   2, 2, 3, 1, 1, 1, 2]
end

eqs = [[[:b], [:a,:f]]]
cone_g = @acset LGraph begin V=3; E=3+2; refl=1:3; vlabel=[:A,:A,:B];
        elabel=[:id_A,:id_A,:id_B,:f,:g]; src=[1,2,3,1,2]; tgt=[1,2,3,3,3] end

cones = [Cone(cone_g, :E, [1=>:e, 2=>:e]), Cone(:I)]

cocone_g = @acset LGraph begin V=3; E=3+2; refl=1:3; vlabel=[:A,:B,:B];
  elabel=[:id_A,:id_B,:id_B,:f,:g]; src=[1,2,3,1,1]; tgt=[1,2,3,2,3] end

cocones = [Cone(cocone_g, :C, [2=>:c, 3=>:c]), Cone(:Z)]

S = Sketch(schema; cones=cones, cocones=cocones, eqs=eqs)

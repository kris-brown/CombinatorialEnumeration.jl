# using Revise
using CombinatorialEnumeration
using Catlab.CategoricalAlgebra

"""
Example sketch with a path equation, equalizer, coequalizer, 0, and 1 object.

  e  f&g  c
E ↪ A ⇉ B ↠ C
   z↑ ↖a↑b
    Z  1
"""

schema = @acset LabeledGraph begin V=6; E=6+7; refl=8:13;
  vlabel=[:A,:B,:C,:E,:Z,:I]
  elabel=[:f,:g,:c,:e,:z,:a,:b,:idA,:idB,:idC,:idE,:idZ,:idI,]
  src   =[1, 1, 2, 4, 5, 6, 6, 1,   2,   3,   4,   5,   6,   ]
  tgt   =[2, 2, 3, 1, 1, 1, 2, 1,   2,   3,   4,   5,   6,   ]
end

eqs = [[[:b], [:a,:f]]]
cone_g = @acset LabeledGraph begin V=3; E=3+2; refl=3:5; vlabel=[:A,:A,:B];
        elabel=[:f,:g,:idA,:idA,:idB]; src=[1,2,1,2,3,]; tgt=[3,3,1,2,3,] end

cones = [Cone(cone_g, :E, [1=>:e, 2=>:e]), Cone(:I)]

cocone_g = @acset LabeledGraph begin V=3; E=3+2; refl=3:5; vlabel=[:A,:B,:B];
  elabel=[:f,:g,:idA,:idB,:idB]; src=[1,1,1,2,3]; tgt=[2,3,1,2,3,] end

cocones = [Cone(cocone_g, :C, [2=>:c, 3=>:c]), Cone(:Z)]

S = Sketch(:test, schema; cones=cones, cocones=cocones, eqs=eqs)

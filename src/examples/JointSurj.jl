module JointSurjSketch
export JointSurj

using Catlab.CategoricalAlgebra
using ...Core

"""
Using the surjection encoding, this is a sketch for a pair of maps that are
*jointly surjective*.

         A
    π₁ ↙   ↘ f
PB ⇉ A+B ↠  C
    π₂   ↖ ↗ g
          B
"""
schema = @acset LGraph begin
  V=5; E=7; vlabel=[:A,:B,:C,:A_B,:PB];
  elabel=[:f,:g,:iA,:iB,:p1,:p2,:c];
  src=[1,2,1,2,5,5,4]; tgt=[3,3,4,4,4,4,3]
end

"""PB is a pullback: all pairs of A+B that agree on their value in c"""
c = Cone(@acset(LGraph, begin V=3;E=2;vlabel=[:A_B,:A_B,:C];
                elabel=[:c,:c];src=[1,2]; tgt=3 end,),
          :PB, [1=>:p1,2=>:p2])

"""(C,c) is the coequalizer of PB's legs"""
cc = Cone(@acset(LGraph, begin V=3;E=2;vlabel=[:PB,:A_B,:A_B];
                  elabel=[:p1, :p2]; src=1; tgt=2 end),
          :C, [2=>:c, 3=>:c])
"""A_B is the coproduct A+B"""
a_b = Cone(@acset(LGraph, begin V=2;vlabel=[:A,:B] end),
           :A_B, [1=>:iA,2=>:iB])

eqs = [[[:f],[:iA,:c]],
       [[:g],[:iB,:c]]]
       
JointSurj = Sketch(schema, cones=[c], cocones=[cc,a_b,],eqs=eqs)

end # module

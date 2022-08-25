module JointSurj

# using Revise
using Catlab.CategoricalAlgebra
using ModelEnumeration

"""
Using the surjection encoding, this is a sketch for a pair of maps that are *jointly surjective*.
"""
schema = @acset LabeledGraph begin
  V=5; E=7; vlabel=[:A,:B,:C,:A_B,:PB];
  elabel=[:f,:g,:iA,:iB,:p1,:p2,:c];
  src=[1,2,1,2,5,5,4]; tgt=[3,3,4,4,4,4,3]
end

"""PB is a pullback: all pairs of A+B that agree on their value in c"""
c = Cone(@acset(LabeledGraph, begin V=3;E=2;vlabel=[:A_B,:A_B,:C];
                elabel=[:c,:c];src=[1,2]; tgt=3 end,),
          :PB, [1=>:p1,2=>:p2])

"""(C,c) is the coequalizer of PB's legs"""
cc = Cone(@acset(LabeledGraph, begin V=2;E=2;vlabel=[:PB,:A_B];
                  elabel=[:p1, :p2]; src=1; tgt=2 end),
          :C, [2=>:c])
"""A_B is the coproduct A+B"""
a_b = Cone(@acset(LabeledGraph, begin V=2;vlabel=[:A,:B] end),
           :A_B, [1=>:iA,2=>:iB])

eqs = [[[:f],[:iA,:c]],[[:g],[:iB,:c]]]
S = Sketch(:JointSurj, schema, cones=[c], cocones=[cc,a_b,],eqs=eqs)

#function runtests()
  I = @acset S.cset begin A=2;B=2;C=2 end
  es = init_db(S,I, [:A,:B,:C])
  chase_db(S,es)
  ms = [get_model(es,S,i) for i in es.models];

  expected = @acset S.cset begin a=3;b=2;c=5;
    d=[1,1,2];d0=[1,1,2,2,3];d1=[1,2,1,2,3] end
  is_isomorphic(get_model(es,S,only(es.models)), expected)

  # we can also, knowing what A and B are, freeze A+B and get the answer more efficiently
  # TODO



#end

end # module

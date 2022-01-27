include(joinpath(@__DIR__, "../../src/Sketch.jl"))

"""
Semigroups.
"""

p1p2, p2p3, idk, kid = map(Symbol, ["π₁×π₂","π₂×π₃","id×k","k×id"])
semig = Sketchinit(@acset LabeledGraph begin
    V = 3
    E = 10
    vlabel = [:s, :s2, :s3]
    elabel = [:k, :π₁, :π₂, :Π₁, :Π₂, :Π₃, p1p2, p2p3, idk, kid]
    src    = [2,  2,   2,   3,    3,   3,   3,   3,    3,   3]
    tgt    = [1,  1,   1,   1,    1,   1,   2,   2,    2,   2]
end );

# s2 is pair
pairconed = @acset LabeledGraph begin
    V = 2
    vlabel = [:s, :s]
end

paircone = Cone(pairconed, :s3, [1=>:π₁, 2=>:π₂])

# s3 is triple
tripconed = @acset LabeledGraph begin
    V = 3
    vlabel = [:s, :s, :s]
end

tripcone = Cone(tripconed, :s3, [1=>:Π₁, 2=>:Π₂, 3=>:Π₃])

semicones = [paircone, tripcone]
semieqs = [
    (:p1p2_p1, [p1p2, :π₁], [:Π₁]),
    (:p1p2_p2, [p1p2, :π₂], [:Π₂]),
    (:p2p3_p1, [p2p3, :π₁], [:Π₂]),
    (:p2p3_p2, [p2p3, :π₂], [:Π₃]),

    (:kid_p1, [kid, :π₁], [p1p2,:k]),
    (:kid_p2, [kid, :π₂], [:Π₃]),

    (:idk_p2, [idk, :π₂], [p2p3,:k]),
    (:idk_p1, [idk, :π₁], [:Π₁]),

    (:assoc, [idk, :k], [kid,:k]),
]
semig = Sketch(:semig, semigschema, semigcones, semigeqs);

include(joinpath(@__DIR__, "../../src/Sketch.jl"))

fxb = Symbol("f×ᵦg")

eqschema = @acset LabeledGraph begin
    V = 3
    E = 4
    vlabel = [:A,:B,fxb]
    elabel = [:f,:g, :π1, :π2]
    src = [1,1,3,3]
    tgt = [2,2,1,1]
end

eqconed = @acset LabeledGraph begin
    V = 3
    E = 2
    vlabel = [:A,:A,:B]
    elabel = [:f,:g]
    src = [1,2]
    tgt = [3,3]
end


eqsketch = Sketch(:equalizer, eqschema, [
    Cone(eqconed, fxb, [1=>:π1,2=>:π2])], Cone[], []);

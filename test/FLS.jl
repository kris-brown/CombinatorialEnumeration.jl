using Test
include(joinpath(@__DIR__, "../src/FLS.jl"))

fgschema = @acset LabeledGraph_{Symbol} begin
  V = 3
  vlabel=[:A, :B, :C]
  E = 3
  elabel=[:f, :g, :c]
  src = [1,2,3]
  tgt = [2,1,1]
end

ccone = @acset  LabeledGraph_{Symbol} begin
    V = 3
    vlabel = [:A,:A,:B]
    E = 2
    elabel = [:f, :f]
    src = [1,2]
    tgt = [3,3]
end
cone = Cone(ccone, :C, [1=>:c,2=>:c])
fls = FLS(:fg, fgschema,[cone], [[:f, :g] => []])
f2 = fls_from_json(to_json(fls))
@test fls_from_json(to_json(fls)) == fls

xmod,xrel = [f(:fg, fgschema) for f in [grph_to_cset, grph_to_crel]]
[add_part!(xmod, x) for x in [:A,:B,:C]]
[set_subpart!(xmod, 1, x, 1) for x in [:f, :g, :c]]

xmodrel = initrel(fls, xmod)
@test crel_to_cset(fls, xmodrel) == xmod


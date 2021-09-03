using Test
include(joinpath(@__DIR__, "../src/FLS.jl"))
include(joinpath(@__DIR__, "../data/sketches/fg.jl"))

f2 = fls_from_json(to_json(fls))
@test fls_from_json(to_json(fls)) == fls

xmod,xrel = fls.cset(), fls.crel()
[add_part!(xmod, x) for x in [:A,:B,:C]]
[set_subpart!(xmod, 1, x, 1) for x in [:f, :g, :c]]

xmodrel = initrel(fls, xmod)
@test crel_to_cset(fls, xmodrel) == xmod

@test isempty(ChaseStepData())


using Test
include(joinpath(@__DIR__, "../src/Sketch.jl"))
include(joinpath(@__DIR__, "../data/sketches/fg.jl"))

f2 = sketch_from_json(to_json(fg))
@test sketch_from_json(to_json(fg)) == fg

xmod,xrel = fg.cset(), fg.crel()
# Create terminal model for fg
[add_part!(xmod, x) for x in [:A,:B]]
[set_subpart!(xmod, 1, x, 1) for x in [:f, :g, :inv]]

xmodrel = initrel(fg, xmod)
@test crel_to_cset(fg, xmodrel) == (xmod => false)



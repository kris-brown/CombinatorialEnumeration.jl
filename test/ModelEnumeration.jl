using Test
include(joinpath(@__DIR__, "../src/ModelEnumeration.jl"))

# Example from earlier
if 1+1==1
  include(joinpath(@__DIR__, "../data/sketches/fg.jl"))

  # chase a complete model, should give one model
  Ks, Ms = chasestep(fls, xmodrel)
  @test isempty(Ks)
  @test only(values(Ms)) == xmodrel


  db = init_db("test.db"; rem=true)
  add_model(db, fls, xmodrel) # adds one premodel and one model
  Kids, Mids = chasestep_db(db, fls, 1)
  @test isempty(Kids)
  @test Mids == [1]

  chase_below(db, fls, 1)
end



# I = grph_to_cset(:cat, catschema);
# add_part!(I, :A);
# add_part!(I, :O; refl=1);
# J = initrel(catfls, I);
# Ks = apply_tgds(catfls, J);
# K = Ks[1] # 3^3 models, first one is free
# e = apply_cones!(catfls, K)
# apply_egds!(catfls, K, e)
# Ks, Ms = chasestep(catfls, J)

include(joinpath(@__DIR__, "../data/sketches/cat.jl"))

# Chase below explicitly  # chase_below(db, catfls, 1)
F,n,nmax, db = catfls, 1, 11, init_db("test.db"; rem=false)
unchased, res, nmax  = Set{Int}(), Set{Int}(), nmax===nothing ? n + 10 : n
m = length(realobs(F))

chase_below(db, catfls, 1)


# for combo in combos_below(m, n)
#   println("COMBO $(Dict(zip(realobs(F),combo)))")
#   push!(unchased, init_premodel(db, F, combo))
# end
# seen = get_seen(db, F)

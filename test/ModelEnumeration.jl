using Test
include(joinpath(@__DIR__, "../src/ModelEnumeration.jl"))
include(joinpath(@__DIR__, "../data/sketches/cat.jl"))

F = catfls;

# Chase below explicitly  # chase_below(db, catfls, 1)
db = init_db(reset=false);

# There is one empty model
@test length(chase_below(db, catfls, 0)) == 1

# There is no model with only one O+A, since each O needs an identity A.
@test length(chase_below(db, catfls, 1)) == 1

# There are two models of size at most 2. The empty model, and the model with
# one (id) arrow and one object.
ms_2 = chase_below(db, catfls, 2)
@test length(ms_2) == 2
ms_2_again = chase_below(db, catfls, 2) # now results are already in DB
@test ms_2 == ms_2_again

# category with one object = monoid. There are two addn'l monoids with 2 arrows.
ms_3 = chase_below(db, catfls, 3)
@test length(ms_3) == 4





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

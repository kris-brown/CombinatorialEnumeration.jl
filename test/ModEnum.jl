module TestModEnum

# using Revise
using Test
using ModelEnumeration
using CSetAutomorphisms

using ModelEnumeration.ModEnum: combos_below, chase_db_step!

include(joinpath(@__DIR__, "TestSketch.jl"));


@test length(combos_below(2, 3)) == 10

# model enumeration where |A| = |B| = 1
I = @acset S.cset begin A=1;B=1;I=1;a=1 end
es = init_db(S,I, [:A,:B])
@test length(es) == 1
test_models(es, S, [@acset(S.cset, begin A=1;B=1;C=1;E=1;I=1;
                                         f=1;g=1;c=1;e=1;a=1;b=1 end)])

# model enumeration where |A| = 1, |B| = 2
I = @acset S.cset begin A=1;B=2;I=1;a=1 end;
es = init_db(S,I, [:A,:B]);
@test nparts(es[1].model,:b) == 0
chase_db(S,es);
expected = [
  # the f&g can point to the same element
  @acset(S.cset, begin A=1;B=2;E=1;C=2;I=1;f=1;g=1;c=[1,2];a=1;b=1;e=1 end),
  # or they can point to different elements
  @acset(S.cset, begin A=1;B=2;C=1;I=1;f=1;g=2;c=1;a=1;b=1 end)
]
test_models(es, S, expected)

# model enumeration where |A| = 2, |B| = 1
I = @acset S.cset begin A=2;B=1 end;
es = init_db(S,I,[:A,:B]);
@test nparts(es[1].model, :E) == 2
chase_db(S,es);
test_models(es, S, [@acset(S.cset, begin A=2;B=1;C=1;E=2;I=1; # both A equalized
                                         f=1;g=1;c=1;e=[1,2];a=1;b=1 end)])
# model enumeration where |A| = 2, |B| = 2
I = @acset S.cset begin A=2;B=2 end;
es = init_db(S,I, [:A,:B]);
chase_db(S,es)
expected = [
  # f&g are both id
  @acset(S.cset, begin A=2;B=2;E=2;C=2;I=1;
                       f=[1,2];g=[1,2];c=[1,2];a=1;b=1;e=[1,2] end),
  # f&g are both const, picking out diff B elems
  @acset(S.cset, begin A=2;B=2;C=1;I=1;f=1;g=2;c=1;a=1;b=1 end),
  # f&g are not const and different for both A's
  @acset(S.cset, begin A=2;B=2;C=1;I=1;f=[2,1];g=[1,2];c=1;a=1;b=2 end),
  # f&g both const and point to same element
  @acset(S.cset, begin A=2;B=2;E=2;C=2;I=1;f=1;g=1;c=[1,2];e=[1,2];a=1;b=1 end),
  # f is const, g differs for the A's, so one of the A's is equalized.
  # "a" points to the element that is equalized.
  @acset(S.cset, begin A=2;B=2;E=1;C=1;I=1;f=1;g=[1,2];c=1;a=1;b=1;e=1 end), # 2
  # f is const, g differs for the A's, so one of the A's is equalized.
  # "a" points to the element that is not equalized.
  @acset(S.cset, begin A=2;B=2;E=1;C=1;I=1;f=1;g=[2,1];c=1;a=1;b=1;e=2 end), # 5
  # g is const, f differs for the A's, so one of the A's is equalized.
  # "a" points to the element that is equalized.
  @acset(S.cset, begin A=2;B=2;E=1;C=1;I=1;f=[1,2];g=1;c=1;a=1;b=1;e=1 end), # 5
  # g is const, f differs for the A's, so one of the A's is equalized.
  # "a" points to the element that is not equalized.
  @acset(S.cset, begin A=2;B=2;E=1;C=1;I=1;f=[2,1];g=1;c=1;a=1;b=2;e=2 end), # 5
]
test_models(es, S, expected)

end # module

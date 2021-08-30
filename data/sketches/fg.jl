include(joinpath(@__DIR__, "../../src/FLS.jl"))

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
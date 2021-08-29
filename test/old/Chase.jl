include("/Users/ksb/Catlab.jl/src/atp/Chase.jl")

sch = Schema(Dict(:R=>2, :A=>1))
_, Isch = schema_to_csettype(sch)
I = Isch()
add_parts!(I, :V, 2, id_V=[101,202], sort=[:X, :X])
add_parts!(I, :R, 2, R_1=[1,2], R_2=[2,2], id_R=[1001,2002])
I2 = deepcopy(I)
add_parts!(I2, :V, 1, id_V=[303], sort=[:X])
add_parts!(I2, :A, 2, A_1=[2,3], id_A=[1000,2000])
I3 = deepcopy(I2)
add_parts!(I2, :R, 1, R_1=[2], R_2=[3], id_R=[3003]) # x2, y relation
add_parts!(I3, :R, 1, R_1=[1], R_2=[3], id_R=[3003]) # x1, y relation

t1 = @acset Isch begin
  V = 2
  R = 1
  R_1 = [1]
  R_2 = [2]
  sort = [:X,:X]
  id_V = [11, 22]
  id_R = [241]
end

t2 = @acset Isch begin
  V = 3
  R = 1
  A = 2
  R_1 = [1]
  R_2 = [3]
  A_1 = [3, 2]
  sort = [:X,:X,:X]
  id_V = [11,22,33]
  id_R = [799]
  id_A = [900, 901]
end

tgd3 = Dep(:d1, t1, t2)
egd3 = Dep(:d2, t1, Isch(), Set([Set([11,22])]))
te = Dep(:d3, t1, t2, Set([Set([11,22])]))

ch, _ = core_chase(I, Set([tgd3]))

redun = @acset Isch begin
  V = 2
  A = 2
  sort = [:X,:X]
  id_V = [11, 22]
  A_1 = [1,1]
  id_A = [1, 2]
end
rcore = findcore(redun)


xnyymx = trim(@program(C, (x::X,n::X,m::X),
              let nx = mul(n,x); (nx,[mul(nx,m),x]) end), 1,1)
s = [:e_intro, :sym, :mul_assoc, :cancel, :pos, :leftid]
h, newres, r, r2 = prove(T_pcs_mon, xnyymx, passx; strat=seq([[ss] for ss in s]), maxi=length(s))

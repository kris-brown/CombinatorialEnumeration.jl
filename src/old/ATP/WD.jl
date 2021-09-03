include("/Users/ksb/Catlab.jl/src/atp/ATP.jl")
using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra
using Catlab.Theories
using Catlab.Programs
using Catlab.Present

"""
Co-diagonals only are created when they are used in an output, so sometimes we
must create 'fake' outputs and then trim them away (replacing with a junction).
We keep the first `O` outputs and `I` inputs, defaulting to keeping all inputs
and no outputs.
"""
function trim(p::WiringDiagram{BiproductCategory, Any, Any, Any}, O::Int=0,
              I::Int=-1)
  pd = p.diagram
  I = I < 0 ? nparts(pd, :OuterInPort) : I # default to keeping all inputs
  N_O = nparts(pd, :OuterOutPort)
  rem_ows, rem_pws = Int[], Int[]
  for oop in O+1:N_O
    typ = pd[:outer_out_port_type][oop]
    b = add_part!(pd, :Box, value=typ, box_type=Junction{nothing, Symbol})
    for pw in incident(pd, oop, :pass_tgt)
      ip = add_part!(pd, :InPort, in_port_box=b, in_port_type=typ)
      add_part!(pd, :InWire, in_src=pd[:pass_src][pw], in_tgt=ip,
                in_wire_value=nothing)
      push!(rem_pws, pw)
    end
    for ow in incident(pd, oop, :out_tgt)
      ip = add_part!(pd, :InPort, in_port_box=b, in_port_type=typ)
      add_part!(pd, :Wire, src=pd[:out_src][ow], tgt=ip, wire_value=nothing)
      push!(rem_ows, ow)
    end
  end
  rem_parts!(pd, :OutWire, sort(rem_ows))
  rem_parts!(pd, :PassWire, sort(rem_pws))
  rem_parts!(pd, :OuterOutPort, O+1:N_O)
  # Repeat, swapping in for out
  N_I = nparts(pd, :OuterInPort)
  rem_iws, rem_pws = Int[], Int[]
  for oip in I+1:N_I
    typ = pd[:outer_in_port_type][oip]
    b = add_part!(pd, :Box, value=typ, box_type=Junction{nothing, Symbol})
    for pw in incident(pd, oip, :pass_src)
      op = add_part!(pd, :OutPort, out_port_box=b, out_port_type=typ)
      add_part!(pd, :OutWire, out_tgt=pd[:pass_src][pw], out_src=op,
                out_wire_value=nothing)
      push!(rem_pws, pw)
    end
    for iw in incident(pd, oip, :in_src)
      op = add_part!(pd, :OutPort, out_port_box=b, out_port_type=typ)
      add_part!(pd, :Wire, tgt=pd[:in_tgt][iw], src=op, wire_value=nothing)
      push!(rem_iws, iw)
    end
  end
  rem_parts!(pd, :InWire, sort(rem_iws))
  rem_parts!(pd, :PassWire, sort(rem_pws))
  rem_parts!(pd, :OuterInPort, I+1:N_I)
  return p
end

# Single sorted inputs/outputs
Zero, One, Two, Three, Four, Five, Six = [repeat([:X], i) for i in 0:6]

# Boxes
mmul = Box(:mul, Two,   One);
e  = Box(:e,   Zero,  One);
inv  = Box(:inv, One,   One);
gens = Box(:s_,   Zero,  One);
genr = Box(:r_,   Zero,  One);
R  = Box(:R,   One,   One);
f  = Box(:f,   One,   One);
g  = Box(:g,   One,   One);
s  = Box(:s,   [:A],  [:O]);
t  = Box(:t,   [:A],  [:O]);
Id   = Box(:Id,  [:O],  [:A]);
cmp  = Box(:cmp, [:A,:A], [:A]);

o_o  = Box(:o_o, [:O,:O], [:O]); # ⊗ₒ
o_a  = Box(:o_a, [:A,:A], [:A]); # ⊗ₐ

ounit= Box(:⊤, Symbol[], [:O])
σ  = Box(:σ,  [:O, :O], [:A])
del  = Box(:δ,  [:O],   [:A])
eps  = Box(:ϵ,  [:O],   [:A])
mu   = Box(:μ,  [:O],   [:A])
ev   = Box(:ev,   [:O, :O], [:A])
Exp   = Box(:exp, [:O, :O], [:O])

lam   = Box(:lam, [:O, :O, :O, :A], [:A])

ϵ(x::Symbol=:X)   = Junction(x, 1, 0)
η(x::Symbol=:X)   = Junction(x, 0, 1)
δ(x::Symbol=:X)   = Junction(x, 1, 2)
μ(x::Symbol=:X)   = Junction(x, 2, 1)
dot(x::Symbol=:X) = Junction(x, 1, 1)
cap(x::Symbol=:X) = Junction(x, 2, 0)
δ_2(x::Symbol=:X)   = Junction(x, 2, 2)

# Generator sets
Σ0     = Set{Box{Symbol}}()
Σ_monoid   = Set([mmul, e]);
Σ_group  = Set([inv]);
Σ_dihedral = Set([gens, genr]);
Σ_rel    = Set([R, f, g]);
Σ_reflG  = Set([s, t, Id]);
Σ_cat    = Set([cmp]);
Σ_mc     = Set([o_o, o_a, ounit])
Σ_smc    = Set([σ])
Σ_crc    = Set([del, eps])
Σ_dcr    = Set([mu])
Σ_ccc    = Set([ev, Exp, lam])


@present C(FreeBiproductCategory) begin
  X::Ob
  A::Ob
  O::Ob
  mul::Hom(otimes(X, X), X)
  e::Hom(munit(), X)
  inv::Hom(X,X)
  s_::Hom(munit(), X)
  r_::Hom(munit(), X)
  R::Hom(X, X)
  f::Hom(X,X)
  g::Hom(X,X)
  s::Hom(A,O)
  t::Hom(A,O)
  Id::Hom(O,A)
  cmp::Hom(otimes(A, A),A)
  o_o::Hom(otimes(O, O), O)
  o_a::Hom(otimes(A, A), A)

  ⊤::Hom(munit(), O)
  σ::Hom(otimes(O,O), A)
  δ::Hom(O,A)
  ϵ::Hom(O,A)
  μ::Hom(O,A)
  ev::Hom(otimes(O,O), A)
  exp::Hom(otimes(O,O), O)
  lam::Hom(otimes(O, O, O, A), A)
end

X, O, A = (generator(C, name) for name in [:X,:O,:A])
mul_,e_,lam_ = (generator(C, name) for name in [:mul, :e, :lam])

passx = @program C (x::X) -> x
passo = @program C (x::O) -> x
passa = @program C (x::A) -> x

epass =  trim(@program(C, (x::X,y::X), (x, [y,e()])), 1)

e11 = @program C (x::X) (e(),x)
ll = @program(C, (x::X), let y=e(); (y, mul(y, x)) end)
leftid = Eq(:leftid, ll, e11, false);

rr = @program(C, (x::X), let y=e(); (y, mul(x, y)) end)
rightid = Eq(:rightid, rr, e11, false);

ma1 = @program C (x::X,y::X,z::X) -> mul(x, mul(y, z))
ma2 = @program C (x::X,y::X,z::X) -> mul(mul(x, y), z)
mul_assoc = Eq(:mul_assoc, ma1, ma2);

ma1 = @program C (x::A,y::A,z::A) -> cmp(x, cmp(y, z))
ma2 = @program C (x::A,y::A,z::A) -> cmp(cmp(x, y), z)
cmp_assoc = Eq(:cmp_assoc, ma1, ma2);

ma1 = @program C (x::O,y::O,z::O) -> o_o(x, o_o(y, z))
ma2 = @program C (x::O,y::O,z::O) -> o_o(o_o(x, y), z)
o_o_assoc = Eq(:o_o_assoc, ma1, ma2);

ma1 = @program C (x::A,y::A,z::A) -> o_a(x, o_a(y, z))
ma2 = @program C (x::A,y::A,z::A) -> o_a(o_a(x, y), z)
o_a_assoc = Eq(:o_a_assoc, ma1, ma2);

e2x = trim(@program(C, (x::X), let y=e(); (y, y, x) end), 2)
rightinv = Eq(:rightinv, @program(C, (x::X), (e(),mul(x, inv(x)))), e2x, false);
leftinv  = Eq(:leftinv,  @program(C, (x::X), (e(),mul(inv(x),x))), e2x, false);
if 1+1==2
posl = trim(@program(C, (x::X,y::X), [mul(x,y), e()]))
posr = trim(@program(C, (x::X,y::X), [x, e(), y]))
pos = Eq(:pos,  posl, posr, false)

cancell = trim(@program(C, (x::X,y::X), (e(), [mul(x,y), y])), 1)
cancelr = @program(C, (x::X,y::X), [x, e()])
cancel = Eq(:cancel, cancell, cancelr, false)

sym = Eq(:sym, @program(C, (x::X,y::X) -> mul(x,y)),
               @program(C, (x::X,y::X) -> mul(y,x)))

uniq_inv_1 = trim(@program(C,(a::X,b::X,c::X),[mul(a, b),mul(b, c),e()]))
uniq_inv_2 = trim(@program(C,(a::X,b::X,c::X),[a,c]))
uniq_inv   = Eq(:uniq_inv,   uniq_inv_1,   uniq_inv_2);


div_1 =  @program C (a::X,b::X,c::X) [mul(a,b),c]
div_2 =  @program C (a::X,b::X,c::X) [mul(inv(a),c),b]
gdiv     = Eq(:gdiv,     div_1,    div_2);

leftcancel_1 = @program C (a::X,b::X,c::X) [mul(a, b), mul(a, c)]
leftcancel_2 = @program C (a::X,b::X,c::X) [b, c]
leftcancel   = Eq(:leftcancel, leftcancel_1, leftcancel_2);

e_wd = @program C () e()

ss = @program C () let x=s_(); mul(x,x) end
s_order_2 = Eq(:s_ord_2, ss, e_wd);

rrr = @program C () let x=r_(); mul(x,mul(x,x)) end
r_order_3 = Eq(:r_ord_3,  rrr, e_wd);


srs = @program C () let x=r_(), y=s_(); mul(mul(y, x), inv(y)) end
rinv = @program C () inv(r_())
sr2 =  @program C () let x=mul(s_(), r_()); mul(x,x) end

R_copy = @program C (i::X) let x=R(i); (x,x) end
fig26 =  @program C (i::X) let x=g(f(i)); (x,x) end

refl_s = @program C (a::O) s(Id(a))
refls = Eq(:refls, refl_s, passo);

refl_t = @program C (a::O) t(Id(a))
reflt = Eq(:reflt, refl_t, passo);

cmp_1 = trim(@program(C,(ff::A,gg::A),(s(ff),[t(ff),s(gg)],t(gg))))

cmp_2 = trim(@program(C,(ff::A,gg::A),begin
  cm = cmp(ff,gg)
  ([s(cm),s(ff)],[t(gg),t(cm)])
  end ))
cmp_intro = Eq(:cmp, cmp_1, cmp_2, false);

id_s = @program C (a::A) cmp(Id(s(a)),a)
l_unit = Eq(:l_unit, id_s, passa);

id_t = @program C (a::A) cmp(a,Id(t(a)))
r_unit = Eq(:r_unit, id_t, passa);

o_func_sl = @program C (a::A, b::A) s(o_a(a,b))
o_func_sr = @program C (a::A, b::A) o_o(t(a),t(b))
o_func_s = Eq(:o_func_s,o_func_sl,o_func_sr)

o_func_tl = @program C (a::A, b::A) t(o_a(a,b))
o_func_tr = @program C (a::A, b::A) o_o(t(a),t(b))
o_func_t = Eq(:o_func_t,o_func_tl,o_func_tr)

o_f_c_1 =  @program C (a::A,b::A,c::A,d::A) cmp(o_a(a,b),o_a(c,d))
o_f_c_2 =  @program C (a::A,b::A,c::A,d::A) o_a(cmp(a,c),cmp(b,d))
o_func_cmp = Eq(:o_func_cmp, o_f_c_1,    o_f_c_2);

lunit_o_a_ = @program C (a::A) o_a(Id(⊤()), a)
lunit_o_a  = Eq(:lunit_o_a,  lunit_o_a_,   passa);

runit_o_a_ = @program C (a::A) o_a(a, Id(⊤()))
runit_o_a  = Eq(:runit_o_a,  runit_o_a_,   passa);

lunit_o_o_ = @program C (a::O) o_o(⊤(), a)
lunit_o_o  = Eq(:lunit_o_o,  lunit_o_o_,   passo);

runit_o_o_ = @program C (a::O) o_o(a, ⊤())
runit_o_o  = Eq(:runit_o_o,  runit_o_o_,   passo);

bb_1 = @program C (a::O,b::O) cmp(σ(a,b),σ(b,a))
bb_2 = @program C (a::O,b::O) Id(o_o(a,b))
braidbraid = Eq(:braidbraid, bb_1,     bb_2);

braid_tl = @program C (a::O,b::O) t(σ(a,b))
braid_tr = @program C (a::O,b::O) o_o(b,a)
braid_t = Eq(:braid_t, braid_tl, braid_tr)

braid_sl = @program C (a::O,b::O) s(σ(a,b))
braid_sr = @program C (a::O,b::O) o_o(a,b)
braid_s = Eq(:braid_s, braid_sl, braid_sr)

braid_ots_t = @program C (a::A,b::A) cmp(o_a(a,b), σ(t(a),t(b)))
braid_ots_s = @program C (a::A,b::A) cmp(σ(s(a),s(b)),o_a(b,a))
braid_ots = Eq(:braid_ots, braid_ots_t, braid_ots_s);

eps_s_l = @program C (a::O) s(ϵ(a))
eps_s   = Eq(:eps_s, eps_s_l, passo)

del_s_l =@program C (a::O) s(δ(a))
del_s   = Eq(:del_s, del_s_l, passo)

e_t = @program C (a::O) t(ϵ(a))
eps_t_2 = @program C (_::O) ⊤()
eps_t   = Eq(:eps_o,   e_t, eps_t_2);

d_t = @program C (a::O) t(δ(a))
del_t_2 = @program C (a::O) o_o(a,a)
del_t   = Eq(:del_t,   d_t, del_t_2);

eps_coh_1 = @program C (a::O,b::O) ϵ(o_o(a,b))
eps_coh_2 = @program C (a::O,b::O) o_a(ϵ(a),ϵ(b))
eps_coh = Eq(:eps_coh, eps_coh_1, eps_coh_2);

del_coh_1 = @program C (a::O,b::O) δ(o_o(a,b))
del_coh_2 = @program C (a::O,b::O) [o_a(δ(a),δ(b)),o_a(o_a(Id(a),σ(a,b)),Id(b))]
del_coh = Eq(:del_coh, del_coh_1, del_coh_2);

del_nat_1 = @program C (a::O) cmp(δ(a),σ(a,a))
del_nat_2 =@program C (a::O) δ(a)
del_nat = Eq(:del_nat, del_nat_1, del_nat_2);

cc1_tt = @program C (a::O) let x=δ(a); cmp(x,o_a(x,Id(a))) end
cc1_ft = @program C (a::O) let x=δ(a); cmp(x,o_a(Id(a),x)) end
cc1   = Eq(:cc1, cc1_tt, cc1_ft);

cc1_tf = @program C (a::O) cmp(δ(a),o_a(ϵ(a),Id(a)))
cc1_ff = @program C (a::O) cmp(δ(a),o_a(Id(a),ϵ(a)))
cc2   = Eq(:cc2, cc1_tf, cc1_ff);

cc3_1 = @program C (a::A) cmp(δ(s(a)), o_a(a,a))
cc3_2 = @program C (a::A) cmp(a, δ(t(a)))
cc3   = Eq(:cc3, cc3_1, cc3_2);

delmu_t = @program C (a::O) cmp(δ(a), μ(a))
idbox = @program C (a::O) Id(a)
bone  = Eq(:bone, delmu_t, idbox)

proj1   = Eq(:mu_s, @program(C,(a::O),s(μ(a))), passo)
proj2   = Eq(:mu_t, @program(C,(a::O),t(μ(a))), passo)

frobr = @program C (a::O) cmp(μ(a),δ(a))
frobll = @program C (a::O) let x=Id(a); cmp(o_a(x,δ(a)),o_a(μ(a),x)) end
frob1   = Eq(:frob_l, frobll, frobr)

frobrl = @program C (a::O) let x=Id(a); cmp(o_a(δ(a),x),o_a(x,μ(a))) end
frob2   = Eq(:frob_r, frobrl, frobr)

epsnat1 = @program C (a::A) cmp(a,ϵ(t(a)))
epsnat2 = @program C (a::A) ϵ(s(a))
eps_nat = Eq(:epsnat, epsnat1, epsnat2)

ev_s = @program C (a::O,b::O) s(ev(a,b))
evs2 = @program C (a::O,b::O) o_o(exp(a,b),a)
evs   = Eq(:evs, ev_s, evs2)

ev_t = @program C (a::O,b::O) t(ev(a,b))
evt2 = @program C (_::O,b::O) (b,)
evt   = Eq(:evt, ev_t, evt2)

lam_intro1 = trim(@program C (x::O,y::O,z::O,q::O) ([o_o(x,y),s(q)],[z,t(q)]))
lam_intro2 = trim(@program C (x::O,y::O,z::O,q::O) lam(x,y,z,q))
λ_intro = Eq(:λ_intro, lam_intro1,  lam_intro2, false)


lam_s_ =  @program C (a::O,b::O,c::O,d::A) s(lam(a,b,c,d))
lam_s2 = @program C (x::O,_::O,_::O,_::A) (x,)
lam_s   = Eq(:lam_s,   lam_s_,  lam_s2)

lam_t_ =  @program C (a::O,b::O,c::O,d::A) t(lam(a,b,c,d))
lam_t2 = @program C (_::O,x::O,y::O,_::A) exp(x,y)
lam_t   = Eq(:lam_t,   lam_t_, lam_t2)

lam_eqf1 = @program C (a::O,b::O,c::O,d::A) cmp(o_a(lam(a,b,c,d),Id(b)),ev(b,c))
lam_eqf2 = trim(@program(C, (a::O,b::O,c::O,d::A), (d, [o_o(a,b),s(d)],[c,t(d)])), 1)
lam_eqf = Eq(:lam_eqf, lam_eqf1,    lam_eqf2)

lam_eqg1 = trim(@program(C, (a::O,b::O,c::O,d::A), (d, [a,s(d)], [exp(b,c),t(d)])), 1)
lam_eqg2 =  @program C (a::O,b::O,c::O,d::A) lam(a,b,c,cmp(o_a(d, Id(b)), ev(b,c)))
lam_eqg = Eq(:lam_eqg, lam_eqg1,    lam_eqg2)

# Equation sets
I_monoid = Set([mul_assoc, leftid, rightid]);

I_group  = Set([leftinv, rightinv]);
I_d3h  = Set([s_order_2, r_order_3]);
I_reflG  = Set([refls, reflt])
I_cat  = Set([cmp_assoc, l_unit, r_unit])
I_mc   = Set([o_o_assoc, o_a_assoc, o_func_s, o_func_t, o_func_cmp,
        lunit_o_a, runit_o_a, lunit_o_o, runit_o_o])
I_smc  = Set([braidbraid, braid_t, braid_s, braid_ots])
I_crc  = Set([eps_s, del_s, eps_t, del_t, eps_coh, del_coh, del_nat,
        cc1, cc2, cc3])
I_dcr  = Set([bone, proj1, proj2, frob1, frob2])
I_cc   = Set([eps_nat])
I_ccc  = Set([evs, evt, λ_intro, lam_s, lam_t, lam_eqf, lam_eqg])
I_pcs_mon = Set([mul_assoc, leftid, pos,cancel,sym])

# Theories
T_monoid = EqTheory(Σ_monoid, I_monoid);

T_pcs_mon = EqTheory(Σ_monoid, I_pcs_mon);
T_group  = union(T_monoid, Σ_group,  I_group);
T_d3h  = union(T_group,  Σ_dihedral, I_d3h);

T_reflG  = EqTheory(Σ_reflG, I_reflG);
T_cat  = union(T_reflG, Σ_cat, I_cat);
T_mc   = union(T_cat,   Σ_mc,  I_mc);
T_smc  = union(T_mc,  Σ_smc, I_smc);
T_crc  = union(T_smc,   Σ_crc, I_crc);
T_dcr  = union(T_crc,   Σ_dcr, I_dcr);
T_cc   = union(T_dcr,   Σ0,  I_cc)
T_ccc  = union(T_cc,  Σ_ccc, I_ccc)
end


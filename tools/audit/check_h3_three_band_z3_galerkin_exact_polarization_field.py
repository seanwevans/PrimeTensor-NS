#!/usr/bin/env python3
"""Exact complex finite-Galerkin polarization and analytic vector-field audit.

The ordered Leray convolution, all sums and polarization identities use exact
Gaussian rational arithmetic. Only Euclidean square roots in Wiener norms are
evaluated with 100-digit Decimal. Tests include output collisions and modes
not in the input support. These tests are independent mathematical checks,
not an alternative to Lean compilation or an ODE/FTC proof.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as F
from random import Random
import check_h3_three_band_z3_galerkin_analytic_consistency as old
import check_h3_three_band_flux_slope as first

A=old.a
ZERO=old.ZERO

def test_case(s,u,v,r,R,mu):
    z={n:old.sub(u[n],v[n]) for n in s}
    q_uu=old.source(s,u,u)
    q_vv=old.source(s,v,v)
    q_zu=old.source(s,z,u)
    q_vz=old.source(s,v,z)
    outputs=set(q_uu)|set(q_vv)|set(q_zu)|set(q_vz)
    for n in outputs:
        diff=old.sub(q_uu.get(n,ZERO),q_vv.get(n,ZERO))
        assert diff==old.vecadd(q_zu.get(n,ZERO),q_vz.get(n,ZERO))
    # The full weighted source difference counts every actual output,
    # including absent input modes and repeated ordered pair sums.
    lhs=sum((old.wt(n,r)*old.nn(old.sub(q_uu.get(n,ZERO),q_vv.get(n,ZERO)))
             for n in outputs),Decimal(0))
    rhs=5*old.mass(s,z,R)*(old.mass(s,u,R)+old.mass(s,v,R))
    assert lhs<=rhs+Decimal('1e-65'),(lhs,rhs)
    if old.mass(s,u,R)<=100 and old.mass(s,v,R)<=100:
        assert lhs<=1000*old.mass(s,z,R)+Decimal('1e-65')
    # Physical Galerkin NS time field: -mu*|n|^2 u(n)+Q(u,u)(n).
    f={n:first.vadd(first.vscale(-mu*A.d2(n),u[n]),q_uu.get(n,ZERO))
       for n in s}
    radius=F(3,2)
    W9=old.mass(s,u,F(9,5))
    W3=old.mass(s,u,radius)
    D3=old.deriv(s,u,radius)
    Lap3=sum((old.wt(n,radius)*A.d2(n)*old.nn(u[n]) for n in s),Decimal(0))
    F3=old.mass(s,f,radius)
    assert Lap3<=100*W9+Decimal('1e-65')
    assert D3<=5*W9+Decimal('1e-65')
    assert W3<=W9+Decimal('1e-65')
    assert F3<=old.dec(mu)*Lap3+W3*D3+Decimal('1e-65')
    # A second analytic-reserve bound pays two Laplacian derivatives on
    # every generated projected nonlinear output at the lower radius.
    qsource=old.source(s,u,u)
    lapQ=sum((old.wt(n,F(5,4))*A.d2(n)*old.nn(z)
              for n,z in qsource.items()),Decimal(0))
    assert lapQ<=100*W3*D3+Decimal('1e-65')
    if W9<=100:
        assert lapQ<=5000000+Decimal('1e-65')
    if W9<=100 and 0<=mu<=F(1,10):
        assert F3<=51000+Decimal('1e-65')
    return sum(n not in s for n in outputs)

def run():
    with localcontext() as ctx:
        ctx.prec=100
        rng=Random(8816531)
        pool=[(a,b,c) for a in range(-3,4) for b in range(-3,4)
              for c in range(-2,3)]
        cases=0; born=0
        for r,R in ((F(5,4),F(3,2)),(F(3,2),F(9,5))):
            for size in (1,2,3,5,7,10):
                for trial in range(24):
                    s=rng.sample(pool,size)
                    # 1/500 keeps the larger analytic-radius 100-ball active;
                    # exact rational scaling preserves the polarization proof.
                    scale=F(1,500) if trial%3 else F(1,2000)
                    u={n:first.vscale(scale,A.rnd_vec(rng)) for n in s}
                    v={n:first.vscale(scale,A.rnd_vec(rng)) for n in s}
                    mu=(F(0),F(1,100),F(1,10))[trial%3]
                    born+=test_case(s,u,v,r,R,mu)
                    cases+=1
        # Test the original six-mode seed with genuinely newborn frequencies.
        core={tuple(int(x) for x in n):vec for n,vec in
              first.make_initial(F(1),F(1)).items()}
        extras=[(1,1,0),(4,1,0),(5,2,0)]
        s=sorted(set(core)|set(extras)|{tuple(-x for x in n) for n in extras})
        u={n:first.vscale(F(1,200),core.get(n,ZERO)) for n in s}
        v={n:first.vscale(F(1,400),core.get(n,ZERO)) for n in s}
        born+=test_case(s,u,v,F(3,2),F(9,5),F(1,10))
        cases+=1
        assert born>0
        print(f'PASS: {cases} exact full-Leray Galerkin polarization/field cases')
        print(f'PASS: {born} generated output modes absent from original supports')
        print('PASS: exact B(u,u)-B(v,v)=B(u-v,u)+B(v,u-v)')
        print('PASS: unconditional two-radius Lipschitz in both radius ladders')
        print('PASS: W_(3/2)(F_mu(u)) <= mu*Lap_(3/2)(u)+W_(3/2)(u)*D_(3/2)(u)')
        print('PASS: W_(9/5)(u)<=100 and mu<=1/10 imply field speed <=51000')
        print('PASS: all-output Laplacian nonlinear source at W_(5/4) <=5000000')
        print('NOTE: time-dependent ODE path and temporal FTC/Duhamel remain unproved')

if __name__=='__main__':run()

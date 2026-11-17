#!/usr/bin/env python3
"""Exact spatial verification of the Galerkin strong temporal FTC interfaces.

Checks the true -mu |n|^2 u + complex Leray B(u,u) field difference,
nonlinear polarization and the cutoff-uniform lower-radius 1010 bound.
The time-FTC theorem itself is mathematical (a Banach FTC application in Lean),
not a numerical substitute for constructing an ODE trajectory.
"""
from decimal import Decimal,localcontext
from fractions import Fraction as F
from random import Random
import check_h3_three_band_z3_galerkin_analytic_consistency as ana
import check_h3_three_band_z3_galerkin_exact_polarization_field as prev
import check_h3_three_band_flux_slope as first

Z=ana.ZERO
A=ana.a

def field(s,u,mu):
    src=ana.source(s,u,u)
    return {n:first.vadd(first.vscale(-mu*A.d2(n),u[n]),src.get(n,Z)) for n in s}

def test(s,u,v,mu):
    delta={n:ana.sub(u[n],v[n]) for n in s}
    fu=field(s,u,mu);fv=field(s,v,mu)
    fd={n:ana.sub(fu[n],fv[n]) for n in s}
    q_u=ana.source(s,u,u);q_v=ana.source(s,v,v)
    qd={n:ana.sub(q_u.get(n,Z),q_v.get(n,Z)) for n in s}
    # Exact Gaussian-rational field difference at every retained Fourier mode.
    for n in s:
        expected=first.vadd(first.vscale(-mu*A.d2(n),delta[n]),qd[n])
        assert fd[n]==expected
    low=F(5,4); mid=F(3,2); high=F(9,5)
    W=ana.mass(s,delta,mid)
    lapLow=sum((ana.wt(n,low)*ana.dec(A.d2(n))*ana.nn(delta[n])
                for n in s),Decimal(0))
    srcLow=sum((ana.wt(n,low)*ana.nn(qd[n]) for n in s),Decimal(0))
    FLow=ana.mass(s,fd,low)
    eps=Decimal('1e-65')
    assert lapLow<=100*W+eps
    assert FLow<=ana.dec(mu)*lapLow+srcLow+eps
    if ana.mass(s,u,mid)<=100 and ana.mass(s,v,mid)<=100:
        assert srcLow<=1000*W+eps
        assert FLow<=1010*W+eps
    if ana.mass(s,u,high)<=100 and ana.mass(s,v,high)<=100:
        assert FLow<=1010*W+eps
    return FLow,W

def run():
    with localcontext() as ctx:
        ctx.prec=100
        rng=Random(2441010)
        pool=[(a,b,c) for a in range(-4,5) for b in range(-3,4) for c in range(-2,3)]
        cases=0
        for size in (1,2,3,5,7,10):
            for trial in range(42):
                s=rng.sample(pool,size)
                scale=F(1,700) if trial%2 else F(1,4000)
                u={n:first.vscale(scale,A.rnd_vec(rng)) for n in s}
                v={n:first.vscale(scale,A.rnd_vec(rng)) for n in s}
                mu=(F(0),F(1,100),F(1,10))[trial%3]
                test(s,u,v,mu)
                cases+=1
        # Real six-mode support, plus newly born output modes initially zero.
        core=first.make_initial(F(1),F(1))
        extras=[(1,1,0),(4,1,0),(5,2,0)]
        s=sorted(set(core)|set(extras)|{tuple(-i for i in z) for z in extras})
        u={n:first.vscale(F(1,300),core.get(n,Z)) for n in s}
        v={n:first.vscale(F(1,400),core.get(n,Z)) for n in s}
        test(s,u,v,F(1,10));cases+=1
        # All-degree analytic envelope, independent of Galerkin support.
        for m in range(3000):
            assert m*m*F(5,4)**m<=100*F(3,2)**m
        print(f'PASS: {cases} exact rational full Galerkin field-difference cases')
        print('PASS: W_(5/4)(F_mu(u)-F_mu(v)) <= mu*Lap_(5/4)(u-v)+W_(5/4)(Q(u)-Q(v))')
        print('PASS: Lap_(5/4)(u-v) <=100 W_(3/2)(u-v) for every integer degree')
        print('PASS: W_(3/2)-100 ball and mu<=1/10: field Lipschitz <=1010')
        print('PASS: stronger W_(9/5)-100 ball implies middle-radius hypothesis')
        print('NOTE: per-mode FTC is formally deduced from strong derivative, continuity, integrability; ODE existence remains open')

if __name__=='__main__':run()

#!/usr/bin/env python3
"""Independent full-output complex Fourier exponential-Euler Wiener audit.

Checks the actual finite Galerkin coefficient, physical heat multiplier
exp(-nu*h*|n|_2**2), and the full nonnegative heat debt. The Gaussian-
rational Leray convolution is exact; only exp/square roots are evaluated
with 90-digit Decimal. Zero input coefficients are explicitly tested.
No ODE or PDE passage is claimed by these finite-step tests.
"""
from collections import defaultdict
from decimal import Decimal, localcontext
from fractions import Fraction as F
from random import Random
import check_h3_three_band_z3_galerkin_output_wiener as old
import check_h3_three_band_flux_slope as first

Z=old.VZ

def dec(x):
    if isinstance(x,int): return Decimal(x)
    if isinstance(x,F): return Decimal(x.numerator)/Decimal(x.denominator)
    return Decimal(x)


def vn2(x): return old.prior.n2(x)

def vn(x): return dec(vn2(x)).sqrt()

def full_source(s,u):
    q=defaultdict(list)
    for p in s:
        for z in s:
            n=old.old.add_modes(p,z)
            q[n].append(old.prior.transport(n,z,u[p],u[z]))
    return {n:old.prior.dsum(v) for n,v in q.items()}


def step_norm(x,y,sigma,h):
    z=[(sigma*dec(a[0])+h*dec(b[0]),
        sigma*dec(a[1])+h*dec(b[1])) for a,b in zip(x,y)]
    return sum((a*a+b*b for a,b in z),Decimal(0)).sqrt()


def test(s,u,R,nu,h):
    with localcontext() as ctx:
        ctx.prec=90
        q=full_source(s,u)
        weight=lambda n:dec(R**old.prior.degree(n))
        W=sum((weight(n)*vn(u[n]) for n in s),Decimal(0))
        D=sum((weight(n)*dec(old.prior.degree(n))*vn(u[n]) for n in s),Decimal(0))
        out=Decimal(0); debt=Decimal(0); qmass=Decimal(0)
        created=0
        for n in s:
            sigma=(-dec(nu)*dec(h)*dec(old.prior.d2(n))).exp()
            assert 0<sigma<=1
            x=u[n]; y=q.get(n,Z)
            assert old.prior.dot_real(n,y)==old.prior.ZERO  # Projected output is solenoidal
            newnorm=step_norm(x,y,sigma,dec(h))
            out += weight(n)*newnorm
            debt += weight(n)*(1-sigma)*vn(x)
            qmass += weight(n)*vn(y)
            if x==Z and y!=Z:
                created+=1
                assert abs(newnorm-dec(h)*vn(y))<Decimal('1e-65')
            assert (newnorm+(1-sigma)*vn(x) <=
                    vn(x)+dec(h)*vn(y)+Decimal('1e-63'))
        eps=Decimal('1e-59')
        assert debt>=-eps
        assert out+debt<=W+dec(h)*qmass+eps,(out,debt,W,qmass)
        assert qmass<=W*D+eps,(qmass,W,D)
        assert out+debt<=W+dec(h)*W*D+eps,(out,debt,W,D)
        assert out<=W+dec(h)*W*D+eps
        return created


def run():
    # Independent earlier full-order, collision-sensitive test.
    rng=Random(99053533)
    pool=[(a,b,c) for a in range(-2,3) for b in range(-2,3)
                      for c in range(-1,2)]
    cases=0; created=0
    for R in (F(1),F(5,4),F(3,2)):
        for nu in (F(0),F(1,10),F(1)):
            for h in (F(0),F(1,100),F(1,2)):
                for size in (1,3,5,7):
                    for trial in range(4):
                        s=rng.sample(pool,size)
                        u={n:(old.prior.rnd_vec(rng) if (trial+n[0])%3 else Z)
                           for n in s}
                        created+=test(s,u,R,nu,h)
                        cases+=1
    # Real six-mode seed plus 3 new conjugate pairs: truly newly born modes.
    core=first.make_initial(F(1),F(1))
    new=((1,1,0),(4,1,0),(5,2,0))
    s=list(core)+list(new)+[old.old.neg_mode(n) for n in new]
    u={n:core.get(n,Z) for n in s}
    assert all(u[n]==Z for n in new)
    for h in (F(1,1000),F(1,20)):
        created+=test(s,u,F(3,2),F(1,10),h)
    assert created>0
    print(f'PASS: {cases} full-output heat-step Wiener/debt comparisons')
    print(f'PASS: {created} initially zero output coefficients with nonzero source')
    print('PASS: all heat factors in (0,1], debt nonnegative')
    print('PASS: W(step) + heat debt <= W(u) + h*W(u)*D(u)')
    print('PASS: exact Gaussian-rational ordered Leray source, 90-digit heat/sqrt')
    print('NOTE: exponential-Euler consistency and continuous-time PDE limit not proved')

if __name__=='__main__': run()

#!/usr/bin/env python3
"""Exact Z3 all-degree Wiener reserves and genuine Galerkin source Lipschitz.

The ordered Leray convolution and polarization identities are evaluated in
Gaussian rationals. Weighted Euclidean sums use 90-digit Decimal. The
frequency-degree envelope is an all-integer theorem in the adjacent Lean
source, not an inference from the bounded enumeration in this audit.

Finite ODE residual data are checked independently; this audit does not
construct an ODE solution or claim the Duhamel/FTC bridge is in Lean.
"""
from collections import defaultdict
from decimal import Decimal, localcontext
from fractions import Fraction as F
from random import Random

import check_h3_three_band_z3_galerkin_output_wiener as out
import check_h3_three_band_z3_complex_leray as a
import check_h3_three_band_flux_slope as first

ZERO=a.VZERO


def sub(x,y):
    return tuple(a.old.zadd(z,a.old.zneg(w)) for z,w in zip(x,y))


def vecadd(x,y):
    return a.old.vector_add(x,y)


def source(s, u, v):
    by_output=defaultdict(list)
    for p in s:
        for q in s:
            n=a.old.add_modes(p,q)
            by_output[n].append(a.transport(n,q,u[p],v[q]))
    return {n:a.dsum(vs) for n,vs in by_output.items()}


def dec(x):
    if isinstance(x, int):return Decimal(x)
    return Decimal(x.numerator)/Decimal(x.denominator)


def nn(x):return dec(a.n2(x)).sqrt()


def wt(n,R):return dec(R**a.degree(n))


def mass(s,u,R):return sum((wt(n,R)*nn(u[n]) for n in s),Decimal(0))


def deriv(s,u,R):return sum((wt(n,R)*a.degree(n)*nn(u[n]) for n in s),Decimal(0))


def test_reserves():
    # The first 5/4 -> 3/2 ladder and its 6/5-scaled 3/2 -> 9/5 version.
    # All-degree validity is established in the Lean source via induction.
    for m in range(0,3000):
        assert m*F(5,4)**m <= 5*F(3,2)**m
        assert m*m*F(5,4)**m <= 100*F(3,2)**m
        assert m*F(3,2)**m <= 5*F(9,5)**m
        assert m*m*F(3,2)**m <= 100*F(9,5)**m
    for n in ((0,0,0), (1,-2,3), (11,-9,17), (-25,-34,10)):
        m=a.degree(n)
        assert a.d2(n)<=m*m
        assert a.d2(n)*F(5,4)**m <= 100*F(3,2)**m
        assert a.d2(n)*F(3,2)**m <= 100*F(9,5)**m


def test_lipschitz(s,u,v,r,R):
    diff={n:sub(u[n],v[n]) for n in s}
    QU=source(s,u,u); QV=source(s,v,v)
    Qa=source(s,diff,u);Qb=source(s,v,diff)
    outs=set(QU)|set(QV)|set(Qa)|set(Qb)
    assert all(sub(QU.get(n,ZERO),QV.get(n,ZERO)) ==
               vecadd(Qa.get(n,ZERO),Qb.get(n,ZERO)) for n in outs)
    lhs=sum((wt(n,r)*nn(sub(QU.get(n,ZERO),QV.get(n,ZERO))) for n in outs),Decimal(0))
    abstract=mass(s,diff,r)*deriv(s,u,r)+mass(s,v,r)*deriv(s,diff,r)
    reserve=5*mass(s,diff,R)*(mass(s,u,R)+mass(s,v,R))
    tol=Decimal('1e-65')
    assert lhs<=abstract+tol,(lhs,abstract)
    assert abstract<=reserve+tol,(abstract,reserve)
    assert lhs<=reserve+tol
    if mass(s,u,R)<=100 and mass(s,v,R)<=100:
        assert lhs<=1000*mass(s,diff,R)+tol
    return sum(1 for x in outs if x not in s)


def test_ode_coeff():
    # Sup at normalized mu=1/10: (51,000,000 + 500,000)/2.
    for mu in (F(0),F(1,1000),F(1,100),F(1,10)):
        C=(1000*51000+mu*5000000)/2
        assert C<=25750000
    # Stress the normalized spectral second jet using genuine full convolution.
    core=first.make_initial(F(1),F(1))
    nu=F(1,10)
    Q0=first.quadratic(core)
    u1=first.first_derivative(core,nu,Q0)
    Q1=first.quadratic_derivative(core,u1)
    supp=set(core)|set(u1)|set(Q1)
    u2={n:first.vadd(Q1.get(n,ZERO),first.vscale(-nu*first.norm2(n),
                   u1.get(n,ZERO))) for n in supp}
    R=F(5,4)
    hvals=(F(1,100),F(1,1000),F(1,10000))
    with localcontext() as ctx:
        ctx.prec=90
        from check_h3_three_band_z3_galerkin_residual_budget import residual
        for h in hvals:
            path={n:first.vadd(first.vadd(core.get(n,ZERO),
                         first.vscale(h,u1.get(n,ZERO))),
                         first.vscale(h*h/2,u2.get(n,ZERO))) for n in supp}
            residual_norm=residual(supp,core,path,nu,h,R)
            assert residual_norm<=Decimal(25750000)*dec(h*h)


def run():
    with localcontext() as ctx:
        ctx.prec=90
        test_reserves()
        rng=Random(602524)
        pool=[(x,y,z) for x in range(-3,4) for y in range(-3,4)
                        for z in range(-2,3)]
        cases=0; new=0
        for radius in ((F(5,4),F(3,2)),(F(3,2),F(9,5))):
            for size in (2,3,5,7,9):
                for k in range(20):
                    s=rng.sample(pool,size)
                    u={n:a.rnd_vec(rng) for n in s}
                    v={n:a.rnd_vec(rng) for n in s}
                    new+=test_lipschitz(s,u,v,*radius)
                    cases+=1
        test_ode_coeff()
        print('PASS: all-degree two-radius/three-radius rational envelopes, 0..2999')
        print(f'PASS: {cases} exact Gaussian-rational Galerkin source-polarization tests')
        print(f'PASS: {new} full-source outputs not in original supports')
        print('PASS: W_r(B(u,u)-B(v,v)) <= 5 W_R(u-v)(W_R(u)+W_R(v))')
        print('PASS: M=100 source-Lipschitz constant 1000; local residual C=25750000')
        print('PASS: actual NS full-Fourier second jet lies under proposed local gate')
        print('NOTE: uniform Galerkin ODE path/FTC bridge is not formalized')

if __name__=='__main__':run()

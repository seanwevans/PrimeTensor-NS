#!/usr/bin/env python3
"""Independent spatial + finite-time sum audit for the full Z3 Galerkin field.

All Fourier convolutions, Laplacians, and perturbations use Gaussian-rational
arithmetic. Only complex Euclidean norms use 100-digit Decimal square roots.
The temporal test snapshots are linear *test* paths, not alleged exact ODE
solutions. The Lean theorem derives the temporal bound for genuine strong ODE
paths using FTC and the exact integral-finset interchange.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as F
from random import Random
import check_h3_three_band_z3_galerkin_strong_temporal_ftc as temporal
import check_h3_three_band_z3_galerkin_analytic_consistency as ana
import check_h3_three_band_flux_slope as first

A=ana.a
Z=ana.ZERO


def snapshot_case(s,u,mu,h):
    # v = u + h*F_mu(u), used solely as an algebraic time-pair test.
    Fu=temporal.field(s,u,mu)
    v={n:first.vadd(u[n],first.vscale(h,Fu[n])) for n in s}
    dv={n:ana.sub(v[n],u[n]) for n in s}
    tol=Decimal('1e-60')
    Rhi=F(9,5); Rmid=F(3,2); Rlo=F(5,4)
    WU=ana.mass(s,u,Rhi)
    WV=ana.mass(s,v,Rhi)
    assert WU<=100 and WV<=100,(WU,WV)
    rate=ana.mass(s,Fu,Rmid)
    inc=ana.mass(s,dv,Rmid)
    assert rate<=51000+tol
    assert abs(inc-ana.dec(h)*rate)<=tol,(inc,rate,h)
    assert inc<=51000*ana.dec(h)+tol
    Q0=ana.source(s,u,u); Qt=ana.source(s,v,v)
    qdiff={n:ana.sub(Qt.get(n,Z),Q0.get(n,Z)) for n in s}
    qcost=ana.mass(s,qdiff,Rlo)
    assert qcost<=1000*inc+tol,(qcost,inc)
    assert qcost<=51000000*ana.dec(h)+tol,(qcost,h)
    Ft=temporal.field(s,v,mu)
    fdiff={n:ana.sub(Ft[n],Fu[n]) for n in s}
    fcost=ana.mass(s,fdiff,Rlo)
    assert fcost<=1010*inc+tol
    assert fcost<=51510000*ana.dec(h)+tol
    # Finite-time Bochner integral interchange tested on rational weights
    # and discretized scalar norm data; it is exact up to Decimal rounding.
    sample=[ana.mass(s,temporal.field(s,
                  {n:first.vadd(u[n],first.vscale(F(k,8)*h,Fu[n])) for n in s},mu), Rmid)
            for k in range(9)]
    component=[sum((ana.wt(n,Rmid)*ana.nn(temporal.field(s,
                  {j:first.vadd(u[j],first.vscale(F(k,8)*h,Fu[j])) for j in s},mu)[n])
                 for k in range(9)),Decimal(0)) for n in s]
    # Equal-weight quadrature in t; ordering finite sums must not add |S|.
    lhs=sum(component,Decimal(0))/Decimal(9)
    rhs=sum(sample,Decimal(0))/Decimal(9)
    assert abs(lhs-rhs)<tol,(lhs,rhs)
    return qcost,fcost


def run():
    with localcontext() as ctx:
        ctx.prec=100
        rng=Random(17422251000)
        pool=[(a,b,c) for a in range(-3,4) for b in range(-3,4)
             for c in range(-2,3)]
        cases=0
        for size in (1,2,3,5,8):
            for trial in range(32):
                s=rng.sample(pool,size)
                scale=F(1,2500)
                u={n:first.vscale(scale,A.rnd_vec(rng)) for n in s}
                mu=(F(0),F(1,100),F(1,10))[trial%3]
                h=(F(1,1000),F(1,100),F(1,25))[trial%3]
                snapshot_case(s,u,mu,h)
                cases+=1
        core=first.make_initial(F(1),F(1))
        extra=[(1,1,0),(4,1,0),(5,2,0)]
        s=sorted(set(core)|set(extra)|{tuple(-x for x in n) for n in extra})
        for h in (F(1,1000),F(1,100)):
            u={n:first.vscale(F(1,500),core.get(n,Z)) for n in s}
            snapshot_case(s,u,F(1,10),h)
            cases+=1
        print(f'PASS: {cases} full-Leray time-pair snapshot tests')
        print('PASS: Fourier-weighted finite sum and 9-node time quadrature interchange')
        print('PASS: W_(3/2) increment <= 51000 h for source-field linear test paths')
        print('PASS: nonlinear source variation <= 51000000 h under W_(9/5) 100-ball')
        print('PASS: complete NS field variation <= 51510000 h under W_(9/5) 100-ball')
        print('NOTE: snapshots are NOT certified exact ODE trajectories; Lean FTC is conditional on actual strong derivatives')
        print('NOTE: Galerkin flow construction and preservation of the high-radius ball remain open')

if __name__=='__main__':run()

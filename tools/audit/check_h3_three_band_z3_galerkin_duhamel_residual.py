#!/usr/bin/env python3
"""Independent full-complex-Leray Galerkin Duhamel residual audit.

Finite ordered-pair collisions and newly generated modes use exact Gaussian
rational arithmetic; Bochner vectors and heat exponentials use 100-digit
Decimal. Simpson quadrature tests numerical instances of the integral
identity, NOT a proof of finite-dimensional ODE existence or Duhamel from FTC.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from random import Random

import check_h3_three_band_z3_galerkin_analytic_consistency as ana
import check_h3_three_band_z3_galerkin_residual_budget as residual
import check_h3_three_band_flux_slope as first

ZERO=ana.ZERO
RLO=Q(5,4)
RMID=Q(3,2)
RHI=Q(9,5)

def weight(n):
    return ana.wt(n,RLO)

def real(x):
    return ana.dec(x)

def vec(z):
    return residual.to_dec_vec(z)

def plus(x,y):
    return residual.plus_dec_vec(x,y)

def minus(x,y):
    return residual.minus_dec_vec(x,y)

def scale(x,z):
    return residual.scaled_dec_vec(x,z)

def norm(z):
    return residual.norm_dec(z)

def dd2(n):
    return real(ana.a.d2(n))

def interpolate(s,u,d,t):
    return {n:first.vadd(u[n],first.vscale(t,d[n])) for n in s}

def simpson(nodes,h):
    m=len(nodes)-1
    assert m%2==0
    return [h*Q((1 if j in (0,m) else (4 if j%2 else 2)),3*m) for j in range(m+1)]

def test_case(s,u,d,mu,h):
    tol=Decimal('1e-64')
    Q0=ana.source(s,u,u)
    base=ana.mass(s,u,RHI)
    assert base<=100
    out=set(Q0)
    step_count=24
    time_nodes=[h*Q(j,step_count) for j in range(step_count+1)]
    weights=simpson(time_nodes,h)
    int_heat={n:residual.zdec() for n in s}
    int_dev={n:residual.zdec() for n in s}
    norm_integral=Decimal(0)
    for t,w in zip(time_nodes,weights):
        ut=interpolate(s,u,d,t)
        assert ana.mass(s,ut,RHI)<=100
        inc={n:ana.sub(ut[n],u[n]) for n in s}
        delta=ana.mass(s,inc,RMID)
        assert delta<=51000*real(t)+tol
        Qt=ana.source(s,ut,ut)
        out.update(Qt)
        source_change=Decimal(0)
        lap=Decimal(0)
        lag=Decimal(0)
        for n in s:
            a=vec(Qt.get(n,ZERO))
            b=vec(Q0.get(n,ZERO))
            lam=dd2(n)
            heat=(-real(mu)*real(h-t)*lam).exp()
            assert Decimal(0)<heat<=1
            assert 1-heat<=real(mu)*real(h-t)*lam+tol
            diff=minus(a,b)
            g=minus(scale(heat,a),b)
            wa=weight(n)
            source_change+=wa*norm(diff)
            lap+=lam*wa*norm(b)
            lag+=wa*norm(g)
            assert norm(g)<=norm(diff)+(real(mu)*real(h-t)*lam)*norm(b)+tol
            int_heat[n]=plus(int_heat[n],scale(real(w)*heat,a))
            int_dev[n]=plus(int_dev[n],scale(real(w),g))
        assert source_change<=51000000*real(t)+tol
        assert lap<=5000000+tol
        assert lag<=source_change+real(mu)*real(h-t)*lap+tol
        assert lag<=51000000*real(t)+real(mu)*5000000*real(h-t)+tol
        norm_integral+=real(w)*lag
    # Define a Duhamel endpoint (not asserted to be the ODE's endpoint).
    # The heat-step residual should equal the integral of the source error.
    residual_mass=Decimal(0)
    for n in s:
        heat=(-real(mu)*real(h)*dd2(n)).exp()
        v=plus(scale(heat,vec(u[n])),int_heat[n])
        step=plus(scale(heat,vec(u[n])),scale(real(h),vec(Q0.get(n,ZERO))))
        diff=minus(v,step)
        assert norm(minus(diff,int_dev[n]))<=tol
        residual_mass+=weight(n)*norm(diff)
    assert residual_mass<=norm_integral+tol
    bound=(Decimal(51000000)+real(mu)*Decimal(5000000))/2*real(h)**2
    assert norm_integral<=bound+tol,(norm_integral,bound)
    assert bound<=Decimal(25750000)*real(h)**2+tol
    return len(out-set(s)),residual_mass

def run():
    with localcontext() as ctx:
        ctx.prec=100
        rng=Random(2023487525750000)
        pool=[(x,y,z) for x in range(-3,4) for y in range(-3,4)
              for z in range(-2,3)]
        cases=0; newborn=0; max_res=Decimal(0)
        for size in (1,2,4,7):
            for trial in range(24):
                s=rng.sample(pool,size)
                u={n:first.vscale(Q(1,1000),ana.a.rnd_vec(rng)) for n in s}
                d={n:first.vscale(Q(1,500),ana.a.rnd_vec(rng))
                   if (trial+sum(n))%5 else ZERO for n in s}
                mu=(Q(0),Q(1,100),Q(1,10))[trial%3]
                h=(Q(1,100),Q(1,200),Q(1,500))[trial%3]
                born,res=test_case(s,u,d,mu,h)
                newborn+=born;cases+=1;max_res=max(max_res,res)
        # Fully explicit generated modes, zero initial coefficients and collision.
        initial=first.make_initial(Q(1),Q(1))
        s=sorted(set(initial)|{(0,0,0),(1,1,0),(-1,-1,0)})
        for mu in (Q(0),Q(1,10)):
            u={n:first.vscale(Q(1,1000),initial.get(n,ZERO)) for n in s}
            d={n:first.vscale(Q(1,800),ana.a.rnd_vec(rng)) for n in s}
            born,res=test_case(s,u,d,mu,Q(1,100))
            newborn+=born;cases+=1;max_res=max(max_res,res)
        # Exact first moments of both distinct affine time clocks.
        for mu in (Q(0),Q(1,100),Q(1,10)):
            for h in (Q(1,1000),Q(1,10),Q(3,7)):
                source_clock=Q(51000000)*h*h/2
                viscous_clock=mu*Q(5000000)*h*h/2
                assert source_clock+viscous_clock==(
                    Q(51000000)+mu*5000000)*h*h/2
                assert source_clock+viscous_clock<=25750000*h*h
        print(f'PASS: {cases} full-complex-Leray Duhamel quadrature paths')
        print(f'PASS: {newborn} nonlinear output modes outside input supports')
        print('PASS: 1-exp(-mu*h*|n|^2) <= mu*h*|n|^2, including nu=0')
        print('PASS: exact Fourier collision-sensitive lagged-source norm splitting')
        print('PASS: local Duhamel residual <= (51000000+mu*5000000)*h^2/2')
        print('PASS: for mu<=1/10, local residual <=25750000*h^2')
        print('NOTE: numerical Duhamel endpoints are not asserted to solve the Galerkin ODE')
        print('NOTE: the Lean theorem retains Duhamel and the high-radius path ball as hypotheses')

if __name__=='__main__':run()

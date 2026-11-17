#!/usr/bin/env python3
"""Independent real-time exact-Leray Galerkin integrating-factor audit.

Compares exact Gaussian-rational convolution against a Python complex
representation, integrates the ACTUAL finite Galerkin ODE numerically with
RK4, and compares endpoints with retarded heat-source quadrature.
This is a numerical test, not a Lean proof or a convergence theorem.
"""
from collections import defaultdict
from fractions import Fraction as Q
from math import exp, sqrt
from random import Random

import check_h3_three_band_z3_galerkin_analytic_consistency as ana


def cv(z):
    return complex(float(z[0]), float(z[1]))


def complex_source(s, U):
    S=set(s)
    out={n:(0j,0j,0j) for n in s}
    for p in s:
        for q in s:
            n=tuple(p[i]+q[i] for i in range(3))
            if n not in S:
                continue
            contract=sum(q[i]*U[p][i] for i in range(3))
            raw=[-1j*contract*U[q][j] for j in range(3)]
            d2=sum(x*x for x in n)
            if d2:
                defect=sum(n[j]*raw[j] for j in range(3))/d2
                raw=[raw[j]-n[j]*defect for j in range(3)]
            out[n]=tuple(out[n][j]+raw[j] for j in range(3))
    return out


def mix(s, u, deriv, h):
    return {n:tuple(u[n][j]+h*deriv[n][j] for j in range(3)) for n in s}


def make_ode(mu, s, U):
    Qs=complex_source(s,U)
    return {n:tuple(Qs[n][j]-mu*sum(k*k for k in n)*U[n][j]
                     for j in range(3)) for n in s}


def rk4(mu, s, u, h):
    a=make_ode(mu,s,u)
    b=make_ode(mu,s,mix(s,u,a,h/2))
    c=make_ode(mu,s,mix(s,u,b,h/2))
    d=make_ode(mu,s,mix(s,u,c,h))
    return {n:tuple(u[n][j]+h*(a[n][j]+2*b[n][j]+2*c[n][j]+d[n][j])/6
                    for j in range(3)) for n in s}


def nrm(v):
    return sqrt(sum(abs(x)**2 for x in v))


def mass(s,U,R):
    return sum(R**sum(abs(x) for x in n)*nrm(U[n]) for n in s)


def test_case(s, seed, mu, h):
    rng=Random(seed)
    ur={n:ana.a.rnd_vec(rng) for n in s}
    U0={n:tuple(0.0009*cv(z) for z in ur[n]) for n in s}
    initial_source=ana.source(s,ur,ur)
    projected=complex_source(s,U0)
    for n in s:
        exact=initial_source.get(n,ana.ZERO)
        for j in range(3):
            assert abs(projected[n][j]-(0.0009**2)*cv(exact[j]))<1e-15
    new=sum(1 for n in initial_source if n not in s and
            any(z != ana.a.old.z() for z in initial_source[n]))
    # The derivative of e^(lambda*t) u_n is exactly e^(lambda*t) Q_n.
    t0=0.17
    flow0=make_ode(mu,s,U0)
    for n in s:
        lam=mu*sum(x*x for x in n)
        for j in range(3):
            lhs=exp(lam*t0)*(flow0[n][j]+lam*U0[n][j])
            rhs=exp(lam*t0)*projected[n][j]
            assert abs(lhs-rhs)<1e-12
    m=128
    states=[U0]
    for _ in range(m):
        states.append(rk4(mu,s,states[-1],h/m))
    Uend=states[-1]
    assert all(mass(s,ut,9/5)<=100 for ut in states)
    assert all(mass(s,{n:tuple(ut[n][j]-U0[n][j] for j in range(3))
                             for n in s},3/2)<=51000*(k*h/m)+1e-12
               for k,ut in enumerate(states))
    # Simpson quadrature of the ACTUAL nonlinear source along the RK4 path.
    accum={n:[0j,0j,0j] for n in s}
    for k,ut in enumerate(states):
        wt=1 if k in (0,m) else 4 if k%2 else 2
        q=complex_source(s,ut)
        t=h*k/m
        for n in s:
            fac=exp(-mu*sum(x*x for x in n)*(h-t))
            for j in range(3):
                accum[n][j]+=wt*fac*q[n][j]
    for n in s:
        for j in range(3):
            accum[n][j]*=h/(3*m)
    mild={n:tuple(exp(-mu*sum(x*x for x in n)*h)*U0[n][j]+accum[n][j]
                  for j in range(3)) for n in s}
    err=mass(s,{n:tuple(Uend[n][j]-mild[n][j] for j in range(3))
                for n in s},5/4)
    assert err<5e-10,(seed,err)
    step={n:tuple(exp(-mu*sum(x*x for x in n)*h)*U0[n][j]
                  +h*projected[n][j] for j in range(3)) for n in s}
    residual=mass(s,{n:tuple(Uend[n][j]-step[n][j] for j in range(3))
                     for n in s},5/4)
    assert residual<=25750000*h*h
    return new, err, residual


def run():
    rng=Random(29062886)
    pool=[(x,y,z) for x in range(-2,3) for y in range(-2,3)
          for z in range(-1,2)]
    samples=0; new_total=0; max_error=0.; max_residual=0.
    for count in (3,5,8,11):
        for k in range(12):
            s=rng.sample(pool,count)
            # Retain a generated output with an initially zero coefficient.
            p,q=s[0],s[1]
            target=tuple(p[j]+q[j] for j in range(3))
            if target not in s:
                s[-1]=target
            new,err,res=test_case(s,10000*count+k,(0.,0.003,0.1)[k%3],
                                   (0.008,0.013,0.022)[k%3])
            samples+=1;new_total+=new
            max_error=max(max_error,err)
            max_residual=max(max_residual,res)
    assert new_total>0
    print(f'PASS: {samples} actual full-complex-Leray Galerkin RK4/retarded Duhamel cases')
    print(f'PASS: {new_total} quadratic frequencies outside retained output supports')
    print('PASS: integrating-factor derivative cancels the exact viscosity term')
    print(f'PASS: numerical endpoint-Duhamel error < 5e-10; max {max_error:.3g}')
    print(f'PASS: local residual <= 25750000 h^2; max observed {max_residual:.3g}')
    print('NOTE: numerical ODE integration is not a substitute for Lean FTC or PDE existence')

if __name__=='__main__':run()

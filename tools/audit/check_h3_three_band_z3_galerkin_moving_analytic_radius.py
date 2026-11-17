#!/usr/bin/env python3
"""Independent moving-radius and finite-cutoff complex-Leray Galerkin audit.

Checks the actual ordered-pair projected Fourier source, with floating-point
weights and exact lattice frequencies. This does not prove ODE existence,
zero-safe Dini differentiation, or analytic-ball persistence.
"""
from math import exp, log, sqrt
from random import Random

import check_h3_three_band_z3_galerkin_ode_to_duhamel as ode


def degree(n):
    return sum(abs(x) for x in n)


def freq2(n):
    return sum(x*x for x in n)


def norm_mass(s, values, r):
    return sum(exp(r*degree(n))*ode.nrm(values[n]) for n in s)


def deriv_mass(s, values, r):
    return sum(degree(n)*exp(r*degree(n))*ode.nrm(values[n]) for n in s)


def lap_mass(s, values, r):
    return sum(freq2(n)*exp(r*degree(n))*ode.nrm(values[n]) for n in s)


def sub(s, u, v):
    return {n:tuple(x-y for x,y in zip(u[n],v[n])) for n in s}


def check():
    rng=Random(210921)
    pool=[(i,j,k) for i in range(-3,4) for j in range(-2,3) for k in range(-2,3)]
    cases=0; generated=0; max_ratio=0.0
    window=(log(2)-log(9/5))/100
    assert window>0
    for count in (3,6,10,15):
        for k in range(16):
            s=rng.sample(pool,count)
            p,q=s[0],s[1]
            generated_mode=tuple(p[j]+q[j] for j in range(3))
            if generated_mode not in s:
                s[-1]=generated_mode
            # Independent random complex bands, including exact zero coefficients.
            U={n:tuple(complex(rng.uniform(-1,1), rng.uniform(-1,1))
                         * (0 if (i+k)%11==0 else .025)
                         for i in range(3)) for n in s}
            V={n:tuple(complex(rng.uniform(-1,1), rng.uniform(-1,1))*.02
                         for _ in range(3)) for n in s}
            if k%5==0:
                U[s[-1]]=(0j,0j,0j)
            r=log((1.15,1.50,1.80,1.99)[k%4])
            delta=window*(k/15)
            r_moving=log(2)-100*delta
            assert log(9/5)-1e-14<=r_moving<=log(2)+1e-14
            assert r_moving >= r if r <= log(9/5) else True
            m=norm_mass(s,U,r)
            d=deriv_mass(s,U,r)
            Q=ode.complex_source(s,U)
            qmass=norm_mass(s,Q,r)
            assert qmass <= m*d+1e-9,(count,k,qmass,m*d)
            if m<=100:
                assert qmass-100*d<=1e-9
            assert norm_mass(s,U,log(9/5)) <= norm_mass(s,U,r_moving)+1e-9
            # The exact analytic-radius derivative carries -100*m(n).
            for n in s:
                eps=1e-7
                numeric=(exp((r_moving-100*eps)*degree(n))-
                         exp((r_moving+100*eps)*degree(n)))/(2*eps)
                target=-100*degree(n)*exp(r_moving*degree(n))
                assert abs(numeric-target) <= max(1e-5,abs(target)*2e-6)
            K=max(degree(n) for n in s)
            L=max(freq2(n) for n in s)
            assert d<= K*m+1e-9
            assert lap_mass(s,U,r)<=L*m+1e-9
            for mu in (0.,.03,.1):
                DU=sub(s,U,V)
                F_U=ode.make_ode(mu,s,U)
                F_V=ode.make_ode(mu,s,V)
                difference=norm_mass(s,sub(s,F_U,F_V),r)
                bound=(mu*L+K*(norm_mass(s,U,r)+norm_mass(s,V,r)))*norm_mass(s,DU,r)
                assert difference<=bound+2e-9,(count,k,mu,difference,bound)
                if bound>0:
                    max_ratio=max(max_ratio,difference/bound)
            all_outputs={tuple(p[i]+q[i] for i in range(3))
                         for p in s for q in s}
            generated+=len(all_outputs-set(s))
            cases+=1
    assert generated>0
    print(f'PASS: {cases} complex-Leray moving-radius and cutoff-Lipschitz cases')
    print(f'PASS: {generated} generated output modes outside retained support')
    print('PASS: exact shrinking window and -100*degree weight derivative')
    print('PASS: W_r(Q) <= W_r(u)*D_r(u) and absorption at W_r <= 100')
    print('PASS: fixed-cutoff K=max true degree, L=max physical |n|^2')
    print(f'PASS: fixed-cutoff Galerkin field Lipschitz; max observed ratio {max_ratio:.5g}')
    print('NOTE: moving 100-ball preservation and ODE existence remain open')


if __name__=='__main__':
    check()

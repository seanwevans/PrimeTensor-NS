#!/usr/bin/env python3
"""Independent zero-safe moving Wiener Galerkin derivative audit.

Evaluates the ACTUAL complex Leray ordered convolution and physical Laplacian
at random finite Z^3 sets. Numerical finite differences corroborate the
exact regularized derivative at zero and nonzero Fourier coefficients.
This is not a Lean compilation, a flow-existence result, or a proof of the
analytic-ball invariance/comparison step.
"""
from math import exp, log, sqrt
from random import Random

import check_h3_three_band_z3_galerkin_ode_to_duhamel as ode


def degree(n):
    return sum(abs(x) for x in n)


def weight(r, n):
    return exp(r*degree(n))


def amplitude(x, epsilon):
    return sqrt(ode.nrm(x)**2+epsilon**2)


def inner(x,y):
    return sum((v.conjugate()*z).real for v,z in zip(x,y))


def smooth_mass(s, U, r, epsilon):
    return sum(weight(r,n)*amplitude(U[n],epsilon) for n in s)


def smooth_derivative(s, U, r, epsilon):
    return sum(degree(n)*weight(r,n)*amplitude(U[n],epsilon) for n in s)


def true_mass(s, U, r):
    return sum(weight(r,n)*ode.nrm(U[n]) for n in s)


def true_derivative(s, U, r):
    return sum(degree(n)*weight(r,n)*ode.nrm(U[n]) for n in s)


def shift(U, F, h):
    return {n:tuple(U[n][j]+h*F[n][j] for j in range(3)) for n in U}


def check():
    rng = Random(271117)
    pool = [(i,j,k) for i in range(-3,4) for j in range(-3,4) for k in range(-2,3)]
    cases=0; generated=0; zeros=0; max_rel=0.; worst=0.
    for size in (3,5,8,12):
        for k in range(20):
            s = rng.sample(pool,size)
            p,q = s[0],s[1]
            produced = tuple(p[i]+q[i] for i in range(3))
            if produced not in s: s[-1] = produced
            U={n:tuple(complex(rng.uniform(-1,1),rng.uniform(-1,1))*.002
                       for _ in range(3)) for n in s}
            for j,n in enumerate(s):
                if (k+j)%6==0: U[n]=(0j,0j,0j);zeros+=1
            eps = (0.01, 0.05, 0.2)[k%3]
            r = log((1.2,1.5,1.8,2)[k%4])
            mu = (0., .01, .1)[k%3]
            Q = ode.complex_source(s,U)
            F = ode.make_ode(mu,s,U)
            smooth=smooth_mass(s,U,r,eps)
            D=smooth_derivative(s,U,r,eps)
            W=true_mass(s,U,r)
            T=true_derivative(s,U,r)
            assert W<=smooth+1e-12
            assert T<=D+1e-12
            assert smooth<=W+eps*sum(weight(r,n) for n in s)+1e-12
            assert true_mass(s,Q,r)<=W*T+1e-11
            exact = 0.
            for n in s:
                w=weight(r,n); A=amplitude(U[n],eps)
                num=inner(U[n],F[n]); normQ=ode.nrm(Q[n]); m=degree(n)
                assert A>0
                assert num/A<=normQ+1e-10
                term=(-100*m)*w*A+w*num/A
                assert term<=w*normQ-100*m*w*A+1e-8
                exact += term
            assert exact <= (smooth-100)*D + 1e-7,(size,k,exact,(smooth-100)*D)
            if smooth<=100: assert exact<=1e-7
            h=1e-7
            plus=smooth_mass(s,shift(U,F,h),r-100*h,eps)
            minus=smooth_mass(s,shift(U,F,-h),r+100*h,eps)
            approx=(plus-minus)/(2*h)
            rel=abs(approx-exact)/max(1,abs(exact))
            max_rel=max(max_rel,rel)
            worst=max(worst,abs(approx-exact))
            assert rel<1e-6,(size,k,exact,approx,rel)
            outputs={tuple(a[j]+b[j] for j in range(3)) for a in s for b in s}
            generated+=len(outputs-set(s))
            cases+=1
    assert zeros>0 and generated>0
    print(f'PASS: {cases} full-Leray zero-safe moving Wiener ODE derivative cases')
    print(f'PASS: {zeros} exactly zero input Fourier coefficients')
    print(f'PASS: {generated} generated frequencies outside selected output set')
    print(f'PASS: regularized norm sandwich and derivative source-damping inequality')
    print(f'PASS: finite-difference versus analytic derivative max relative {max_rel:.3g}; max abs {worst:.3g}')
    print('NOTE: analytic-ball comparison, ODE flow existence, and Lean compilation not checked')


if __name__=='__main__':
    check()

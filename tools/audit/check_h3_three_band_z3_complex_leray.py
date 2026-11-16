#!/usr/bin/env python3
"""Exact Z3 complex Leray contraction and all-output ordered convolution test.

Uses rational Gaussian complex numbers, the explicit -i Fourier transport
symbol and the REAL Euclidean projector. All single-mode energy and source
estimates use exact Fraction arithmetic; only the final sums of square roots
use 75-digit Decimal. This is not a Lean proof or a PDE existence argument.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext
from random import Random
from collections import defaultdict
import check_h3_three_band_leray_symbol as old

ZERO=old.z()
VZERO=(ZERO,ZERO,ZERO)

def dsum(xs):
    v=VZERO
    for x in xs:v=old.vector_add(v,x)
    return v

def squared(z):return z[0]*z[0]+z[1]*z[1]
def n2(v):return sum(squared(z) for z in v)
def d2(n):return sum(q*q for q in n)
def degree(n):return sum(abs(q) for q in n)
def dot_real(k,v):return old.dot_real_complex(k,v)

def leray(k,v):
    if d2(k)==0:return v
    dot=dot_real(k,v)
    factor=old.zscale(F(1,d2(k)),dot)
    return tuple(old.zadd(x,old.zneg(old.zscale(j,factor)))
                 for x,j in zip(v,k))

def transport(n,q,u,v):
    c=dot_real(q,u)
    return leray(n,tuple(old.zminus_i(old.zmul(c,x)) for x in v))

def square_sum_decimal(x):
    with localcontext() as ctx:
        ctx.prec=85
        return (Decimal(x.numerator)/Decimal(x.denominator)).sqrt()

def rnd_vec(rng):
    return tuple(old.z(rng.randrange(-3,4),rng.randrange(-2,3)) for _ in range(3))

def trial(s,t,u,v,r):
    outputs=defaultdict(list)
    for p in s:
        for q in t:
            n=old.add_modes(p,q)
            f=tuple(old.zminus_i(old.zmul(dot_real(q,u[p]),x)) for x in v[q])
            z=leray(n,f)
            outputs[n].append(z)
            # Orthogonal projection is a contraction, exactly.
            assert n2(z)<=n2(f)
            if d2(n):
                assert n2(f)==n2(z)+squared(dot_real(n,f))/d2(n)
                assert dot_real(n,z)==ZERO
            # Cauchy-Schwarz and Euclidean <= l1 frequency, exactly.
            assert squared(dot_real(q,u[p]))<=d2(q)*n2(u[p])
            assert d2(q)<=degree(q)**2
            assert n2(z)<=d2(q)*n2(u[p])*n2(v[q])
            assert n2(z)<=degree(q)**2*n2(u[p])*n2(v[q])
            assert degree(n)<=degree(p)+degree(q)
            assert r**degree(n)<=r**degree(p)*r**degree(q)
    with localcontext() as ctx:
        ctx.prec=85
        dec=lambda a:Decimal(a.numerator)/Decimal(a.denominator)
        w=lambda n:dec(r**degree(n))
        lhs=sum(w(n)*square_sum_decimal(n2(dsum(terms)))
                 for n,terms in outputs.items())
        wa=sum(w(p)*square_sum_decimal(n2(u[p])) for p in s)
        db=sum(w(q)*degree(q)*square_sum_decimal(n2(v[q])) for q in t)
        rhs=wa*db
        assert lhs<=rhs+Decimal('1e-65'),(lhs,rhs)
    return sum(len(terms)-1 for terms in outputs.values())

def run():
    old.main()
    rng=Random(4006411)
    modes=[(a,b,c) for a in range(-2,3) for b in range(-2,3)
                     for c in range(-1,2)]
    checked=0; collisions=0
    for radius in (F(1),F(5,4),F(3,2),F(2)):
        for size in range(1,8):
            for _ in range(24):
                s=rng.sample(modes,size)
                t=rng.sample(modes,size+2)
                u={p:rnd_vec(rng) for p in s}
                v={q:rnd_vec(rng) for q in t}
                collisions+=trial(s,t,u,v,radius)
                checked+=1
    assert collisions>0
    print(f'PASS: {checked} exact projected complex convolution support/radius cases')
    print(f'PASS: {collisions} colliding ordered-pair output frequencies')
    print('PASS: exact Leray Pythagoras, solenoidality, Cauchy-Schwarz, Z3 l2<=l1')
    print('PASS: 85-digit all-output weighted Wiener convolution comparisons')
    print('NOTE: Galerkin ODE differentiation and infinite-dimensional limit remain open')
if __name__=='__main__':run()

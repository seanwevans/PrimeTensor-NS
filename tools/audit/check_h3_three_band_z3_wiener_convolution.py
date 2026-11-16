#!/usr/bin/env python3
"""Independent Z3 Fourier-Wiener convolution audit on all ordered pairs.

Exact rational powers R^m rather than floating-point exponentials;
checks actual integer-lattice triangle, all output collisions, and
full pair-sum majorants. Finite tests are not a substitute for Lean.
"""
from fractions import Fraction as F
from itertools import product
import random

def add(p,q): return tuple(x+y for x,y in zip(p,q))
def neg(p): return tuple(-x for x in p)
def degree(p): return sum(abs(x) for x in p)
def weight(R,p): return R**degree(p)

def check_support(S,T,a,b,R):
    W1=sum(weight(R,p)*a[p] for p in S)
    W2=sum(weight(R,q)*b[q] for q in T)
    D2=sum(weight(R,q)*degree(q)*b[q] for q in T)
    raw=F(0); drv=F(0)
    convolution={}; derivative={}
    for p in S:
        for q in T:
            n=add(p,q)
            assert degree(n)<=degree(p)+degree(q)
            assert weight(R,n)<=weight(R,p)*weight(R,q)
            m=a[p]*b[q]
            convolution[n]=convolution.get(n,F(0))+m
            derivative[n]=derivative.get(n,F(0))+degree(q)*m
            raw+=weight(R,n)*m
            drv+=weight(R,n)*degree(q)*m
    assert raw==sum(weight(R,n)*x for n,x in convolution.items())
    assert drv==sum(weight(R,n)*x for n,x in derivative.items())
    assert raw<=W1*W2
    assert drv<=W1*D2
    return len(convolution)

def main():
    rg=random.Random(244)
    supports=[]
    base=[(1,0,0),(2,1,0),(3,1,0)]
    supports.append(base+[neg(p) for p in base])
    for count in (1,3,6,9,15,23):
        supports.append(list(dict.fromkeys(tuple(rg.randrange(-4,5) for _ in range(3)) for _ in range(count))))
    checked=0; collisions=0
    for R in (F(1),F(5,4),F(3,2),F(2),F(7,3)):
        for S in supports:
            for T in supports:
                a={p:F(1+rg.randrange(1,17),2+rg.randrange(0,7)) for p in S}
                b={q:F(1+rg.randrange(1,17),2+rg.randrange(0,7)) for q in T}
                outputs=check_support(S,T,a,b,R)
                collisions+=len(S)*len(T)-outputs
                checked+=1
    assert collisions>0
    # Zero and arbitrarily separated frequencies; no cutoff constant.
    for n in (0,1,7,100,1024):
        S=[(n,0,0),(-n,0,0)] if n else [(0,0,0)]
        a={p:F(1) for p in S}
        check_support(S,S,a,a,F(5,4))
    print(f'PASS: {checked} exact Z3 ordered weighted convolution/derivative cases')
    print(f'PASS: {collisions} pair-to-output collisions included in aggregate checks')
    print('PASS: m(p+q)<=m(p)+m(q) and W_r*D_r majorant, no cardinality factor')
    print('NOTE: Leray projection identification, norm differentiation, Galerkin limit separate')

if __name__=='__main__': main()

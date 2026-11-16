#!/usr/bin/env python3
"""Independent full Z3 projected Galerkin output check, including collisions.

Exact Gaussian-rational Leray projection and frequency comparisons. The only
nonrational operation is Euclidean vector norm, evaluated by high-precision
Decimal for finite-frequency Wiener sums. Tests deliberately arbitrary output
subsets and output modes absent from both inputs, not a six-mode closure.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext
from random import Random
from collections import defaultdict
import check_h3_three_band_z3_complex_leray as prior

old = prior.old
Z = prior.ZERO
VZ = prior.VZERO


def norm_decimal(v):
    with localcontext() as ctx:
        ctx.prec = 90
        squared = prior.n2(v)
        return (Decimal(squared.numerator) / Decimal(squared.denominator)).sqrt()


def source(s, t, u, v):
    by_output = defaultdict(list)
    for p in s:
        for q in t:
            n = old.add_modes(p,q)
            by_output[n].append(prior.transport(n,q,u[p],v[q]))
    return by_output


def test_case(s,t,u,v,r,rng):
    by_output=source(s,t,u,v)
    keys=set(by_output)
    extras={(30,0,0),(-30,2,1),(0,0,0)}
    output_sets=[keys, set(list(keys)[::2]), keys | extras, extras, set()]
    # Add one arbitrary subset; all tests use independent output selection.
    output_sets.append({n for n in keys if rng.getrandbits(1)})
    with localcontext() as ctx:
        ctx.prec=90
        as_dec=lambda a: Decimal(a.numerator)/Decimal(a.denominator)
        weight=lambda n: as_dec(r**prior.degree(n))
        W=sum(weight(p)*norm_decimal(u[p]) for p in s)
        D=sum(weight(q)*prior.degree(q)*norm_decimal(v[q]) for q in t)
        rhs=W*D
        all_pairs=sum(weight(old.add_modes(p,q)) *
                      norm_decimal(prior.transport(old.add_modes(p,q),q,u[p],v[q]))
                      for p in s for q in t)
        assert all_pairs <= rhs + Decimal('1e-65')
        for output in output_sets:
            lhs=Decimal(0)
            pair_sum=Decimal(0)
            for n in output:
                terms=by_output.get(n,[])
                lhs += weight(n)*norm_decimal(prior.dsum(terms))
                pair_sum += weight(n)*sum((norm_decimal(z) for z in terms),Decimal(0))
            assert lhs<=pair_sum+Decimal('1e-65'),(lhs,pair_sum)
            assert pair_sum<=all_pairs+Decimal('1e-65'),(pair_sum,all_pairs)
            assert lhs<=rhs+Decimal('1e-65'),(lhs,rhs)
    for p in s:
        for q in t:
            assert prior.d2(q) <= prior.degree(q)**2
    return sum(max(0,len(v)-1) for v in by_output.values())


def run():
    prior.old.main()
    rng=Random(5353391)
    modes=[(a,b,c) for a in range(-3,4) for b in range(-2,3)
                      for c in range(-2,3)]
    count=0; collisions=0
    for R in (F(1),F(5,4),F(3,2),F(2)):
        for size in (1,2,3,5,7):
            for _ in range(20):
                s=rng.sample(modes,size)
                t=rng.sample(modes,size+2)
                u={p:prior.rnd_vec(rng) for p in s}
                v={q:prior.rnd_vec(rng) for q in t}
                collisions+=test_case(s,t,u,v,R,rng)
                count+=1
    assert collisions > 100
    print(f'PASS: {count} full complex Leray Galerkin output-set tests')
    print(f'PASS: {collisions} colliding ordered pair output frequencies')
    print('PASS: six output-support policies per case, including missing/new modes')
    print('PASS: norm of full output <= ordered pair norms <= Wiener W*D')
    print('PASS: exact Z3 Euclidean squared norm <= l1 squared degree')
    print('NOTE: tests are independent numerical audits, not Lean/PDE proofs')

if __name__ == '__main__':
    run()

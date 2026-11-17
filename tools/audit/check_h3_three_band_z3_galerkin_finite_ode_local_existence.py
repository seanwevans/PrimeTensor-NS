#!/usr/bin/env python3
"""Check the finite complex-Leray ODE quadratic Taylor identity numerically.

This is a regression check, NOT a replacement for Lean verification.
"""
import cmath
import math
import random
from collections import defaultdict
from pathlib import Path

rng = random.Random(244)
S = [(0, 0, 0), (1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (1, 1, 0), (-1, -1, 0)]

def add(p, q):
    return tuple(p[i] + q[i] for i in range(3))

def inner(a, b):
    return sum(a[i].conjugate() * b[i] for i in range(3))

def project(n, x):
    d = sum(i * i for i in n)
    if d == 0:
        return x
    factor = sum(n[i] * x[i] for i in range(3)) / d
    return tuple(x[i] - factor * n[i] for i in range(3))

def Q(x, y):
    out = {}
    for n in S:
        total = [0j] * 3
        for p in S:
            for q in S:
                if add(p, q) != n:
                    continue
                scalar = -1j * inner(tuple(complex(i) for i in q), x[p])
                v = project(n, tuple(scalar * y[q][j] for j in range(3)))
                total = [total[j] + v[j] for j in range(3)]
        out[n] = tuple(total)
    return out

def field(x, mu=0.1):
    q = Q(x, x)
    return {n: tuple(q[n][i] - mu * sum(j*j for j in n) * x[n][i]
                     for i in range(3)) for n in S}

for trial in range(6):
    x = {n: tuple(complex(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in range(3)) for n in S}
    h = {n: tuple(complex(rng.uniform(-0.1, 0.1), rng.uniform(-0.1, 0.1)) for _ in range(3)) for n in S}
    xp = {n: tuple(x[n][i] + h[n][i] for i in range(3)) for n in S}
    f0, f1 = field(x), field(xp)
    qhx, qxh, qhh = Q(h, x), Q(x, h), Q(h, h)
    error = max(abs((f1[n][j] - f0[n][j]) -
                    (qhx[n][j] + qxh[n][j] + qhh[n][j] -
                     0.1 * sum(i*i for i in n) * h[n][j]))
                for n in S for j in range(3))
    if error > 1e-10:
        raise AssertionError((trial, error))
print('PASS: exact finite quadratic Taylor expansion, 6 deterministic complex-valued trials')
print('NOTE: numerical tests do not establish Fréchet differentiability in Lean')

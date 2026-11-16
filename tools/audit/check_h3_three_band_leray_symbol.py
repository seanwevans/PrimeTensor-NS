#!/usr/bin/env python3
"""Exact rational/Gaussian-rational test of a full six-mode NS Fourier symbol.

Run from anywhere. This uses all ordered p+q=k interactions, Hermitian
negative-frequency partners, and the actual Leray projector. It is an
independent arithmetic audit of the Lean finite-mode counterexample.
"""
from fractions import Fraction as Q


def z(x=0, y=0):
    return (Q(x), Q(y))


def zadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def zmul(x, y):
    return (x[0] * y[0] - x[1] * y[1],
            x[0] * y[1] + x[1] * y[0])


def zneg(x):
    return (-x[0], -x[1])


def zconj(x):
    return (x[0], -x[1])


def zscale(q, x):
    return (Q(q) * x[0], Q(q) * x[1])


def zminus_i(x):
    return (x[1], -x[0])


def add_modes(a, b):
    return tuple(x + y for x, y in zip(a, b))


def neg_mode(a):
    return tuple(-x for x in a)


def subtract_modes(a, b):
    return tuple(x - y for x, y in zip(a, b))


def dot_real_complex(k, v):
    return tuple_sum([zscale(ki, vi) for ki, vi in zip(k, v)])


def dot_complex_complex(u, v):
    return tuple_sum([zmul(x, y) for x, y in zip(u, v)])


def tuple_sum(items):
    ans = z()
    for x in items:
        ans = zadd(ans, x)
    return ans


def vector_add(u, v):
    return tuple(zadd(x, y) for x, y in zip(u, v))


def vector_scale(q, v):
    return tuple(zscale(q, x) for x in v)


def leray(k, v):
    kk = sum(x * x for x in k)
    assert kk > 0
    multiplier = zscale(Q(1, kk), dot_real_complex(k, v))
    return tuple(zadd(vi, zneg(zscale(ki, multiplier)))
                 for ki, vi in zip(k, v))


def coefficient(k, velocities):
    result = tuple(z() for _ in range(3))
    for p, up in velocities.items():
        q = subtract_modes(k, p)
        uq = velocities.get(q)
        if uq is None:
            continue
        d = dot_real_complex(q, up)
        term = tuple(zminus_i(zmul(d, component)) for component in uq)
        result = vector_add(result, term)
    return leray(k, result)


def modal_work(k, velocities):
    out = coefficient(k, velocities)
    conj_u = tuple(zconj(component) for component in velocities[k])
    value = dot_complex_complex(conj_u, out)
    assert value[1] == 0, (k, value)
    return value[0]


def main():
    a, b = (1, 0, 0), (2, 1, 0)
    c = add_modes(a, b)
    A, B, C = (0, 1, -1), (-1, 2, 1), (0, 0, -1)
    assert c == (3, 1, 0)
    assert all(sum(x * y for x, y in zip(k, v)) == 0
               for k, v in ((a, A), (b, B), (c, C)))
    assert sum(x * x for x in a) < Q(9, 4) < sum(x * x for x in b)
    assert sum(x * x for x in b) < 9 < sum(x * x for x in c)

    velocities = {
        a: tuple(z(x) for x in A),
        b: tuple(z(x) for x in B),
        c: tuple(z(0, x) for x in C),
    }
    for k, u in list(velocities.items()):
        velocities[neg_mode(k)] = tuple(zconj(x) for x in u)
    assert len(velocities) == 6

    # Exact quadratic Navier-Stokes term: -i P_k sum_{p+q=k} (u_p.q) u_q.
    works = tuple(modal_work(k, velocities) for k in (a, b, c))
    assert works == (Q(-1), Q(-1), Q(2)), works
    assert sum(works) == 0
    assert -works[0] > 0           # Outward flux across N=3/2.
    assert works[2] > 0            # Outward flux across 2N=3.
    assert works[0] + works[1] == -works[2]

    # Both Hermitian partners have the same real energy-work contribution.
    for k in (a, b, c):
        assert modal_work(neg_mode(k), velocities) == modal_work(k, velocities)

    print('PASS: exact six-mode Gaussian-rational Navier-Stokes Leray convolution')
    print('frequency-square order: 1 < (3/2)^2 < 5 < 3^2 < 10')
    print(f'positive-mode nonlinear work: {works}')
    print('outward cutoffs N=3/2 and 2N=3: both positive')
    print('Hermitian counterparts and total instantaneous energy cancellation: PASS')


if __name__ == '__main__':
    main()

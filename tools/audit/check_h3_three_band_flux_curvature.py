#!/usr/bin/env python3
"""Exact second temporal variation of full unforced NS three-band Fourier flux.

Derivatives are evaluated from the genuine infinite-system convolution at
finite-Fourier initial data, NOT from a six-mode Galerkin closure.  Because
only time-zero jets are needed, their frequency supports are finite.

Independent checks: both quadratic NS energy ledgers at third order and
exact degree-six polynomial interpolation of the original cubic flux.
"""
from fractions import Fraction as F
import check_h3_three_band_flux_slope as first

ZERO = first.VZERO


def clean(d):
    return {k: v for k, v in d.items() if v != ZERO}


def plus(*terms):
    out = {}
    for d in terms:
        for k, v in d.items():
            out[k] = first.vadd(out.get(k, ZERO), v)
    return clean(out)


def times(c, d):
    return clean({k: first.vscale(c, v) for k, v in d.items()})


def damping(d, nu):
    return clean({k: first.vscale(-nu * first.norm2(k), v)
                  for k, v in d.items()})


def bilinear(x, y):
    """Exact -i P_n sum_{p+q=n}(q·x_p)y_q, all ordered interactions."""
    support = {first.old.add_modes(p, q) for p in x for q in y}
    return clean({n: first.full_ordered_leray(n, x, y)
                  for n in support if n != (0, 0, 0)})


def second_jet(k, A, nu):
    u = first.make_initial(k, A)
    Q = bilinear(u, u)
    u1 = plus(Q, damping(u, nu))
    Q1 = plus(bilinear(u1, u), bilinear(u, u1))
    u2 = plus(Q1, damping(u1, nu))
    Q2 = plus(bilinear(u2, u), times(F(2), bilinear(u1, u1)),
              bilinear(u, u2))
    u3 = plus(Q2, damping(u2, nu))
    return (u, u1, u2, u3), (Q, Q1, Q2)


def inner(x, y):
    return first.inner_real(x, y)


def work_jet(us, qs, p):
    u, u1, u2, _ = us
    Q, Q1, Q2 = qs
    U = [w.get(p, ZERO) for w in (u, u1, u2)]
    V = [w.get(p, ZERO) for w in (Q, Q1, Q2)]
    return (inner(U[0], V[0]),
            inner(U[1], V[0]) + inner(U[0], V[1]),
            inner(U[2], V[0]) + 2 * inner(U[1], V[1]) +
            inner(U[0], V[2]))


def cutoff_selector(k, p, band):
    q = first.norm2(p)
    if band == 'low':
        return 4 * q < 9 * k * k
    if band == 'high':
        return q > 9 * k * k
    raise ValueError(band)


def flux_jet(k, us, qs):
    support = set().union(*[set(x) for x in (*us, *qs)])
    works = {p: work_jet(us, qs, p) for p in support}
    assert all(sum(row[i] for row in works.values()) == 0 for i in (0, 1, 2))
    assert all(row == works[first.old.neg_mode(p)] for p, row in works.items())
    out = []
    for band, sign in (('low', -1), ('high', 1)):
        out.append(tuple(sign * sum(row[j] for p, row in works.items()
                                    if cutoff_selector(k, p, band))
                         for j in (0, 1, 2)))
    return tuple(out)


def energy_ledger_flux_curvature(k, nu, us):
    """Derive J'' from E''' + nu D'', independent of cubic flux expansion."""
    u, u1, u2, u3 = us
    support = set().union(*map(set, us))
    out = []
    for band, sign in (('low', -1), ('high', 1)):
        e3 = F(0)
        d2 = F(0)
        for p in support:
            if not cutoff_selector(k, p, band):
                continue
            U = [w.get(p, ZERO) for w in us]
            e3 += inner(U[0], U[3]) + 3 * inner(U[1], U[2])
            d2 += 2 * first.norm2(p) * (inner(U[1], U[1]) +
                                          inner(U[0], U[2]))
        out.append(sign * (e3 + nu * d2))
    return tuple(out)


def polynomial_interpolation_second(k, us):
    """Evaluate cubic J(u+t*u1+t^2*u2/2), then extract its exact t^2 term.

    This composite polynomial has degree <= 6.  Its even part minus J(0)
    has form a*t²+b*t⁴+c*t⁶, so 2a=3E(1)-3E(2)/10+E(3)/45,
    where E(j)=(J(j)+J(-j))/2-J(0).
    """
    u, u1, u2, _ = us
    def at(t):
        w = plus(u, times(t, u1), times(t*t/F(2), u2))
        return first.direct_flux_at_state(k, w)
    z = at(F(0))
    vals = []
    for n in (1, 2, 3):
        p = at(F(n)); m = at(F(-n))
        vals.append(tuple((p[i] + m[i])/2-z[i] for i in (0, 1)))
    return tuple(3*vals[0][i] - F(3,10)*vals[1][i] + F(1,45)*vals[2][i]
                 for i in (0,1))


def coeffs(nu, k, A):
    # Polynomial scaling of dimension [J'']=k^3 A^5*poly(nu*k/A).
    lower = (F(-1792,425)*k**3*A**5 + F(1148,5)*nu*k**4*A**4 +
             512*nu**2*k**5*A**3)
    upper = (F(-615688,12325)*k**3*A**5 - F(728,5)*nu*k**4*A**4 +
             1024*nu**2*k**5*A**3)
    return lower,upper


def run():
    first.run()
    checked = 0
    for k in (F(1), F(2), F(7)):
        for nu in (F(0), F(1,2), F(3)):
            for A in (F(1), 6*(nu+1)*k, 10*(nu+1)*k):
                us, qs = second_jet(k, A, nu)
                lo, hi = flux_jet(k, us, qs)
                assert lo[0] == 2*k*A**3 and hi[0] == 4*k*A**3
                assert lo[1] == -F(46,5)*k**2*A**4 - 32*nu*k**3*A**3
                assert hi[1] == F(36,5)*k**2*A**4 - 64*nu*k**3*A**3
                assert (lo[2], hi[2]) == coeffs(nu,k,A), (k,nu,A,lo,hi)
                assert energy_ledger_flux_curvature(k, nu, us) == (lo[2],hi[2])
                assert all(first.old.dot_real_complex(p, v) == first.ZERO
                           for state in us for p,v in state.items())
                if k == 1 and (A,nu) in ((1,F(0)),(1,F(1,2)),(1,F(3))):
                    assert polynomial_interpolation_second(k, us) == (lo[2],hi[2])
                checked += 1
    # Genuine sign contrast at amplitude 10*nu*k.
    for k in (F(1),F(2),F(7)):
        for nu in (F(1,2),F(1),F(3)):
            A=10*nu*k
            us,qs=second_jet(k,A,nu)
            lo,hi=flux_jet(k,us,qs)
            assert hi[1] > 0 and hi[2] < 0 and lo[1] < 0 and lo[2] > 0
    print(f'PASS: {checked} exact second-jet full-convolution cases')
    print('PASS: exact energy-ledger third-derivative independent cross-check')
    print('PASS: selected degree-six interpolation checks of full cubic flux')
    print('PASS: Jlow\'\' = -1792/425*k³*A⁵ + 1148/5*nu*k⁴*A⁴ + 512*nu²*k⁵*A³')
    print('PASS: Jhigh\'\' = -615688/12325*k³*A⁵ - 728/5*nu*k⁴*A⁴ + 1024*nu²*k⁵*A³')
    print('PASS: at A=10*nu*k, high outward flux initially rises but bends down')

if __name__ == '__main__':
    run()

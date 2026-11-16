#!/usr/bin/env python3
"""Exact full-mode Navier--Stokes derivative of two outward energy fluxes.

The six-mode periodic initial state is NOT truncated after t=0. All first
nonzero generated modes and all Q'(0) ordered convolutions are included.
Arithmetic is entirely exact Gaussian-rational; no floating-point tolerance.
"""
from fractions import Fraction as Q
import check_h3_three_band_leray_symbol as old

ZERO = old.z()
VZERO = (ZERO, ZERO, ZERO)


def vadd(x, y):
    return old.vector_add(x, y)


def vscale(x, y):
    return old.vector_scale(x, y)


def norm2(k):
    return sum(x * x for x in k)


def inner_real(x, y):
    out = old.dot_complex_complex(tuple(old.zconj(z) for z in x), y)
    assert out[1] == 0, (x, y, out)
    return out[0]


def full_ordered_leray(k, x, y):
    """-i P_k sum_{p+q=k} (q·x_p)y_q, with x,y distinct if needed."""
    assert norm2(k) > 0
    result = VZERO
    for p, xp in x.items():
        yq = y.get(old.subtract_modes(k, p))
        if yq is None:
            continue
        q = old.subtract_modes(k, p)
        contraction = old.dot_real_complex(q, xp)
        term = tuple(old.zminus_i(old.zmul(contraction, z)) for z in yq)
        result = vadd(result, term)
    return old.leray(k, result)


def quadratic(x):
    sums = {old.add_modes(p, q) for p in x for q in x}
    return {k: full_ordered_leray(k, x, x)
            for k in sums if k != (0, 0, 0)}


def make_initial(k, A):
    a, b, c = (k, 0, 0), (2 * k, k, 0), (3 * k, k, 0)
    polar = {
        a: ((0, 1, -1), False),
        b: ((-1, 2, 1), False),
        c: ((0, 0, -1), True),
    }
    u = {}
    for mode, (coeff, imaginary) in polar.items():
        val = tuple(old.z(0, A * x) if imaginary else old.z(A * x)
                    for x in coeff)
        u[mode] = val
        u[old.neg_mode(mode)] = tuple(old.zconj(x) for x in val)
        assert old.dot_real_complex(mode, val) == ZERO
    return u


def first_derivative(u, nu, q):
    """The genuine PDE right-hand side Q(u) - nu |k|^2 u_k."""
    result = {}
    for k in q.keys() | u.keys():
        dv = vadd(q.get(k, VZERO), vscale(-nu * norm2(k), u.get(k, VZERO)))
        if dv != VZERO:
            result[k] = dv
        assert old.dot_real_complex(k, dv) == ZERO
    return result


def quadratic_derivative(u, du):
    """Full product rule, including modes not in the initial support."""
    sums = {old.add_modes(p, q) for p in du for q in u}
    sums.update(old.add_modes(p, q) for p in u for q in du)
    return {k: vadd(full_ordered_leray(k, du, u),
                    full_ordered_leray(k, u, du))
            for k in sums if k != (0, 0, 0)}


def work_and_derivative(u, q, du, dq, k):
    w = inner_real(u.get(k, VZERO), q.get(k, VZERO))
    dw = (inner_real(du.get(k, VZERO), q.get(k, VZERO)) +
          inner_real(u.get(k, VZERO), dq.get(k, VZERO)))
    return w, dw


def cutoff_fluxes(k, u, q, du, dq):
    """J_low=-sum_{|n|<3k/2} work; J_high=sum_{|n|>3k} work."""
    terms = {p: work_and_derivative(u, q, du, dq, p)
             for p in u.keys() | q.keys()}
    low = [value for p, value in terms.items()
           if 4 * norm2(p) < 9 * k * k]
    high = [value for p, value in terms.items()
            if norm2(p) > 9 * k * k]
    return ((-sum(w for w, _ in low), -sum(dw for _, dw in low)),
            (sum(w for w, _ in high), sum(dw for _, dw in high)),
            terms)


def direct_flux_at_state(k, u):
    """Full cubic flux polynomial, for independent finite-difference audit."""
    q = quadratic(u)
    lo = sum(inner_real(v, q.get(p, VZERO))
             for p, v in u.items() if 4 * norm2(p) < 9 * k * k)
    hi = sum(inner_real(v, q.get(p, VZERO))
             for p, v in u.items() if norm2(p) > 9 * k * k)
    return -lo, hi


def cubic_interpolation_slope(k, u, du):
    """Since J(u+t du) is cubic, this extracts the derivative exactly."""
    def at(t):
        state = {p: vadd(u.get(p, VZERO), vscale(t, du.get(p, VZERO)))
                 for p in u.keys() | du.keys()}
        state = {p: v for p, v in state.items() if v != VZERO}
        return direct_flux_at_state(k, state)
    p, n, p2, n2 = at(Q(1)), at(Q(-1)), at(Q(2)), at(Q(-2))
    return tuple((8 * (x-y) - (z-w)) / 12
                 for x, y, z, w in zip(p, n, p2, n2))


def run():
    old.main()
    checked = 0
    for k in (Q(1), Q(2), Q(7)):
        for nu in (Q(0), Q(1, 2), Q(3)):
            for A in (Q(1), Q(6) * (nu + 1) * k, Q(10) * (nu + 1) * k):
                u = make_initial(k, A)
                q = quadratic(u)
                du = first_derivative(u, nu, q)
                dq = quadratic_derivative(u, du)
                low, high, terms = cutoff_fluxes(k, u, q, du, dq)

                # Exact three newly created positive-frequency modes. Other
                # candidate sums (including self-interactions) vanish.
                expected_new = {
                    (k, k, 0): (old.z(0, 2 * k * A*A),
                                old.z(0, -2 * k * A*A), ZERO),
                    (4*k, k, 0): (ZERO, ZERO, old.z(-k * A*A)),
                    (5*k, 2*k, 0): (ZERO, ZERO, old.z(k * A*A)),
                }
                actual_new = {mode: val for mode, val in q.items()
                              if mode not in u and val != VZERO}
                assert set(actual_new) == (set(expected_new) |
                                           {old.neg_mode(p) for p in expected_new})
                for mode, val in expected_new.items():
                    assert actual_new[mode] == val, (k, A, mode, val, actual_new[mode])
                    assert actual_new[old.neg_mode(mode)] == tuple(old.zconj(x) for x in val)

                # These sums are pair-kinetic second-order coefficients:
                # 1/2*(|u_k|²+|u_-k|²) = t² * |u'_k(0)|² + o(t²).
                pair_leak = sum(sum(inner_real((z,), (z,)) for z in vec)
                                for vec in expected_new.values())
                outer_leak = sum(sum(inner_real((z,), (z,)) for z in expected_new[p])
                                 for p in ((4*k,k,0), (5*k,2*k,0)))
                assert pair_leak == 10*k*k*A**4
                assert outer_leak == 2*k*k*A**4

                # Hermitian work cancellation includes the generated modes.
                assert all(terms[p][0] == terms[old.neg_mode(p)][0]
                           and terms[p][1] == terms[old.neg_mode(p)][1]
                           for p in terms)
                assert sum(v[0] for v in terms.values()) == 0
                assert sum(v[1] for v in terms.values()) == 0

                assert low == (2*k*A**3,
                               -Q(46,5)*k*k*A**4 - 32*nu*k**3*A**3)
                assert high == (4*k*A**3,
                                Q(36,5)*k*k*A**4 - 64*nu*k**3*A**3)
                if nu > 0:
                    assert (high[1]>0) == (A>Q(80,9)*nu*k)
                if k == 1 and A == 1 and nu in (Q(0), Q(3)):
                    # Check derivative a SECOND way by exact polynomial
                    # interpolation, not by differentiating the convolution.
                    assert cubic_interpolation_slope(k, u, du) == (low[1], high[1])
                checked += 1
    print(f'PASS: {checked} exact full-convolution and derivative cases')
    print('PASS: newly generated projected squared amplitudes (8, 1, 1)')
    print('PASS: quadratic pair leakage = 10*k²*A⁴; outer leakage = 2*k²*A⁴')
    print('PASS: dJ_low = -46/5*k²*A⁴ - 32*nu*k³*A³')
    print('PASS: dJ_high = 36/5*k²*A⁴ - 64*nu*k³*A³')
    print('PASS: dJ_high>0 iff A>(80/9)*nu*k')
    print('PASS: independent cubic-polynomial interpolation checks')


if __name__ == '__main__':
    run()

#!/usr/bin/env python3
"""Independent exact arithmetic checks for three-band Wiener persistence.

This checks the published constants against the genuine six-mode convolution,
first-jet interpolation, and integral-power Wiener inequalities. It is NOT
an infinite-dimensional PDE proof: the analytic Wiener bootstrap is supplied
by a separate mathematical argument, not by this finite audit.
"""
from fractions import Fraction as F
import check_h3_three_band_flux_slope as old

M = F(100)
MU_MAX = F(1, 10)
TAU_MAX = F(1, 10**11)


def difference_cap(mu, tau):
    return (5*M*M+100*mu*M)*tau


def flux_cap(mu, tau):
    return 12*M*M*difference_cap(mu, tau)


def scalar_analytic_inequalities():
    # Exponential weights: for each integer m >= 0,
    # m*(5/4)^m <= 5*(3/2)^m;
    # m²*(5/4)^m <= 100*(3/2)^m;
    # m <= 4*(5/4)^m.
    # Their ALL-m proofs are by Bernoulli/binomial bounds (research note).
    for n in range(0, 1025):
        assert n * F(5,4)**n <= 5 * F(3,2)**n
        assert n*n * F(5,4)**n <= 100 * F(3,2)**n
        assert F(n) <= 4 * F(5,4)**n

    # All six real-conjugate modes: |a|_1=1, |b|_1=3, |c|_1=4.
    # Euclidean amplitude bounds |A|<2, |B|<3, |C|=1.
    w2_upper = 2 * (2*2 + 8*3 + 16*1)
    assert w2_upper == 88 and w2_upper < M

    for mu in (F(0), F(1,100), F(1,10)):
        for tau in (F(0), TAU_MAX/2, TAU_MAX):
            assert 2*(1-M*tau) >= F(3,2)
            assert difference_cap(mu, tau) <= 51000*tau
            assert flux_cap(mu, tau) <= 6120000000*tau
            assert flux_cap(mu, tau) < F(1,10)
            assert 2-flux_cap(mu, tau) > F(19,10)
            assert 4-flux_cap(mu, tau) > F(39,10)
    assert flux_cap(MU_MAX, TAU_MAX) == F(612,10000)


def full_symbol_and_jet_checks():
    old.old.main()
    # Reuse the committed *full ordered convolution*, not a six-mode closure.
    for mu in (F(0), F(1,100), F(1,10)):
        u = old.make_initial(F(1), F(1))
        q = old.quadratic(u)
        du = old.first_derivative(u, mu, q)
        dq = old.quadratic_derivative(u, du)
        low, high, _ = old.cutoff_fluxes(F(1), u, q, du, dq)
        assert (low[0], high[0]) == (2, 4)
        for tau in (TAU_MAX/2, TAU_MAX):
            # This is only the first PDE jet; the Wiener argument, rather
            # than a truncated Taylor series, covers the full time window.
            pair = old.direct_flux_at_state(
                F(1), {n: old.vadd(u.get(n, old.VZERO),
                          old.vscale(tau, du.get(n,old.VZERO)))
                      for n in set(u)|set(du)})
            assert abs(pair[0]-2) < flux_cap(mu,tau)
            assert abs(pair[1]-4) < flux_cap(mu,tau)


def run():
    scalar_analytic_inequalities()
    full_symbol_and_jet_checks()
    print('PASS: integer weighted Wiener inequalities tested through degree 1024')
    print('PASS: initial six-mode W_2 norm < 88 < 100')
    print('PASS: 0<=mu<=1/10, tau<=10^-11 gives radius >= 3/2')
    print('PASS: difference cap <= 51000*tau; flux cap <= 6120000000*tau')
    print('PASS: endpoint flux cap = 0.0612 < 0.1')
    print('PASS: full-convolution six-mode first-jet fluxes remain within cap')
    print('NOTE: the infinite Fourier PDE analytic estimate is a separate proof obligation')


if __name__ == '__main__':
    run()

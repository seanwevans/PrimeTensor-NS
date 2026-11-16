#!/usr/bin/env python3
"""Exact analytic-Wiener integer-envelope and viscous-payment audit.

Proves the induction constants by rational algebra and tests actual six-mode
physical Fourier data using the project's existing full-convolution checker.
This checker DOES NOT replace the unformalized full Navier--Stokes Wiener PDE
construction; the new Lean theorem covers all n and all finite index sets.
"""
from fractions import Fraction as F
import check_h3_three_band_flux_slope as earlier

A, B = F(5, 4), F(3, 2)
TMAX = F(1, 10**11)


def verify_induction_certificate():
    # For a_n = (5/4)^n, b_n = (3/2)^n, assume:
    # a_n<=b_n, n*a_n<=5*b_n, n^2*a_n<=100*b_n.
    # Then by algebra and nonnegativity, the successor bounds follow from:
    assert A <= B
    assert A * (5 + 1) <= 5 * B
    assert A * (100 + 2 * 5 + 1) <= 100 * B
    # For n<=4*(5/4)^n, (n+1)<=4*a_n+1<=5*a_n=4*a_(n+1).
    assert 4 * A == 5
    for n in range(200):
        assert A**n <= B**n
        assert n * A**n <= 5 * B**n
        assert n * n * A**n <= 100 * B**n
        assert n <= 4 * A**n
    print('PASS: all-degree induction coefficients certified exactly')


def verify_all_mode_original_fourier_data():
    old = earlier.old
    old.main()
    u = earlier.make_initial(F(1), F(1))
    # Exact squared amplitudes of the *real* six-mode datum.
    norms2 = {k: sum(old.zmul(v, old.zconj(v))[0] for v in vec)
              for k, vec in u.items()}
    assert len(u) == 6
    assert sorted(norms2.values()) == [1, 1, 2, 2, 6, 6]
    initial_gradient_sq = sum(earlier.norm2(k) * n2
                              for k, n2 in norms2.items())
    assert initial_gradient_sq == 84
    degree = lambda n: sum(abs(x) for x in n)
    # Rational upper bounds on Euclidean magnitudes: 2, 3, 1.
    amp_bound = {k: {1: 1, 2: 2, 6: 3}[norms2[k]] for k in u}
    weighted = sum(A**degree(k) * amp_bound[k] for k in u)
    assert weighted == 2*(2*A + 3*A**3 + A**4)
    assert weighted < 100
    grad1 = sum(degree(k)*amp_bound[k] for k in u)
    assert grad1 <= 4 * weighted
    grad2 = sum((degree(k)*amp_bound[k])**2 for k in u)
    assert grad2 <= grad1**2 <= (4*weighted)**2 <= 160000
    q = earlier.quadratic(u)
    du = earlier.first_derivative(u, F(1, 10**7), q)
    dq = earlier.quadratic_derivative(u, du)
    low, high, _ = earlier.cutoff_fluxes(F(1),u,q,du,dq)
    assert low[0] == 2 and high[0] == 4
    print('PASS: genuine six-mode gradient energy is 84, W_(5/4)<100')


def verify_payment_separation():
    for eps in (F(1), F(1,10), F(1,10**3), F(1,10**8)):
        mu = min(F(1, 10), eps/F(100000))/2
        for T in (TMAX/2, TMAX):
            assert 0 < mu <= F(1,10)
            assert mu <= eps/F(100000)
            viscous_ceiling = 160000*mu*T
            lower_outward_transfer = F(19,10)*T
            upper_outward_transfer = F(39,10)*T
            assert viscous_ceiling <= eps*lower_outward_transfer
            assert viscous_ceiling <= eps*upper_outward_transfer
            # This comparison requires the previous analytic PDE bridge.
            # Here only its exact scalar consequences are checked.
            assert 160000*mu*T <= F(8,5)*eps*T
    print('PASS: arbitrary epsilon separates kinetic viscous charge from outward flux')


def run():
    verify_induction_certificate()
    verify_all_mode_original_fourier_data()
    verify_payment_separation()
    print('NOTE: actual PDE existence and W_R bootstrap remain a distinct Lean obligation')


if __name__ == '__main__':
    run()

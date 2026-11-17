#!/usr/bin/env python3
"""Independent complex-Leray moving analytic-ball persistence numerical audit.

RK4 integrates the actual finite Galerkin ODE, including zero coefficients and
all ordered-pair output collisions. It checks the smooth moving Wiener
inequality, positive-radius duration, and the finite-cutoff epsilon budget.
The comparison theorem is proved in Lean, not by these numerical tests.
"""
from math import exp, log
from random import Random
import check_h3_three_band_z3_galerkin_ode_to_duhamel as ode
import check_h3_three_band_z3_galerkin_zero_safe_moving_wiener as smooth


def check():
    rng = Random(112726)
    pool = [(i, j, k) for i in range(-2, 3) for j in range(-2, 3) for k in range(-2, 3)]
    window = log(10 / 9) / 100
    total = 0
    zero = 0
    generated = 0
    max_smooth = 0.
    for size in (3, 5, 8, 11):
        for case in range(12):
            s = rng.sample(pool, size)
            out = tuple(s[0][j] + s[1][j] for j in range(3))
            if out not in s:
                s[-1] = out
            if len(set(s)) != len(s):
                raise AssertionError('duplicate output')
            U = {n: tuple(complex(rng.uniform(-1, 1), rng.uniform(-1, 1))
                          for _ in range(3)) for n in s}
            for j, n in enumerate(s):
                if (j + case) % 5 == 0:
                    U[n] = (0j, 0j, 0j)
                    zero += 1
            initial = smooth.true_mass(s, U, log(2))
            target = (48., 78., 95., 99.0)[case % 4]
            if initial == 0:
                raise AssertionError('all zero inputs')
            factor = target / initial
            U = {n: tuple(factor * z for z in U[n]) for n in s}
            W0 = smooth.true_mass(s, U, log(2))
            assert W0 < 100 and abs(W0 - target) < 1e-9
            E = sum(smooth.weight(log(2), n) for n in s)
            eps = (100 - W0) / (2 * (E + 1))
            assert eps > 0
            assert eps * E <= 100 - W0
            M0 = smooth.smooth_mass(s, U, log(2), eps)
            assert M0 <= 100 + 1e-8
            mu = (0., 0.001, 0.05, 0.1)[case % 4]
            h = window * 0.45
            steps = 60
            for k in range(steps + 1):
                t = h * k / steps
                r = log(2) - 100 * t
                assert r >= log(9 / 5)
                M = smooth.smooth_mass(s, U, r, eps)
                D = smooth.smooth_derivative(s, U, r, eps)
                assert M <= 100 + 1e-5, (size, case, k, M)
                assert M <= M0 + 1e-5, (size, case, k, M, M0)
                exact = ode.make_ode(mu, s, U)
                src = ode.complex_source(s, U)
                deriv = sum(
                    smooth.weight(r, n) * (
                        -100 * smooth.degree(n) * smooth.amplitude(U[n], eps)
                        + smooth.inner(U[n], exact[n]) / smooth.amplitude(U[n], eps)
                    ) for n in s
                )
                assert deriv <= (M - 100) * D + 2e-8
                if k < steps:
                    U = ode.rk4(mu, s, U, h / steps)
            outputs = {tuple(p[j] + q[j] for j in range(3)) for p in s for q in s}
            generated += len(outputs - set(s))
            max_smooth = max(max_smooth, M0)
            total += 1
    assert generated > 0 and zero > 0
    print(f'PASS: {total} actual finite complex-Leray Galerkin ODE moving-ball cases')
    print(f'PASS: {zero} exact zero-coefficient input modes; {generated} generated output modes')
    print(f'PASS: smooth derivative inequality, regularization budget, and radius window')
    print(f'PASS: smoothed and true analytic masses stayed within the 100-ball; max initial {max_smooth:.8f}')
    print('NOTE: numerical RK4 is not a proof of ODE existence or a Galerkin limit')


if __name__ == '__main__':
    check()

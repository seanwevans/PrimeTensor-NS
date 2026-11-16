#!/usr/bin/env python3
"""Independent exact six-mode Leray-viscosity scaling test for the new module.

Reuses the prior exact Gaussian-rational ordered-convolution implementation,
not the new Lean algebraic formulas. Checks actual modal work for all six
frequencies at multiple rescaled wavevectors and amplitudes.
"""
from fractions import Fraction as Q
import check_h3_three_band_leray_symbol as old


def make_state(scale, amplitude):
    a, b, c = (1, 0, 0), (2, 1, 0), (3, 1, 0)
    A, B, C = (0, 1, -1), (-1, 2, 1), (0, 0, -1)
    modes = {}
    for k, polar, imaginary in ((a, A, False), (b, B, False), (c, C, True)):
        key = tuple(scale * x for x in k)
        value = tuple(old.z(0, amplitude * x) if imaginary else
                      old.z(amplitude * x) for x in polar)
        modes[key] = value
        modes[old.neg_mode(key)] = tuple(old.zconj(v) for v in value)
    return modes


def square(v):
    return sum(x*x for x in v)


def run_test():
    old.main()
    for scale in (Q(1), Q(2), Q(7)):
        a = (scale, Q(0), Q(0))
        b = (2*scale, scale, Q(0))
        c = (3*scale, scale, Q(0))
        for nu in (Q(1, 2), Q(1), Q(3)):
            for factor in (Q(4), Q(5), Q(6)):
                amp = factor * nu * scale
                u = make_state(scale, amp)
                works = tuple(old.modal_work(k, u) for k in (a, b, c))
                expected = (-scale * amp**3, -scale * amp**3,
                            2 * scale * amp**3)
                assert works == expected, (scale, nu, amp, works)
                assert sum(works) == 0
                for k in (a, b, c):
                    assert old.modal_work(old.neg_mode(k), u) == old.modal_work(k, u)
                assert -works[0] > 0 and works[2] > 0
                high_amp_sq = sum(old.zmul(v, old.zconj(v))[0] for v in u[c])
                assert high_amp_sq == amp**2
                viscous = nu * square(c) * high_amp_sq
                assert viscous == 10 * nu * scale**2 * amp**2
                net = works[2] - viscous
                assert net == 2 * scale * amp**2 * (amp - 5 * nu * scale)
                assert (net > 0) == (factor > 5)
                assert (net == 0) == (factor == 5)
                assert 2*net == 4 * scale * amp**2 * (amp-5*nu*scale)
    print('PASS: 27 full-six-mode rescaled Navier-Stokes convolution/viscosity tests')
    print('PASS: high-mode net work has exact threshold amplitude > 5*nu*scale')
    print('PASS: both nonlinear outward fluxes persist at every tested scale')


if __name__ == '__main__':
    run_test()

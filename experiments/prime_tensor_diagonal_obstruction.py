#!/usr/bin/env python3
"""
PrimeTensor same-depth diagonal obstruction probe.

Take continued-fraction convergents u/v -> log(3)/log(2), so

    a_n = 2^u / 3^v -> 1.

For the intended coupling,

    log C(a_n, a_n) = (u log 2 - v log 3)^2 -> 0.

But the current finite-stage atomic dyadic kernel uses

    Q_pq(n) = floor(exp(log p log q) * 2^n) / 2^n,

and the same-depth diagonal on a_n has log-value

    u^2 log Q_22 + v^2 log Q_33 - 2uv log Q_23.

The exponents can amplify O(2^-n) atomic floor errors much faster than the
external depth increases.  This script uses arbitrary precision arithmetic so
the effect is not a floating-point artifact.
"""

import mpmath as mp

mp.mp.dps = 180

LN2 = mp.log(2)
LN3 = mp.log(3)
ALPHA = LN3 / LN2

T22 = mp.exp(LN2 * LN2)
T23 = mp.exp(LN2 * LN3)
T33 = mp.exp(LN3 * LN3)


def convergents(x, count=40):
    y = mp.mpf(x)
    coeffs = []
    for _ in range(count):
        a = int(mp.floor(y))
        coeffs.append(a)
        frac = y - a
        if frac == 0:
            break
        y = 1 / frac

    p0, p1 = 0, 1
    q0, q1 = 1, 0
    out = []
    for a in coeffs:
        p = a * p1 + p0
        q = a * q1 + q0
        out.append((p, q))
        p0, p1 = p1, p
        q0, q1 = q1, q
    return out


def lower_dyadic(target, precision):
    D = mp.mpf(2) ** precision
    return mp.floor(target * D) / D


def approximate_diagonal_log(precision, u, v):
    q22 = lower_dyadic(T22, precision)
    q23 = lower_dyadic(T23, precision)
    q33 = lower_dyadic(T33, precision)
    return (
        mp.mpf(u) ** 2 * mp.log(q22)
        + mp.mpf(v) ** 2 * mp.log(q33)
        - 2 * mp.mpf(u) * mp.mpf(v) * mp.log(q23)
    )


def fmt(x, digits=10):
    return mp.nstr(x, digits)


def main():
    conv = convergents(ALPHA, 45)

    print("PrimeTensor same-depth diagonal obstruction probe")
    print("=" * 68)
    print("a_n = 2^u / 3^v using u/v convergents to log(3)/log(2)")
    print()
    print(
        f"{'depth':>5} {'u':>16} {'v':>16} "
        f"{'log(a_n)':>15} {'true log C':>15} {'sampled log C':>18}"
    )
    print("-" * 92)

    for depth in range(8, min(25, len(conv))):
        u, v = conv[depth]
        input_log = mp.mpf(u) * LN2 - mp.mpf(v) * LN3
        true_output_log = input_log * input_log
        sampled_output_log = approximate_diagonal_log(depth, u, v)

        print(
            f"{depth:5d} {u:16d} {v:16d} "
            f"{fmt(input_log, 7):>15} "
            f"{fmt(true_output_log, 7):>15} "
            f"{fmt(sampled_output_log, 10):>18}"
        )

    print()
    print("Interpretation:")
    print("  log(a_n) -> 0, so a_n -> 1 multiplicatively.")
    print("  The intended coupling also tends to 1 because true log C -> 0.")
    print("  The same-depth sampled kernel does not: atomic floor errors are")
    print("  multiplied by u^2, uv, and v^2 before the external depth catches up.")
    print()
    print("This diagnoses a precision-scheduling defect, not a defect in the")
    print("finite coupling target itself.")


if __name__ == "__main__":
    main()

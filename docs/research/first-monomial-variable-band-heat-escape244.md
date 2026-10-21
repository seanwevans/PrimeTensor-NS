# Arbitrarily strong normalized pure heat concentration in a two-band spectral model

Base commit: `072d6b06` — identify exact global heat barycenter and two-band sign obstruction.

For two nonnegative frequency masses `x` at radial weight `q=1` and `y` at `q=r`, the six moments are `m_k = x + r^k y`. In particular the previously formalized physical heat barycenter imbalance factors as

    I = xy (r−1)^3 (r+1)^2 (x−r²y).

For `r>1` and strictly positive masses, `I>0` precisely when `x>r²y`, and `I<0` precisely when `x<r²y`. The exact algebraic normalized heat rate equals

    B = 2 (x+r²y) I / ((x+y)(x+r⁴y))².

Take `x=r⁴`, `y=1`. Elementary polynomial cancellation (when `r≥2`) gives

    B(r) = (r−1)^4 (r+1)^3 (r²+1) / (2(r⁴+1)²).

The formal lower bound `B(r)≥r/128` for `r≥2` implies **no universal numerical upper bound** on normalized pure heat concentration in this algebraic spectral class.

By homogeneity of the rate in the two band masses, the same values are obtained after dividing both masses by `r⁴`: `x=1, y=r⁻⁴`. Then `m0=1+r⁻⁴`, `m2=1+r⁻²`, `m4=2`. The first and second are bounded between one and two, and the fourth is fixed, while `m5=1+r` grows without bound. This demonstrates why bounds on `E0`, `E2`, and `D3` alone do not bound the rate or the fifth moment. The Lean package formalizes the bounded low moments and unbounded *unscaled* rate; the rescaling is algebraic and not used to assert a smooth NS solution.

## Scope / mathematical audit

These are **two-band algebraic spectral models**, not actual Navier–Stokes trajectories. The earlier `GlobalHeatBarycenterSign244` theorem identifies the same exact six-moment expression for a strict-time physical H³ path, but the two-band examples do not prove realizability with a divergence-free smooth field or satisfy full nonlinear dynamics. Thus they negate a universal scalar-moment sign or ceiling argument, **not** the possibility of cancellation special to nonlinear NS solutions.

The next useful question is a structural signed inequality binding nonlinear `E₂′`, `D₃′`, and the high-frequency heat gain, rather than assuming the latter is uniformly bounded.

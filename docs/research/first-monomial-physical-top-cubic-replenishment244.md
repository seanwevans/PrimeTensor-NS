# Physical top-dissipation replenishment is paid by cubic forcing

Base commit: `8a3fd6d8` — prove physical top log replenishment and near-Young variation burden.

## The exact PDE identity

The existing strong fourth-radial Hilbert evolution and its complete signed
Fourier square completion give, at each strict physical time,

    D3' + M5 + P = M3,   M5 >= 0,   P >= 0,   M3 >= 0.

Here `D3` is the *physical* fourth-radial dissipation mass, `M5` is the
unrestricted fifth velocity moment, `M3` is the already-built cubic weighted
Leray forcing-square mass, and `P` is the genuine signed phase-mismatch square
remainder. Nothing is replaced by an independently assumed forcing scalar.

Thus positive top logarithmic replenishment has the exact identity

    (D3')_+ / D3 = (M3-M5-P)_+ / D3 <= M3 / D3.

At any strict time where `M3 <= M5+P`, positive logarithmic replenishment is
**zero**. Strict positive growth requires `M3 > M5+P`; the phase penalty
opposes top-mass replenishment even though it contributes positively in the
separate variance-production decomposition.

## Integrated near-Young obstruction

For `s<t` inside the physical preterminal H3 energy class and positive
`E0,D3` throughout, the existing integrated concentration and top-variation
theorems, combined with the new forcing inequality, prove

    R(s) - 256 δ/(27 K^4 E0(t))
      - [log E0(s) - log E0(t)]
      - 36 integral_s^t C1 sqrt(E_H3(r)) dr
      - [log D3(s) - log D3(t)]
    <= integral_s^t M3(r)/D3(r) dr.

The `M3/D3` profile has a zero extension off the strict energy-class tail.
All relevant `IntervalIntegrable` conditions remain explicit; particularly,
compact differentiability alone is never presented as proof of time-
integrability of the cubic forcing ratio.

This is an *obstruction*, not a bound on the terminal forcing integral. The
open analytic question is how to control that normalized cubic action from the
exact physical PDE, the kinetic/enstrophy clocks, and the radial forcing
hierarchies. No global Navier–Stokes regularity is claimed.

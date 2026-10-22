# Physical kinetic logarithmic action and integrated signed top-phase budget

Base checkpoint: `b0bcac21`, compact H³ gradient action for normalized order-two transport.

## Closed PDE kinetic law

The canonical order-zero derivative identity, physical momentum PDE split, order-zero pressure cancellation and order-zero transport flux cancellation combine to give, at every strict energy-class time,

    E0' = L0 = -2 D0.

For E0>0 the scalar log-loss primitive `-log E0` has derivative `-L0/E0 = 2D0/E0`. On a compact interval with integrable normalized kinetic loss, the fundamental theorem of calculus gives

    integral_s^t [-L0/E0] = log E0(s) - log E0(t).

Integrability of this normalized derivative is an **explicit hypothesis**. This result is not claiming automatic integrability of an arbitrary derivative merely from differentiability. For a strictly positive kinetic energy, the formula can also be expressed `log (E0(s)/E0(t))`.

## Signed middle/top fifth phase

The previously verified exact physical normalized concentration source splits as

    X/A² = Middle + TopPhase,     A=E0 D3.

    Middle = [2E2(L2 - T2) A - E2² L0 D3]/A².

    TopPhase = E2² E0 (M5 + P - M3)/A².

`M5` is the fifth radial velocity mass, `P>=0` is the exact positive signed velocity–forcing phase mismatch, and `M3` is the cubic Leray forcing mass. The positive sign of P in normalized concentration production is important: it does **not** oppose concentration. The top expression retains rather than discards the genuine phase.

The previously proved pointwise middle estimate gives

    Middle <= -L0/E0 + 36 C1 sqrt(E_H3).

Compact-time integrability of the last gradient envelope follows from the energy-class regularity (previous checkpoint). Given explicitly interval-integrable derivative, middle, top and kinetic loss profiles, this yields the quantitative physical action barrier

    integral_s^t TopPhase
      >= R(s)-R(t) - [log E0(s)-log E0(t)]
           -36 integral_s^t C1 sqrt(E_H3).

Near-Young terminal samples replace `R(t)` by the established bound `256 δ/(27 K⁴ E0(t))`.

## Frontier

The new result removes abstract budget constants for BOTH the order-two transport and kinetic-loss contributions. It does not prove an unconditional estimate on the remaining signed weighted moment `M5+P-M3`, or temporal integrability of all normalized sources up to a singular endpoint. The next meaningful step is to turn the top-phase action into a testable signed mass/phase-defect obstruction and examine whether the *actual PDE* can meet its necessary quantitative threshold.

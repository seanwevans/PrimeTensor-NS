# Physical compact-time integrated order-two gradient allowance

Base checkpoint: `0eccaf93` — conditional integrated physical heat / order-two transport / Leray signed budget.

## New unconditional piece of the compact-time analysis

The already-proved strict H³ energy-class continuity of `velocityH3EnergyAt` implies the canonical envelope

    h(t) = C1 * sqrt(velocityH3EnergyAt u t)

is continuous on the entire strict energy-class interval `(a,T)` and, in particular, interval-integrable on every compact `[s,t]` with `a<s<=t<T`. This is a genuine **automatic compact-time integrability fact**. It is not integrability on the full terminal interval `(a,T)`.

The existing physical commutator theorem gives, pointwise wherever kinetic and third-order dissipation masses are positive,

    OrderTwoNormalizedRate(t) <= 36 h(t).

If the *actual* signed normalized order-two profile is interval-integrable, comparison yields

    integral(s,t) OrderTwoNormalizedRate <= 36 integral(s,t) h.

The exact three-channel physical concentration balance of the preceding checkpoint then implies

    R(s)-R(t) - 36 integral(s,t) h
      <= integral(s,t) Heat + integral(s,t) Leray.

A near-Young endpoint sample with gap upper bound `256 δ/(27 K^4 E0(t))` therefore forces the same lower bound after replacing `R(t)` by that upper bound. Under a separately supplied physical signed heat-action ceiling `H`, the Leray action must pay at least

    R(s) - 256 δ/(27 K^4 E0(t)) - H - 36 integral(s,t) h.

## What remains open

The three-channel FTC still explicitly requires integrability of the normalized variance derivative and individual heat, order-two, and Leray profiles. The pointwise commutator bound does not by itself prove temporal measurability of the normalized order-two profile. The signed physical heat action has no established uniform ceiling, as shown by the separate two-band scalar spectral obstruction. The terminal `sqrt(H3)`-envelope action can itself diverge; compact integrability is not a terminal estimate. Nothing here proves smooth continuation.

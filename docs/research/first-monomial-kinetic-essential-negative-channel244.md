# Kinetic-anchored essential negative signed H³ channel (244)

Checkpoint: `7efeabaf` — kinetic-anchored fixed negative signed H³ cubic channel.

## Mathematical content

Let `E(t) ≥ 1` be the physical normalized H³ energy, `D(t) ≥ 0` its full
viscous dissipation, `G₃(t)` the 972-term canonical signed physical-gradient
cubic, and `M₃(t)` the 243-slot canonical signed interpolation cubic.

The pre-existing post-anchor Young estimate is

    E' + D ≤ 3 C₁ sqrt(E) E₀(b) + 441 C₁² E₀(b) E - (G₃ + 3 M₃).

Since `sqrt(E) ≤ E`, set the **fixed** kinetic-anchor constant

    K(b) = (3 C₁ + 441 C₁²) E₀(b).

Define two *genuinely adverse* physical channel ratios:

    A_G = -(G₃ + D/2)/E,    A_I = -(3 M₃ + D/2)/E.

The existing physical-to-spectral equality gives

    E'/E ≤ K(b) + A_G + A_I.

With `U = max(0, E'/E - 4422)`, established to be measurable on the
energy-class tail, this yields

    U ≤ max(0, K(b) - 4422 + A_G + A_I).

Under hypothetical nonextension, `U` cannot be almost-everywhere dominated
by *any* integrable scalar envelope on *any* strict terminal subtail. If
both `A_G` and `A_I` admitted integrable almost-everywhere upper envelopes,
then an integrable envelope `|K-4422|+|r_G|+|r_I|` would dominate `U`, a
contradiction. The standard nested-tail finite selection fixes one channel,
independent of the choice of tail or integrable envelope.

No time-measurability of either spectral channel is assumed. This is a
necessary PDE-conditioned barrier in the nonextension branch; it neither
closes unconditional Navier–Stokes regularity nor asserts realization of
static Schwartz concentration profiles along a solution.

## Frontier

A genuine PDE-dependent a.e. integrable upper bound for the chosen
*dissipation-adjusted* adverse channel would contradict the obstruction.
The existing fixed-kinetic spatial counterexamples rule out obtaining such
a bound by unrestricted static coercivity alone.

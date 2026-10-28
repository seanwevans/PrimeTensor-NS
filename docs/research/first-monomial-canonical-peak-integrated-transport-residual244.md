# Canonical physical H³ source peak: integrated transport residual

Base: `d1feac25` — the pointwise viscous-or-signed-transport split at an intermediate mean-value time.

Let `A = ‖U₃(s)‖`, `E₃(t) = velocityH3EnergyAt u t`,
`D₃(t) = velocityH3DissipationAt u t`,
`Tr₃(t) = velocityH3TransportDerivativeAt u t`, and
`B = ∫_a^T D₃(t) dt < ∞`.

At the original canonical projected-source-maximizing peak `s`, the earlier clock forces either terminal compression, or an observation `r` with `s < r < T` and `‖U₃(r)‖ < A/2`. The exact three-component spectral energy comparison implies

    E₃(s) - E₃(r) > A²/4.

The true nonnegative physical viscous dissipation obeys, without another local-time estimate,

    ∫_s^r D₃(t) dt ≤ B.

Thus the exact integrated **residual**

    R(s,r) := E₃(s) - E₃(r) - 2 ∫_s^r D₃(t) dt

satisfies

    R(s,r) > A²/4 - 2B.

In particular if `A² ≥ 16B`, then `R(s,r) > A²/8 > 0`.
For the fixed finite `B`, the original canonical source-maximizing sequence has
`A_k → ∞` under the inherited **conditional** critical-width hypotheses;
hence the `A_k² ≥ 16B` threshold holds eventually. The canonical times and
annulus witnesses are not changed.

The physical exact PDE identity is

    E₃'(t) + 2D₃(t) = -Tr₃(t).

If the actual energy derivative and the physical signed transport are separately
interval-integrable on `[s,r]`, the FTC yields

    R(s,r) = ∫_s^r Tr₃(t) dt.

Those temporal integrability hypotheses are explicit in
`h3Path_physicalSignedTransportResidual_eq_integral244` and
`h3Path_physicalHalfLoss_positiveIntegratedTransport244` rather than
implicitly inferred from differentiability. Consequently the unconditional
theorem about `R` does **not** pretend to have proved temporal integrability
of `Tr₃` from the energy class alone.

## What this changes

The instantaneous viscous branch at the mean-value point can remain arbitrarily
large; finite ∫D does not control its pointwise height. But viscosity's *total*
contribution to the rapid H³ energy drop is at most `2B`. At a sufficiently
high canonical peak, the remaining energy loss must be assigned to the
positive signed transport expenditure on the interval, in the precise residual
sense above. If the local FTC conditions hold, it is literally the positive
time integral of the physical transport density.

This is a necessary condition for the noncompressed half-loss branch, not an
upper bound, a contradiction, or a Navier–Stokes regularity theorem.

Validation in this package: Python registrar syntax, theorem-name checks,
idempotence, and source linting. Lean elaboration/build are not available
inside the packaging environment; the supplied shell commands must be run
against the repository's pinned Mathlib toolchain.

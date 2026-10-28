# Automatic compact-time H³ transport integrability at canonical source peaks

Base commit: `3a6c69a7` (actual integrated energy residual beyond finite global viscous expenditure).

Previous bridge `h3Path_physicalSignedTransportResidual_eq_integral244` required independent temporal integrability of the actual H³ energy derivative and signed transport on `[s,r]`. Both are now derived from the existing strict preterminal energy class, its canonical continuous H³ energy, the physical Landau bound, and the already-assumed finite global viscous integral.

Define

    E(t)  = velocityH3EnergyAt u t,
    D(t)  = velocityH3DissipationAt u t >= 0,
    Tr(t) = velocityH3TransportDerivativeAt u t,
    C(t)  = 4422*(1+|h3PathCanonicalSqrtEnergyGradientEnvelope u t|),
    M(t)  = C(t)*E(t).

On every compact strict energy-class interval `[s,r]`, `E` and `M` are continuous. The full physical PDE balance and the previously proved commutator bound imply

    E'(t) + 2 D(t) = -Tr(t),
    |Tr(t)| <= M(t),
    E'(t) <= M(t) <= max_[s,r] M = K.

Mathlib's one-sided derivative integrability lemma, already implemented as `h3_scalar_signedRate_intervalIntegrable_of_upperDerivative244`, proves `E'` interval-integrable **without** continuity of its derivative. The global dissipation integral supplies local `D` integrability. The actual pointwise PDE identity

    Tr(t) = -E'(t) - 2D(t)

then proves interval-integrability of the real signed transport via `IntervalIntegrable.congr_uIoo`. There are no added local FTC or continuity assumptions.

Therefore, at every canonical peak half-loss interval satisfying `A² >= 16 B` with `B = ∫_a^T D`, the full signed transport integral obeys

    ∫_s^r Tr(t) dt = E(s) - E(r) - 2∫_s^r D(t) dt > A²/8.

The theorem `h3Path_noL2Trace_canonicalWidth_sourcePeakIntegratedTransport_automatic244` transports this to the **unchanged** original canonical source maximizers and annulus witnesses under the **same conditional** critical-width regime. The necessary alternative is terminal compression or positive actual signed transport time expenditure. It does not bound that integral from above and does not prove global smoothness.

Validation: static checks, registrar idempotence, and ZIP integrity. Lean compilation must be performed against the project toolchain in the user's repository.

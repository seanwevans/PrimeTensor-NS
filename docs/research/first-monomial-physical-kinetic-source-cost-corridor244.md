# Physical kinetic source cost and terminal dissipation corridor

Base commit: `85ad2d96` — identify physical momentum source pairing with exact kinetic dissipation.

The existing proof gives the *exact signed physical Hilbert pairing* on every
strict time `t ∈ (0,T)`:

    inner U(t) R(t) = -D0(t)

where `U` is the actual old physical L² velocity, `R` the canonical projected
physical momentum source, and `D0` the order-zero viscous dissipation.

The present patch derives eight statements. Cauchy–Schwarz yields

    D0(t) ≤ ‖U(t)‖₂ ‖R(t)‖₂ = √E0(t) ‖R(t)‖₂.

This is a **lower constraint on the size of the source for a given kinetic
dissipation**, not an upper bound for high-order nonlinear transport.

The exact kinetic balance and nonnegativity imply for any `0<s≤t<T`:

    2 ∫ₛᵗ D0(r) dr ≤ E0(s).

Therefore a uniform rate floor `κ ≤ D0(r)` on `[s,t]` obeys

    2 κ (t-s) ≤ E0(s).

If `E0(s) < 2 κ (t-s)`, some `r∈[s,t]` has `D0(r) < κ`. Choosing
`t=(s+T)/2` yields a concrete strict-terminal-midpoint witness whenever
`E0(s) < κ (T-s)`.

## What this does and does not show

The result rules out **persistent** excessive order-zero dissipation across a
specified time window. It does not exclude isolated dissipation spikes,
nonintegrable behavior of higher-order H³ transport, or a terminal singularity.
The order-zero kinetic energy can stay bounded while higher-order energies
escape; this patch makes no converse claim. Every estimate is relative to
`LoggedPreterminalH3PathAdmissible`, with all inherited curl weak-FTC and
selected evolution dependencies unchanged. There are no endpoint assumptions.

Build: `lake env lean PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticSourceCostCorridor244.lean`.

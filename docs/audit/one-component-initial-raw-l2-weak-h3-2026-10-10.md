# Initial physical raw L² trace closes the weak H³ correlation frontier

Parent checkpoint `7c9e1ad5` — one-sided initial energy/correlation.

## Analytic bridge

At each positive physical time, the canonical H³ weighted spectral encoder is
`W₃ * û` and the canonical deweighter recovers the physical zeroth-order Fourier
`L²` state, as `h3Audit_actualFullRawFourier_eq_physicalZeroJet` proves.

For a smooth compact H³-frequency test `G`, multiply the test by the real
positive polynomial weight `W₃`, obtaining a Schwartz Fourier `L²` test.
`h3Audit_inner_spectral_smoothCompact_eq_rawFourier_reweighted` identifies the
weighted and unweighted Hilbert pairings. Raw Fourier `L²` convergence
therefore gives weak H³ pairing convergence against every such compact test.

The already-available smooth compact density theorem plus the eventually
uniform H³ norm bound extends convergence to the fixed initial spectral state.
The uniform bound is **proved** from the assumed one-sided physical H³ energy
inequality. Summing all three correlation limits closes the lower-correlation
hypothesis of the parent audit and consequently yields the strong H³ right trace.

## New assumptions and remaining PDE frontier

`H3AuditInitialRightPhysicalRawL2AndEnergyUpper` assumes an initial right raw
Fourier `L²` trace for all three physical zeroth-order velocity components,
with the same proposed H³ initial datum, and an initial one-sided H³ energy
upper inequality. These are strictly more physically interpretable than assuming
weak H³ correlation. The raw Fourier premise is equivalent, by Plancherel,
to a physical velocity `L²` initial trace, but **its derivation from a
Navier–Stokes initial-value class is not yet supplied**.

The strong terminal vorticity endpoint and Liu–Zhang theorem are separate.
No `sorry`, `admit`, or new axioms were introduced. Local Lean compilation is
unavailable in this authoring environment.

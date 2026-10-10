# Initial H³ energy-class cover from genuine positive-time spatial smoothing

Parent checkpoint: `1e2e1596` (signed NS transport controls initial H³ growth).

The signed-transport closure consumed an abstract hypothesis:
`H3AuditInitialPositiveEnergyClassCover u T`, requiring an H³ energy class
whose start `a` precedes each positive time `s`.

This patch constructs each class by choosing `a = s/2`, using *one actual
Navier–Stokes pressure witness* and the explicit hypotheses:

- velocity: every strictly positive preterminal time has spatial C³
  regularity **after two further spatial derivatives** (the project's C⁵
  justification class);
- pressure: each strict positive preterminal time has spatial C³ regularity
  after one spatial derivative (the project's C⁴ justification class).

This establishes `PreterminalH3EnergyClass u (s/2) T` for every `s in (0,T)`.
The assumptions imply the initial cover, but are not claimed to follow
from the weaker `LoggedPreterminalH3PathAdmissible` predicate alone.

## Added public declarations

- `H3AuditInitialPositiveVelocitySpatialC5`
- `H3AuditInitialPositivePressureSpatialC4`
- `H3AuditInitialPositiveHighOrderClassicalNavierStokes`
- `h3Audit_initialPositiveHighOrderClassicalNS_energyClass_at`
- `h3Audit_initialPositiveHighOrderClassicalNS_energyClass_cover`
- `h3Audit_initialPositiveHighOrderClassicalNS_orderwiseDerivatives`
- `H3AuditInitialPhysicalSignedTransportSmoothData`
- `h3Audit_initialSignedTransportSmooth_implies_signedTransportData`
- `h3Audit_initialSignedTransportSmooth_implies_strongH3Trace`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialSignedTransportSmooth`

## Remaining analytic frontier

Parabolic positive-time smoothing sufficient for these high-order witnesses;
actual initial endpoint continuity, Bochner temporal source integrability and
bounds; one-sided signed H³ transport bound. The terminal strong vorticity
H³ endpoint is still a separate conditional premise. No `sorry`, `admit`, or
new axioms were added. Local Lean compilation not available.

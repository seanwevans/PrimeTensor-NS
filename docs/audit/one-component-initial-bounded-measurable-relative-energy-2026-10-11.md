# Initial relative-energy integrability from bounded measurable energy

Base checkpoint: `584304e7` — derive initial uniqueness without scalar energy continuity.

`OneComponentInitialBoundedMeasurableRelativeEnergy.lean` proves a
finite-measure `L^∞`-to-`L¹` implication for scalar energy on `(0,b)`, then
uses that proof to discharge the initial scalar `IntervalIntegrable` premise
of the existing no-continuity Gronwall interface.

New mathematical step:

- `h3Audit_initialBoundedMeasurableEnergy_intervalIntegrable`: a nonnegative,
  a.e.-strongly-measurable, uniformly bounded scalar energy on `(0,b)` is
  interval-integrable; no initial or positive-time continuity is assumed.
- `h3Audit_initialBoundedMeasurableEnergy_zero_of_continuousCoefficient`:
  the previously established approximate integrated-coefficient relative
  energy estimates and a finite kinetic-energy ceiling force exact scalar
  uniqueness.
- `H3AuditInitialCanonicalBoundedMeasurableRelativeEnergyData`: a PDE-facing
  sufficient condition using a bounded measurable physical `L²` comparison
  energy rather than directly postulating its interval integrability.
- The bridge recovers canonical compact weak-test equality, the actual initial
  `L²`/`H³` traces and the conditional terminal transverse estimate.

The bounded measurable input is **not weaker** than `L¹` integrability in
general; it is a physically motivated alternative. The original open-time
Navier–Stokes admissibility predicate has not yet been shown to imply that
initial uniform bound or the relative-energy residual inequalities. The
terminal strong-`H³` actual-vorticity endpoint is separate.

Lean compilation must be verified locally using the repository toolchain.

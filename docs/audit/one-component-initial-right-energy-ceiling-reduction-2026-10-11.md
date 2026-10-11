# Right-initial physical H³ energy trace to an initial kinetic ceiling

Base checkpoint: `49ef2a04` — derive initial kinetic ceiling from actual H3 energy.

New module: `OneComponentInitialRightEnergyCeilingReduction.lean`.

The previous initial old/selected physical uniqueness criterion assumes a **uniform** ceiling on `velocityH3EnergyAt u` for an entire positive initial interval. An independently supplied finite right trace of this actual energy provides a uniform ceiling `L + 1` on a possibly shorter interval. The proof extracts the interval from `Metric.tendsto_nhdsWithin_nhds` and stays inside the canonical restart radius.

The original comparison inequality (with coefficient *inside* the integral), upper coefficient ceiling, and epsilon-small absolute residuals restrict to that smaller interval. Absolute residual mass is monotone and interval integrability restricts via `IntervalIntegrable.mono_set`. The old physical `L²` time measurability similarly restricts to the smaller interval.

The resulting predicate implies the preceding `H3AuditInitialCanonicalH3EnergyCeilingRelativeEnergyData`, hence compact physical weak-test equality, the initial physical `L²` jet and upper `H³` trace, and—given a separate terminal actual-vorticity strong-H³ endpoint—the two full-time transverse intrinsic Ḣ^(3/2) conclusions.

## Noncircularity audit

The right energy trace is an independent PDE-side **premise**, not borrowed from the initial uniqueness conclusion. It is **not** derived from `LoggedPreterminalH3PathAdmissible`. The PDE relative-energy comparison, time measurability, shrinking approximation residuals, and terminal strong-H³ vorticity endpoint remain explicit obligations. This is a conditional bridge, not a Navier–Stokes regularity theorem.

No Lean compilation was run in the packaging environment; `lake env lean`, full `lake build`, and `tools/audit/baseline.sh --reuse-build` run in the consumer's repository before commit.

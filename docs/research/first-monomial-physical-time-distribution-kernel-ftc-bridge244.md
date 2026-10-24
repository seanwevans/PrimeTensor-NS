# Physical time-distribution kernel → Hilbert weak FTC (244)

Base: `e2c678c3` (*prove unconditional connected time distribution kernel*).

The zero-derivative distributional kernel theorem `h3Path_zeroDistributionDerivative_eq_constant_onStrict244` is now unconditional for nonempty strict intervals. Applied to the exact physical FTC defect it supplies, **assuming distributional momentum**, a scalar constant-distribution defect for each divergence-free test.

This patch adds the locally integrable additive rule for the project's concrete regular time distribution and derives a distributional representation of scalar physical momentum as the canonical projected source primitive plus a constant. The already-committed outer-primitive theorem upgrades this to the actual physical Hilbert FTC on all shorter closed time intervals.

Thus for `0<c<a<b<d<T`, `h3PathSolenoidalDistributionalMomentumOn244 hH3 c d` implies both `h3PathActualProjectedMomentumFTCDefect244 hH3 a b = 0` and `H3AuditPhysicalSolenoidalWeakFTCOn U R a b`.

**Unproved PDE-facing obligation:** derive the genuine tested temporal distributional momentum identity from `LoggedPreterminalH3PathAdmissible` and the old physical Navier–Stokes PDE. The equality between spatially tested classical time derivatives and derivatives of the integrated momentum pairing must be justified, not assumed. This module introduces no axiom, placeholder, unconditional global regularity theorem, or new admissibility field.

**Validation:** the zip/audit script is structurally checked by the assistant; Lean/Lake compilation requires the repository's pinned toolchain.

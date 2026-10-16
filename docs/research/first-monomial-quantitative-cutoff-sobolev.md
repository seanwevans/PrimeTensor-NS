# Quantitative radius-dependent Sobolev bound toward critical-half closure

Base commit: `aba59e89` (coefficient-one Schwartz quartic L²/L⁶ interpolation).

The old whole-space Sobolev module proves membership `C¹ ∩ H¹ → L⁶`, by
using a radius-independent cutoff-derivative majorant. Membership does not
supply the homogeneous, uniform numerical coefficient required to combine
that result with the complete 243-slot Hölder and integer-moment estimates.

This patch goes beyond membership. Mathlib's compact-support 3D inequality
has an explicit finite constant `S`; the existing PrimeTensor cutoff has an
absolute derivative bound `‖Dχ_R‖∞ ≤ C/R`, with `C` independent of the
field and radius. The new Lean theorem retains that factor precisely:

    ‖χ_R g‖₆ ≤ S ‖ |Dg| + (C/R)|g| ‖₂  (R > 0).

The first theorem isolates its pointwise form, the second applies the
compact-support Sobolev theorem to the ACTUAL cutoff field. Both apply to
any physical `Point3` spatial `C¹` field in H¹, not merely selected Schwartz
snapshots. The hypotheses are the genuine analytic H¹ hypotheses; no
conditional nonlinear bound, solenoidality or NS evolution is introduced.

**Remaining step**: pass to `R → ∞`, show the vanishing `(C/R)|g|`
remainder in `L²`, and recover `‖g‖₆ ≤ S‖Dg‖₂` with the same uniform
constant. Then apply the homogeneous Sobolev bound to the 27 actual
second-order Schwartz jets, convert the quartic aggregate into a finite
real bound, and combine with `lowNormalRealSchwartz_integerMoments_E2_mul_E3_pow_five_le`.

No unconditional Navier–Stokes regularity theorem is asserted.

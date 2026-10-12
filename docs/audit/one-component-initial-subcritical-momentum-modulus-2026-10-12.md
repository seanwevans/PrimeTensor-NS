# Quantitative positive-time physical momentum modulus from subcritical initial H³ energy

Base checkpoint: `e624a6b7` — derive initial projected RHS from subcritical H3 energy rate.

New module: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialSubcriticalMomentumModulus.lean`.

For `0 < s ≤ t < b < T`, assuming `E₃(r) ≤ M r^(-α)` on `(0,b]`,
with `0 ≤ α < 1` and `M ≥ 0`, the already formalized physical projected
source bounds, source Bochner integrability and global strong Hilbert FTC yield

    ‖u(t)-u(s)‖_(physical L²)
      ≤ (3 + C_L) M (t^(1-α)-s^(1-α))/(1-α).

The scalar estimate uses the exact Mathlib `integral_rpow` formula, not an
abstract integrability assumption for the source. The vector estimate uses
`intervalIntegral.norm_integral_le_integral_norm` and integral domination.

The existing strong physical L² right limit `L` under the same hypotheses
then yields the rate

    ‖u(t)-L‖_(physical L²) ≤ (3 + C_L) M t^(1-α)/(1-α).

This rate is towards the as-yet-unidentified Hilbert limit `L`, not necessarily
the actual declared `u(0)` velocity jet. In particular, no zero-time
continuity is smuggled in as an assumption or conclusion.

Independent frontiers: obtaining the subcritical energy envelope from bare H³
admissibility, establishing old-branch temporal-derivative joint continuity,
identifying the physical initial trace without the old/selected comparison,
controlling its vanishing residual, and the terminal vorticity endpoint.

This patch has not been elaborated with the user's Lean toolchain; run
`lake build <new module>` before committing.

## 2026-10-12 repair 1: right-neighborhood filter elaboration

The earlier proof used `Tendsto.mono_left nhdsWithin_le_nhds` without
specifying the underlying set defining `nhdsWithin`. Lean could not infer
that implicit set, even though it was intended to be `Ioi 0`. This repair
separates ordinary continuity at zero (`hAmbient`) from restriction to the
explicit right-neighborhood filter (`hRestricted`) and states the filter
inequality as `(𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ)`.

No analytic hypothesis, theorem statement, or mathematical proof strategy
changes.

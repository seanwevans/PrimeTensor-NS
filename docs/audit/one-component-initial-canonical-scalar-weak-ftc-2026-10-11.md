# Initial canonical compact weak data from scalar initial weak FTC

Baseline: `259ebd4b` (`derive full initial H3 trace from canonical overlap and compact data`).

The previous audit demanded distributional `t -> 0+` convergence against each compact smooth spatial test. The new module proves that convergence from the physically natural weak initial-time evolution identity for each test: `⟪φ,u_j(t)⟫_ℝ - ⟪φ,u_j(0)⟫_ℝ = ∫₀ᵗ g_{j,φ}(s) ds`, with only `IntervalIntegrable g_{j,φ} volume 0 b` on one interval. This is a scalar-in-time obligation. No common vector-valued Bochner source or test-uniform `L∞` bound is assumed.

`h3Audit_initialScalarWeakPrimitive_tendsto_zero` proves the integral tends to zero from the right using Mathlib interval-integral continuity. The next two theorems transfer this to compact test pairings and the actual three-component old physical velocity. `H3AuditInitialCanonicalOverlapScalarWeakFTCData` then combines the actual old/selected canonical overlap with this testwise initial weak equation; the remaining theorems discharge the previous compact-data interface and its physical L2/H3 consequence.

**Important:** The weak initial-time integral identity is an explicit hypothesis, **not established here from open-time Navier–Stokes admissibility**. This patch is a usable PDE-facing verification interface, not an unconditional deduction. The canonical old/selected overlap and terminal physical vorticity strong-H3 endpoint remain separate, unproved obligations.

No `sorry`, `admit`, or additional axioms. Local Lean compilation not available in the patch creation environment; run the local Lean checker and full audit before pushing.

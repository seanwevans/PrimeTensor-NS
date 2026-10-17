# Strong Schwartz jet Cauchy control automatically bounds all 243 roots

Baseline: `f9cb3139` (2026-10-17).

This patch removes the independent `Schwartz243UniformJetRoots244` assumption from the existence theorem for the signed first-monomial limit. For each of the 243 derivative slots, strong Cauchy control of the L² third jet and the L⁴ middle/cross second jets implies the corresponding scalar norm sequences are Cauchy by the reverse triangle inequality. `cauchySeq_bdd` bounds every scalar sequence, and a finite sum of the slotwise constants bounds all 243 roots at all indices by one `K ≥ 1`.

The new physical-root `L²` triangle and reverse triangle inequalities are derived from mathlib `eLpNorm_add_le`, the existing exact L² real-root identity and Schwartz continuity. The L⁴ reverse triangle inequality is reused.

The combined theorem `lowNormalRealSchwartz_firstMonomial_existsLimit_of_strongJetCauchy244` concludes existence of a real signed monomial limit using **only** `Schwartz243StrongJetCauchy244`, no separate uniform bound and no assumed nonlinear convergence.

No theorem about Sobolev graph density or the identification of the limit with a physical path pairing is claimed. This module should be compiled with the repository's pinned Lean toolchain, audited, and run through the full CI baseline before committing.

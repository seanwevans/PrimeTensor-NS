# Canonical H³ source peaks: eventual terminal-clock compression

Base commit `cbd47c19` (`bound canonical H3 peak clock by inverse-root Riccati transport barrier`).

Write `A=‖G₃(s)‖` for the original three-component spectral SUP norm, `B=∫ₐᵀD₃`, `E₀=velocityH3Energy0At u b`, `C=C₁` and `K=4422(C₁+1)`. The prior *noncompressed* canonical peak branch forces

    A^8 < 16384 (E₀+1) M(A)^3,
    M(A) = max(128 (B+1) 4422 (1+4 C A), 2 K (B+1) A).

For `A ≥ 2`, both terms have the amplitude-independent linear coefficient

    Q = max(128 (B+1) 4422 (1+4 C), 2 K (B+1))

and `M(A) ≤ Q A`. Therefore `A^8 < 16384 (E₀+1)Q³A³`, and cancellation of the strictly positive `A³` yields

    A^5 < 16384 (E₀+1) Q³.

Since `A≥2` entails `A≤A⁵`, the entire noncompressed branch has the explicit fixed amplitude ceiling

    A < 16384 (E₀+1) Q³.

Consequently any original peak exceeding the ceiling must obey **terminal compression**

    T - s ≤ (B+1)/H,
    A⁸ = 16384 (E₀+1) H³.

Under the inherited, unchanged **conditional** cubic-annulus critical-width hypotheses, `h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244` supplies the original source-maximizing physical times `sₖ` with `Aₖ → ∞`. Hence eventually those *same* peaks can only inhabit the terminal-compression branch. The witness time sequence and annulus-source maxima are not reselected.

## Boundary

This theorem eliminates the rapid half-loss branch under the specified joint critical-width regime; it does **not** eliminate terminal compression, imply strong H³ trace, or prove Navier–Stokes continuation. In particular the shrinking terminal-distance inequality is consistent with escalating amplitude. Do not silently convert this necessary alternative into a contradiction.

Validation: source and registrar static checks and archive integrity. Lean elaboration and baseline build remain to be checked in the repository pinned Mathlib environment.

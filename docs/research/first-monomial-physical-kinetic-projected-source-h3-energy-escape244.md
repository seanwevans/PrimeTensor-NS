# Actual physical source escape and H³ energy majorants

Baseline: `a5049e4f` — fixed Laplacian/Leray source escape from missing L² terminal trace.

## Quantitative source bounds

For every strictly positive preterminal time and actual Fourier-reconstructed source, the previously proved source bounds apply:

- `‖Laplacian_physical(t)‖ ≤ 3 E₃(t)`.
- `‖Leray_physical(t)‖ ≤ C_L E₃(t)`.
- `‖R(t)‖ ≤ (3 + C_L) E₃(t)` where `R = Laplacian_physical - Leray_physical`, and `C_L ≥ 0` is the established nonlinear Fourier coefficient.

The actual H³ quantity `E₃` is `velocityH3EnergyAt u t`, a normalized energy including a unit term. Bounds come from the already formalized physical Fourier inverse transforms, not an assumed identification.

## Cofinal alternative

A reusable lemma propagates cofinal norm escape backwards through any nonnegative pointwise scalar majorant. Applying this separately to the two physical components, each fixed component escape forces

`∀ b ∈ (a,T), ∀ M : ℝ, ∃ t ∈ (b,T), M < E₃(t)`.

Thus, for an H³-admissible trajectory with positive canonical terminal kinetic mass `L > 0`, **if no strong physical L² terminal trace exists**, the normalized H³ energy is cofinally unbounded. The result also follows directly from projected-source norm escape.

Conversely, bounding `E₃` on one final subtail bounds the physical projected momentum source and therefore yields a strong physical L² terminal trace of squared mass `L`.

## Logical scope

These results do *not* equate H³ nonextension with failure of physical L² convergence. H³ nonextension can coexist with an L² terminal trace. Cofinal unboundedness is not convergence to infinity nor quantitative dominance of a particular high-frequency channel; those require additional estimates.

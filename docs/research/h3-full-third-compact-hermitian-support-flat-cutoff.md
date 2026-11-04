# Support-flat even Fourier cutoffs for physical solenoidal Schwartz recovery

**Baseline**: `e554a8f1` — identify regularized real solenoidal Schwartz recovery with weighted H3 Fourier states.

## Obstruction

The exact Fourier identification in `FullThirdRegularizedPhysicalWeightedFourierBridge` assumed a sequence of *supplied* smooth, compactly supported, even cutoffs `χₙ` that equal one wherever the smooth transverse input `Uₙ` is nonzero. The previous physical Fourier theorem then removed `χₙ` algebraically from `χₙ RₙUₙ` but did not construct the cutoffs.

## Construction

For a compactly supported vector-valued function `U : (Axis three → ℝ) → (Axis three → ℂ)`, its topological support is compact and therefore bounded. Choose a radius `R` containing that support in a closed ball centered at the origin. Replace it by `ρ = max R 1 > 0` and take Mathlib's `ContDiffBump 0` with inner radius `ρ` and outer radius `2ρ`.

The bump is exactly smooth (`C∞`), compactly supported, valued in `[0,1]`, even under `ξ ↦ -ξ` (using the library's precise `.neg` theorem), and identically one wherever **any** component `U ξ j` is nonzero. There is no use of a singular Leray multiplier, no weak/distributional cutoff, and no new analytic assumption.

## Results

- `exists_thirdFullAxisSupportFlatEvenCutoff244`: unconditionally selects a suitable cutoff for each compact vector profile.
- `exists_thirdFullRealSchwartzRecovery_of_compactProfile244`: for any smooth compact Hermitian transverse input, constructs a cutoff and a genuine real, physically divergence-free Schwartz velocity whose Fourier transform is exactly `RₙU` at every frequency.
- `exists_thirdFullPhysicalSchwartzMovingCompletion_of_compactProfiles244`: eliminates *all* externally provided cutoff assumptions from the previous moving weighted-H³/real-decoder convergence assembly.

## Remaining hard mathematics

The moving-sequence theorem still requires that the moving *weighted* Fourier input have a smooth, compact, pointwise transverse, Hermitian representative, with the exact factor `W₃(ξ)` in the `Fin 3 ↔ Axis three` coordinate bridge. Existing Hermitian compact approximants become pointwise transverse only after applying Leray; the ordinary Leray multiplier is not smooth at the Fourier origin. The next bridge must use the globally smooth regularized Leray numerator and positive denominator directly, prove agreement with `Rₙ P` of the weighted compact inputs, and then diagonalize its norm error. Do not silently identify a measurable Leray representative with a smooth Fourier profile.

**Verification:** registrar and archive integrity are statically checked by the packaging workflow. Lean compiler verification is required in the user's project toolchain.

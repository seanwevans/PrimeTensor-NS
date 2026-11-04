# Smooth real-solenoidal Fourier recovery from unprojected compact Hermitian inputs

Baseline: `dd88ab3a` (`construct support-flat even cutoffs for real solenoidal H3 Schwartz recovery`).

## Proven algebra and construction

The compact Hermitian input `U` is **not required to be transverse**. The exact positive-denominator numerator is

`[|ξ|² U(ξ) - ξ (ξ · U(ξ))]/[|ξ|² + δ_n]`, with `δ_n = 1/(n+1)`.

Hermitian symmetrization doubles the original compact numerator, which cancels the existing `1/2` in the regularized inverse-square factor. The already-proved support-flat even bump is chosen from compact support, removing its frequency factor wherever the numerator can be nonzero. The existing Schwartz inverse-Fourier construction then gives an actual real, spatially divergence-free Schwartz velocity, including at ξ=0. The same amplitude is multiplied by the canonical Sobolev weight for the H3 spectral bridge.

## Still open

The result does not identify the normalized intrinsic-axis numerator with the project’s `Fin 3`-indexed Leray coefficient `h3LerayCoefficient` at nonzero frequencies. That is the remaining symbol-algebra step before equating this actual physical field to `h3FullThirdRadialRecoveryVelocity244 n (h3SpectralFinLerayApply F)` and deriving unconditional real-solenoidal Schwartz H3 density from the compact-Hermitian input sequence.

## Validation

Source contains no `sorry`, `admit`, or new axioms. Registration script performs static checks. Lean compilation requires the target repository and pinned mathlib toolchain and was not run in the packaging environment.

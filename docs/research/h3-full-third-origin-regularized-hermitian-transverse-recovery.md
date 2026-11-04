# Smooth origin-regularized Hermitian transverse recovery

**Base:** `fd1d883a` — Hermitian smooth-compact weighted H³ spectral density and real solenoidal approximation.

## The origin obstruction

The genuine Fourier Leray projection has a factor `|ξ|⁻²` and does not automatically map a smooth-compact Fourier field to a Schwartz field. The previously established transverse polynomial `N_ξ(U)=|ξ|²U−(ξ·U)ξ` is globally smooth but grows quadratically; applying it to a generic spectral approximant is not an approximate identity.

## Regularization

For `δ>0`, define `rδ(ξ)=(2(|ξ|²+δ))⁻¹`, smooth and even on the entire frequency space. Form `Gδ(ξ)=χ(ξ)N_ξ(rδ(ξ)U(ξ))` and Hermitianize `Hδ(ξ)=Gδ(ξ)+conj(Gδ(−ξ))`. For `χ` smooth compact, this is a smooth compact transverse Hermitian Fourier vector. The existing exact inverse Fourier construction therefore gives **real Schwartz velocity with physical divergence zero at every spatial point**.

If `U` is already Hermitian and transverse and `χ` even, the exact complex Fourier transform of that real Schwartz velocity equals `χ(ξ)·|ξ|²/(|ξ|²+δ)·U(ξ)`. The factor two from Hermitianization is cancelled by the `1/2` in `rδ`. The radial ratio lies in `[0,1]`; the exact pointwise loss is `δ/(|ξ|²+δ)`. The full-third longitudinal defect also vanishes identically on these true Fourier transforms, so the six-orbit equals the sixth-power flux for each momentum-conserving triad.

## Remaining analysis

This patch **does not** yet prove strong weighted-H³ convergence of the regularized fields as δ→0, nor replace a generic spectral `L²` target with a pointwise smooth transverse input without an approximation estimate. Next prove dominated convergence in weighted Fourier `L²` for the multiplier `|ξ|²/(|ξ|²+δ)`, using that the singleton frequency origin has zero Euclidean volume, then diagonalize with the already-constructed Hermitian smooth-compact density and bounded Leray projection. Identify the same real Schwartz sequence with the canonical physical second- and third-derivative jets before invoking H³ completion. No singular projection is declared Schwartz by fiat.

## Validation

Source registration and structural audit check all newly declared constants, no admitted placeholders, and axiom print declarations. Run the targeted Lean file, targeted Lake module build, full proof audit, and full build. Lean compilation of this new module was not available in the artifact environment.

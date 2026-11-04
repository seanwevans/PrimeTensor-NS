# Strong solenoidal approximation in the exact weighted H³ Fourier state

**Parent:** `140b9fac` — complex transverse numerator and exact longitudinal resonance.

## What this checkpoint proves

The continuation layer already supplies a genuinely bounded finite-dimensional Leray operator `P` on `H3SpectralFinVectorState = Fin 3 → H3SpectralScalarState`, with `‖P G‖ ≤ 6‖G‖` in the project's finite-product sup norm. It also proves `P G` is divergence-free, `P U = U` whenever `U` is divergence-free, and continuity of `P`. The critical H³ control layer separately proves that spectral Schwartz vectors are strongly dense in the same weighted H³ state.

The new module combines those independently established analytic ingredients, without importing a new approximation hypothesis. Given a divergence-free `U` and weighted spectral Schwartz vector `Phi`,

```
‖U - P(Realization Phi)‖
  = ‖P(U - Realization Phi)‖
  ≤ 6 ‖U - Realization Phi‖.
```

Choosing the raw Schwartz vector within `epsilon/6` gives a genuinely divergence-free spectral approximation within `epsilon` in the original H³ topology. The full sequence is produced by the existing weighted spectral Schwartz density sequence and continuity of `P`. The resulting projected sequence converges strongly to `U` and is Cauchy. Conversely, the subspace of divergence-free spectral states is sequentially closed, using continuity and pointwise fixedness of the bounded Leray operator on that subspace; no unsupported pointwise-limit argument for arbitrary `L²` representatives occurs.

## Why this matters for the physical full-H³ flux

At `140b9fac` the exact symbol identity has the longitudinal defect `D_long`. The new projected H³ sequence lies in the Fourier-divergence-free subspace *exactly*, not asymptotically, at every index. Its strong H³ limit is the intended solenoidal state. Thus **the spectral density/projection leg** needed for a solenoidal completion is closed.

## What is deliberately not claimed

The projected output is currently a weighted Fourier **`L²` state**. An arbitrary `L²` Leray projection need not be represented by a physical **real Schwartz vector**. To connect this sequence to `fullSchwartzThirdCommutator244` and the existing `H3MatchedSchwartzGradientCompletion244`, we must still:

1. Build a smooth compact weighted-frequency family *supported in annuli separated from zero*, with a Hermitian/reflection symmetry and dense range in the **divergence-free** weighted subspace.
2. Show the Leray matrix preserves smoothness, support and Hermitian reality on those annuli, and that deweighting and inverse Fourier transform give a genuine real physical Schwartz vector.
3. Prove pointwise decoder exactness and both second/third derivative jet identities for that same family. Then reuse the canonical reference-independence/limit theorem and `D_long=0` to reach the **uncorrected** physical spectral flux limit.

There is no frequency-dependent denominator in the polynomial numerator of `140b9fac`. The true Leray multiplier divides by `|ξ|²` away from zero, which is harmless on an annulus; zero-frequency excision must be proved in the weighted `L²` topology rather than asserted. Moreover, the global polynomial numerator alone is not a bounded H³ projection: it grows like `|ξ|²`, so the bounded Leray map is the appropriate object for density.

## Source and validation

The code is based on the actual GitHub state `140b9fac`; it reuses the exact repository's `exists_h3SchwartzSpectralVelocityApprox_norm244`, `exists_h3SchwartzSpectralVelocityApprox_sequence244`, `h3SpectralFinLerayApply_divergenceFree`, `h3SpectralFinLerayApply_eq_of_divergenceFree`, `h3SpectralFinLerayApply_sub`, `norm_h3SpectralFinLerayApply_le`, and `continuous_h3SpectralFinLerayApply`. Structural checks and ZIP integrity are run during packaging. Lean compilation must be verified by the user's Lake toolchain.

# Strong weighted-H³ convergence of origin-regularized radial recovery

**Base:** `9de79370` — construct smooth origin-regularized Hermitian transverse H³ Schwartz recovery.

## New analytic result

The previous stage proved the exact Fourier amplitude of the real, solenoidal Schwartz recovery of a smooth compact Hermitian transverse input: for an even cutoff it equals `χ(ξ) q(ξ)/(q(ξ)+δ) U(ξ)`, with `q(ξ) = Σ_i ξ_i²`.

For an **arbitrary** scalar weighted H³ spectral state `F ∈ L²(V3;ℂ)`, define a positive scale `δ_n = 1/(n+1)` and its radial regularization as the `L²` class of

`(‖ξ‖²/(‖ξ‖² + δ_n)) F(ξ)`.

The new proof shows:

1. `0 ≤ ‖ξ‖²/(‖ξ‖²+δ_n) ≤ 1` uniformly, with a continuous multiplier for each `n`.
2. At each nonzero frequency the factor tends to 1; the singleton `{0}` has zero Fourier volume, proved from the project's real three-axis hyperplane null-measure argument.
3. The pointwise complex error is bounded by the unchanged input `|F(ξ)|`.
4. Bochner dominated convergence of the **square error integrals** and the project's exact `L²` norm-square identity show `‖R_nF−F‖→0`, without assuming a smooth representative for `F`.
5. The same regularization converges in the full three-component, finite-product weighted-H³ space; the sequence is Cauchy.
6. `h3FourierPoint3_norm_sq_eq_sum_coordinates` identifies the Euclidean multiplier with the exact positive-depth axis-coordinate factor used by `9de79370`.

## Still open

This does **not** by itself assert that every regularized `L²` state is a physical Schwartz velocity. The next link must use the committed compact-Hermitian smooth density, supply compatible even compact cutoffs and smooth transverse input, and identify the weighted spectral state of the actual inverse-Fourier real solenoidal Schwartz field. Its exact real second/third physical derivative jets must then be matched with the canonical H³ completion. The endpoint signed transport integral and Navier–Stokes global continuation are not established by this result.

# Radially regularized moving solenoidal Hermitian H³ density

**Base commit:** `bed68aa7` — strong weighted-H³ convergence of the origin
regularizer on a *fixed* spectral state.

## The missing diagonal estimate

Write `Rₙ` for multiplication by the scalar frequency symbol

    rₙ(ξ) = |ξ|² / (|ξ|² + 1/(n+1)).

For each scalar Fourier L² class, `Rₙ` is a contraction. Its extension to the
actual three-component weighted H³ state also has operator norm at most one.
The proof shows subtraction commutes with this multiplier in the bundled L²
space, not just for unbundled functions. It then proves

    ||Rₙ V - U|| ≤ ||V-U|| + ||Rₙ U-U||.

Consequently **for any moving sequence** `Vₙ → U` in weighted H³, one has
`Rₙ Vₙ → U` and the diagonal is Cauchy. This is the logically necessary step
that fixed-target dominated convergence alone does not provide.

## Invariants preserved

* `rₙ` is real and even, so weighted and raw Hermitian Fourier reality are
  preserved using the project's exact reality equivalences.
* The same scalar `rₙ(ξ)` multiplies each component; it passes through the
  finite Fourier divergence sum, preserving incompressibility exactly.
* The existing raw-Hermitian-to-realizable decoder theorem gives genuine
  real physical L² realizability of every diagonal state.
* Applying the diagonal theorem to the compact-Hermitian Leray sequence from
  `fd1d883a` establishes a single strongly convergent, Cauchy, Hermitian,
  realizable and divergence-free *weighted Fourier state* sequence.

## Remaining analytic bridge

This theorem deliberately **does not** claim the diagonally regularized
weighted states are already the Fourier encodings of real **Schwartz** spatial
fields. That requires: (1) deweighting each compact smooth input by the exact
H³ weight; (2) identifying the axis and `Fin 3` polarizations and the precise
Leray matrix; (3) verifying the regularized polynomial construction from
`9de79370` matches the actual radial Leray image pointwise; and (4) applying
Schwartz Fourier inversion to obtain actual physical fields and their matched
zeroth-, second-, and third-order jet identities.

No Navier–Stokes global continuation or endpoint closure is asserted here.

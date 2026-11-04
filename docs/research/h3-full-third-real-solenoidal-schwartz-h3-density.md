# Real solenoidal physical Schwartz density in weighted H³

**Baseline:** `aa8a09b3` (*identify regularized physical Schwartz Fourier states with weighted H3 Leray L2 recovery*).

## The analytic bridge

A real-data Fourier H³ target is represented as a `Fin 3`-indexed complex
weighted `L²` state. The compiled Hermitian smooth compact density theorem
constructs actual Schwartz profiles `Φ_n` with pointwise Hermitian reflection.
The exact H³ reciprocal weight converts them to unweighted Fourier profiles:

\[
U_n(\eta)_a = W_3(\operatorname{toLp}\eta)^{-1}\,\Phi_{n,a}(\operatorname{toLp}\eta).
\]

This conversion is globally smooth and does not enlarge the original compact
supports, because the reciprocal weight is smooth and nonzero. Finite-index
compact support passes to the entire `Axis Depth.three` complex vector by a
finite union of topological supports. The reciprocal weight is real and even,
so the polarization remains pointwise Hermitian.

For the weighted pre-Leray state `G_n = Φ_n.toLp`, the already-compiled weighted
Fourier identification applies at the exact scale `δ_n = 1/(n+1)`:

\[
  W_3 \widehat{u_{n,a}} = [R_n P G_n]_a
\quad\text{a.e. on Fourier space}.
\]

The fields `u_{n,a}` are real spatial Schwartz maps and their physical
coordinate divergence vanishes **pointwise**. The projected radial regularizer
converges strongly in the original weighted H³ spectral norm to every
Fourier-divergence-free, raw-Hermitian target, and the canonical real physical
`L²` decoder converges. The sequence is Cauchy.

## Exact scope

This closes **real divergence-free Schwartz density in the weighted spectral
H³ topology** for target states satisfying the existing real-data Hermitian
and Fourier divergence-free predicates. The statement is existential, not an
assertion that every `L²` class has a pointwise smooth representative.

The subsequent hard-math bridge should identify canonical physical second-
and third-order derivative jets of this sequence through the existing
Fourier/Plancherel compatibility theorems. It should not infer convergence of
nonlinear quartic terms solely from weighted H³ convergence without the
appropriate interpolation or integral control.

## Audit

One public definition, seven public theorems, and 16 axiom-audit lines.
There are no `sorry`/`admit` placeholders or new axioms. The registrar is
idempotent and requires exactly one registration in the project index and
audit module. Lean compilation must run in the user's Lean environment.

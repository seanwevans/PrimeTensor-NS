# The finite Leray multiplier is the weighted Fourier state of real solenoidal Schwartz recovery

**Baseline:** `ad13c120` (finite-axis identity for the regularized Leray numerator).

The previous theorem gives, at every Fourier frequency and for every complex
finite-index polarization `z`,

\[
\frac{|\xi|^2}{|\xi|^2+\delta_n} P(\xi)z
 = \frac{|\xi|^2 z-\xi(\xi\cdot z)}{|\xi|^2+\delta_n}.
\]

The earlier real-Schwartz construction has exactly the right-hand-side
Fourier profile for any **smooth compact Hermitian pre-Leray** raw input `U`.
This file identifies that physical transform with the actual
`h3FullThirdRadialRecoveryVelocity244 n (h3SpectralFinLerayApply G)` state,
provided `G` is the bundled weighted state represented by `W₃ U`.

The argument uses only three existing almost-everywhere representatives:

1. The `MemLp.toLp` representative of the radial multiplier.
2. The `h3SpectralFinLerayApply_ae` matrix representative.
3. The three componentwise a.e. equalities of the **pre-Leray** weighted input.

The common full-measure set is formed using `filter_upwards`. The scaled
matrix/numerator equality then equals the exact *weighted* Schwartz Fourier
identity. The finite-coordinate permutation is the committed
`h3AxisOfFin3` / `h3ClassicalizationFinOfAxis` equivalence.

The projective Fourier `Lp` state is **never presumed smooth**. The compact
cutoff is chosen automatically from the already proved support-flat even
bump theorem; the resulting real Schwartz field has zero *physical*
divergence at every spatial point.

The moving-sequence theorem adds convergence under the standard prior H³
approximation of the pre-Leray weighted inputs, assuming only that the target
is divergence-free. Bounded continuity of the Leray projector plus uniform
radial contraction yields strong H³ convergence and a Cauchy sequence, and
the real spectral decoder inherits convergence.

**Outstanding:** discharge the smooth axis pre-Leray representative hypothesis
by deweighting the existing compact Hermitian `Fin 3 → SchwartzMap` density
sequence and transporting it through `WithLp.toLp` and the axis equivalence.
That step will deliver unconditional physical solenoidal Schwartz density.

No theorem in this increment claims an unconditional Navier–Stokes
continuation bound.

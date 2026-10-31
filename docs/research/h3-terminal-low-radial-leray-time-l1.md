# Actual low-band Leray source: terminal-time Bochner L¹

Parent commit: `03b0b521`.

## New mathematical step

The previous module proved the squared physical L² kinetic ceiling for each
sharp radial cutoff of the **actual** nonlinear Leray forcing:

`‖B_(ρ,i)(t)‖² ≤ volume(Sρ) · (18 ρ E₀(b))²` for `b < t < T`.

This module builds a complex-linear, norm-≤1 sharp-cutoff operator on Fourier
L², identifies its output with the Fourier state constructed previously, and
uses the established spectral source continuity and real inverse-Fourier
decoder to prove **strong continuity in positive physical time**.
The finite interval plus the fixed kinetic bound then gives Bochner L¹:

`IntervalIntegrable (fun t => B_(ρ,i)(t)) volume b T`.

The proof uses no auxiliary time-measurability hypothesis and no bound on the
terminal H³ norm. The cutoff is sharp and only needs to be measurable in
spatial frequency; no smoothness of the multiplier is claimed.

## Not yet proved

1. The same bounded-frequency time-L¹ result for the physical Laplacian.
2. Equality of a single bounded linear physical-space Fourier cutoff with the
   separately decoded nonlinear and Laplacian components of the full
   projected momentum source.
3. Consequently, elimination of the remaining low-pass L¹ premise from the
   high-pass escape theorem.

This does not establish an unconditional Navier–Stokes singularity.

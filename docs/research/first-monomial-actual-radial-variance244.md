# Actual physical radial Fourier variance and zero-defect rigidity

Checkpoint: `f839a850` — reduce essential H³ Fourier Landau barrier to the physical middle moment.

## What is new

The first physical Fourier Cauchy defect is

\[
F_1(t) = E_0(t)D_3(t)-E_2(t)^2\ge0.
\]

Its earlier interpretation as a Fourier variance is now a **proved physical integral identity**. Let
`S(ξ)` denote the actual nonnegative Fourier velocity mass density and let
`q(ξ)=(2π)^2|ξ|²` be the Fourier gradient square. The existing exact Fourier
moment identification gives

\[
E_0=\int S,\quad E_2=\int q^2 S,\quad D_3=\int q^4 S.
\]

The new proof uses only these established integrable moments, and verifies

\[
\boxed{\int (E_0q(\xi)^2-E_2)^2 S(\xi)\,d\xi=E_0F_1.}
\]

This formulation is **division-free**: it remains meaningful if `E0=0`. It
is not an assumption that `F1` enjoys any fixed positive lower bound.

If `F1=0`, the integral vanishes. Since the integrand is nonnegative,
then a.e. whenever `S(ξ)>0`,

\[
E_0q(\xi)^2=E_2.
\]

Thus exact saturation requires a single squared-radial-frequency level on
the essential support of the actual Fourier mass. The contrapositive gives
strict positivity of `F1` whenever that a.e. monochromaticity fails. Coupled
with the prior sharp-Young first-variance correction, this yields a strict
improvement of Young's ceiling at such a time for positive `K,D3`.

## What remains

This does not itself establish that physical Fourier mass cannot be supported
a.e. on a measure-zero sphere (that requires a separate null-level-set
argument in the project's exact Fourier measure space), and it certainly
does not supply a **uniform** dispersion gap along terminal time. The next
hard analytic target is to derive quantitative spectral spreading under the
Navier–Stokes evolution rather than merely a qualitative a.e. condition.

## Build and audit

Run `python3 -B tools/audit/register_first_monomial_actual_radial_variance244.py`,
`python3 -B proof/generate_index.py`, `--check`, fragment checks, the module
Lean check and full build, and `bash tools/audit/baseline.sh --reuse-build`.
The Lean source contains no axioms, placeholders, or external hypotheses
beyond the preexisting logged Navier–Stokes admissibility framework.

# Complex six-order solenoidal H³ flux: both outer-minimum frequency orientations

Base HEAD: `abf16d44ece0f8942126e4a273d66780a2ae1160`.

## New hard-math step

The accepted `FullThirdSolenoidalHighHighLowH3Budget` places the raw first Fourier
moment on the middle momentum `q` of the conserving triad `p+q+r=0`, provided
`|q| <= min(|p|,|r|)`.  The previous commit `abf16d44e` proves the resulting
sector integral is bounded by `648 C₁ K³` on the exact physical weighted H³
Schwartz recovery.  But a general Fourier triad's smallest momentum may
be the first or the last input.

To move the low momentum, it is NOT valid to permute the three terms in the
explicit sixth-power formula by inspection: the formula is equal to the six
ordered contributions only under the full momentum and three complex
divergence-zero hypotheses.  Instead, we prove at the polynomial level that
the **complete six-order complex symbol** is invariant under adjacent
permutations of `(momentum, polarization)` pairs. Then use the existing theorem
`thirdFullComplexSix_sixthPowerFlux244` twice for each transposition. The
resulting sixth-power flux identities are valid for *genuine complex* Fourier
polarizations (not an artificial real or Hermitian replacement).

For `p` the lowest frequency the bound is

    |Flux(p,q,r;A,B,C)| <= 52 (|q|³|B|)(|r|³|C|)(|p||A|).

For `r` the lowest frequency it is

    |Flux(p,q,r;A,B,C)| <= 52 (|p|³|A|)(|q|³|B|)(|r||C|).

The older measure-preserving outer-L¹ integration (`h3Triad_integral_norm_le_outer_L1`)
handles the first orientation. Its product-swap image handles the last. For
any measurable sector `s` lying in either region, no radial ceiling is needed:

    |∫_s Flux(v)| <= 72 (∫ |ξ|⁶ |vhat(ξ)|²) (∫ |ξ| |vhat(ξ)|).

The literal weight in `|ξ|` is unnormalized; the physical Fourier derivative
convention `(2π)` remains inside the exact H³ weight. The previously proved
cubic Fourier deweighting estimate and first-moment embedding then give

    |∫_s Flux(v)| <= 648 C₁ K³

when the same weighted physical Fourier representatives satisfy
`||G_j|| <= K`. The physical snapshot theorem obtains ONE recovery sequence,
retaining weighted-H³ strong convergence, solenoidality, both sector bounds,
the sixth raw moment budget, and convergence of the full signed complex flux
to the original physical third-order transport derivative.

## Limits

This file covers each outer-minimum region.  It does **not** yet prove the
measurable disjoint partition of all three minimum-frequency regions, sum the
sector integrals into a sharp full-flux bound, furnish a favorable sign or
absorption constant, or make K uniform as time approaches the terminal
endpoint. Those remain separate mathematical steps.

## Verification

The archive is syntax/structure checked, `unzip -t` tested and registration
is tested idempotently in a mock repository. Lean/mathlib are not installed in
the patch creation environment, so *compilation is unverified*; the full run
script first checks the targeted Lean file, target build, and all standard
project audits, then commits and pushes only if successful.

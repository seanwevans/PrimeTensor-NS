# Native mixed sixth-power Fourier flux: automatic Schwartz integrability

Base: `922485b19d7811d6d6a74a119144ef503e2a9cb3` — bridge native mixed sixth flux Young moments to weighted H3 spectral states.

## The missing mathematical step

The previous weighted-H3 mixed Young bridge proved a seventh-power finite-radius bound, but required two genuine analytic contracts: integrability of the unsigned mixed contraction budget on all of the six-dimensional momentum plane, and integrability of the complex mixed flux on the low-maximum sector. Diagonal Schwartz integrability does not automatically establish either assertion for three unrelated polarizations.

Here `v, w, h` are arbitrary independent three-component *complex Schwartz* fields. Their actual Fourier polarizations are used, without any Hermitian or solenoidal replacement. The three complex budget contractions are:

* `X = (sum_j vhat_j(p) hhat_j(r)) (sum_m r_m what_m(q))`
* `Y = (sum_j vhat_j(p) what_j(q)) (sum_m q_m hhat_m(r))`
* `Z = (sum_j what_j(q) hhat_j(r)) (sum_m r_m vhat_m(p))`

with `q = -(p+r)`. The Fourier multipliers are REAL frequency components, cast to complex. These equations represent the exact three terms of `thirdFullComplexSixthFluxContractionBudget244`.

Each contraction expands into nine coordinate-indexed Fourier triple terms, and the frequency factor is placed on the Schwartz factor at that same frequency. The existing `h3Schwartz_frequencyWeight` and measure-preserving `h3Schwartz_triad_integrable` prove **global L1** integrability. The three norm-integrals sum to the native unsigned budget, with no extra regularity or moment hypothesis.

## Genuine signed flux on the exact sector

The three squared-radius cubic gaps `R³−P³`, `Q³−P³`, `R³−Q³` are continuous complex functions of `(p,r)`. The signed mixed flux equals `X (R³−P³) + Y (Q³−P³) + Z (R³−Q³)`; therefore it is a.e. strongly measurable. On the literal complement of the high-maximum set, each radial cubic coefficient is bounded by the established `3 [2(R+1)]⁶` factor. The global mixed-budget integral then dominates the sector-restricted flux norm, proving automatic integrability on **LowMax(R)**.

## Consequence

For independently Schwartz-regular `v,w,h` represented by three actual weighted-H3 spectral velocity states `V,W,H`, the prior reciprocal-scaled Young estimate now applies **without either mixed-integrability assumption**:

`∫_LowMax(R) |F6(v,w,h)| <= 9 [2(R+1)]^7 ((3 scale² ||V||² + 3 scale⁻² ||H||²)/2) (3 C0 ||W||)`.

This is an absolute-integral inequality for the genuine phase-bearing kernel. No global H3 terminal bound, no automatic physical-time continuity and no Navier–Stokes continuation theorem follow at this stage. The next mathematical step is a two-snapshot difference theorem using the *exact* three-term polarization telescope. Each difference must be identified with the Fourier representative of the difference of two physical weighted H3 states, on the correct low-maximum band. This is essential for using actual kinetic-gap PDE freezing rather than a fictional full-H3 temporal estimate.

## Verification

The registrar checks each named declaration and `#print axioms`; run the pinned Lean toolchain after `proof/generate_index.py` and before committing. Static source/ZIP/registrar checks do not establish Lean elaboration or theorem kernel verification.

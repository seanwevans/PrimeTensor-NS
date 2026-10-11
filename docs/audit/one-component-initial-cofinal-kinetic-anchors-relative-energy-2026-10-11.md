# Initial cofinal kinetic anchors and positive-time dissipation

Parent checkpoint: `852300ec` (“derive initial uniqueness from integrated kinetic budget”).

## New result

`OneComponentInitialCofinalKineticAnchorsRelativeEnergy.lean` closes a **whole-positive-time** energy monotonicity lemma for the actual order-zero kinetic energy. The existing closed H³ local-restart smoothing theorem supplies an actual physical high-order energy class before every strict time. The previously proved exact PDE energy derivative identity plus whole-space transport and pressure cancellation and diffusion sign make the kinetic derivative nonpositive at every strict time. The standard real mean-value theorem then gives

\[
0<s\le t<T\quad\Longrightarrow\quad E_0(t)\le E_0(s).
\]

In particular, if for each `t ∈ (0,b)` there is a strictly earlier `s ∈ (0,t)` with `E₀(s) ≤ B`, then `E₀(t) ≤ B` throughout `(0,b)`. By the already-proved physical kinetic identity,

\[
\lVert u_{\mathrm{old}}(t)\rVert_{L^2}^2=E_0(t)\le B,
\]

so the old physical Hilbert velocity has uniform norm ceiling `sqrt B`. Its positive-time Bochner measurability was established independently at checkpoint `327cdeaa`.

An additional scalar result shows that if arbitrarily early samples satisfy `E₀(s) ≤ E₀(0)+ε` for every positive `ε`, then the exact kinetic energy inequality `E₀(t) ≤ E₀(0)` follows at every strict physical time. The proof does not need a time-zero derivative, a right limit, or a temporal defect integral.

## PDE-facing comparison chain

`H3AuditInitialCanonicalCofinalKineticAnchorsRelativeEnergyData` assumes (i) actual initial H³ Fourier data and a valid Picard radius; (ii) cofinally bounded actual kinetic samples; and (iii) the still-independent integrated-coefficient relative-energy inequality with arbitrarily small `L¹` residual. It requires neither the right-kinetic-energy limit (`985236d5`) nor the integrated kinetic defect (`852300ec`).

The bridge recovers the existing old-kinetic-ceiling interface and thereby the initial weak-test comparison, initial physical `L²` trace / upper `H³` energy trace, and the conditional full-time transverse intrinsic Sobolev estimates.

## Boundaries and mathematical status

The cofinally bounded initial kinetic samples are **not** derived from the open-time path class. Positive-time dissipation alone cannot prevent an infinite-energy entrance layer as `t ↓ 0`. Obtaining the initial energy bound and especially the epsilon-vanishing old/selected relative-energy inequality from a genuine Navier–Stokes initial-value formulation remain PDE obligations. The terminal actual-vorticity strong-H³ endpoint is a separate premise. This is not an unconditional Navier–Stokes regularity theorem.

This module contains no `sorry` or `admit`. Lean compilation must be checked with the repository's Lean toolchain; only archive/static verification is possible in the artifact-generation environment.

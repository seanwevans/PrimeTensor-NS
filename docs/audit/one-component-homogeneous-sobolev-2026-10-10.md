# One-component endpoint: exact homogeneous three-halves Fourier density

Verified input commit: `7fc1a74c`.

The project Fourier transform convention uses `q(ξ) = (2π)^2 ‖ξ‖²` and the weighted H³ solver state `G(ξ) = W₃(ξ) û(ξ)` with `W₃² = 1 + q + q² + q³`. The squared homogeneous \dot H^{3/2} Fourier seminorm is `∫ sqrt(q³) |û|²`. This checkpoint defines that exact Fourier density using `h3SpectralScalarRawFourier` and proves the pointwise, integrable domination

    0 ≤ sqrt(q³) |û|² ≤ |G|²,     ∫ sqrt(q³) |û|² ≤ ‖G‖².

It then specializes to the actual spectral velocity components selected by `hPhysical`, removing the earlier ad hoc spectral-domination assumption. The existing terminal-integrability lemma implies a common terminal interval of finite homogeneous three-halves time-integrals **provided the scalar time densities are measurable**.

## Still open, not silently assumed

1. Prove time measurability of `h3AuditHomogeneousThreeHalvesVelocityTimeDensity`, ideally by establishing the appropriate strong/weak measurable dependence of selected spectral states on physical time. No spatial slice measurability alone gives this.
2. Identify the weighted Fourier representative with the *physical* homogeneous Sobolev seminorm in the published theorem's normalization, and check the local-strong-solution class, initial-time integrability and initial vorticity assumptions against the exact version of the paper.
3. Either formalize or explicitly import a suitable published one-component regularity theorem before asserting `H3AuditOnePhysicalEndpointLiteratureBridge`.

The new results are rigorous Fourier inequalities conditional only on their displayed time-measurability premise. No unconditional Navier–Stokes regularity result follows.

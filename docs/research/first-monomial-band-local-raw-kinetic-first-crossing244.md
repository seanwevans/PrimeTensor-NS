# Exact annular raw Fourier kinetic mass at the physical first crossing

Base: `a021a13c` (physical kinetic bandwidth bounds).

The earlier crossing inequality `3 R³ < 16(Q+1)^8 E₀(b)` uses **global** kinetic energy. Its weakness is geometric: the `L²` energy may live entirely away from the annulus that carries the cubic `H³` dissipation. This module replaces the global energy input by a *band-local unweighted raw Fourier square mass* on the exact annulus `B_Q \ B_R`.

Write `D(ξ)=|ξ|_grad² Σ_j |G_j(ξ)|²`, `F(ξ)=Σ_j |G_j(ξ)|²`, and `g(ξ)=Σ_j |û_j(ξ)|²`, where `G` is the actual encoded weighted `H³` spectral velocity. The repository already proves `F ≤ W(Q) g` almost everywhere on `B_Q`, with `W(Q)=1+Q²+Q⁴+Q⁶`. Since `D ≤ Q² F` there, restricting both estimates to the same measurable annulus `A_{R,Q}:=B_Q\B_R` yields

`∫_A D ≤ Q² W(Q) ∫_A g`.

The exact set-integral difference lemma `setIntegral_sdiff` identifies `∫_A D` with `lowDiss(Q,t)-lowDiss(R,t)` for `R≤Q`, without a fictitious pointwise Fourier identification or an illicit subtraction of unrelated bounds.

For a **physical minimal first crossing**, `3R³/4 < lowDiss(Q,t)-lowDiss(R,t)`. Combining with `Q²W(Q)≤4(Q+1)^8` gives the new strictly local necessary condition

`3 R³ < 16(Q+1)^8 kineticRawMass(A_{R,Q},t)`.

The final theorem selects this actual annular kinetic cost along the cofinal minimal first-crossing sequence, preserving minimality. This is a pointwise **lower bound on raw kinetic mass in the selected band** (scaled by its large frequency factor), not a uniform lower bound on kinetic mass or a Navier–Stokes regularity contradiction. The cost can decay to zero if the selected outer cutoff grows sufficiently fast. No additional temporal integrability is asserted.

Validation: run the module's `lake env lean` check, its `lake build`, audit source, regenerated proof index, and complete project build before commit.

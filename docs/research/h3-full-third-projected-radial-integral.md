# A real Fourier-pair integral retaining the full H³ radial defect

**Base:** `95295cdb` (full H³ signed transport radial factorization).

The previous result proved a genuine six-permutation symbol identity; it had not yet demonstrated that the gain survives integration. This increment inserts that identity into the existing **frequency-varying, exactly transverse, Hermitian** polynomial kernel. The three polarizations are the actual moving Leray germs, not constant vectors frozen at a packet center.

For momentum `q = -p-r` and projected real polarizations `U(p), V(q), W(r)`, the previously proved Hermitian identity is `K(p,r)=2 S₆(p,q,r;U,V,W)`. Let `H(p,r)` be the sum of the absolute values of the three non-defect prefactors of the exact radial factorization, with the same moving polarizations. On any region where all three differences of squared frequency radii have absolute value at most `ρ`,

    |K(p,r)| ≤ 2 ρ H(p,r).

The new theorem integrates this inequality **over any compact six-dimensional momentum-pair closed ball** contained in that near-balanced region:

    |∫_ball K(p,r) dp dr| ≤ 2 ρ ∫_ball H(p,r) dp dr.

Both integrals are finite automatically, because `K` and `H` are continuous and the integration region is compact. No ad hoc integrability or terminal-energy hypothesis is added. The factor `ρ` is preserved *outside* the integral; it would have been lost if the six ordered terms were bounded individually before symmetrization. The analytic gain is local to comparable squared radii. The prior adverse Schwartz triad has radii squared `(1,2,5)` and remains an obstruction to global static absorption.

## Boundary

This is a real six-dimensional Fourier-pair **kernel** integral, not yet an equality for the complete unrestricted Fourier integral of an arbitrary real divergence-free Schwartz velocity. The latter requires a general real/complex polarization decomposition and measure-preserving six-permutation symmetrization of the previously proved `fullThirdSchwartzFourierCoefficient244`. The current proof also makes no claim of bound by kinetic energy, H³ energy, or full H⁴ dissipation; the complementary far-from-balanced region is untreated. No new `Depth`-specific invariant is asserted simply by changing coordinates.

## Next acceptance test

Derive the same radial-defect integral identity for the **actual arbitrary Schwartz velocity**, not just the projected polynomial germ. Distinguish near-balanced and far-separated Fourier triads and test the resulting majorant against the established fixed-kinetic Schwartz concentration counterexample. The goal is a PDE-time estimate that closes H³ continuation, not an additional singularity alternative.

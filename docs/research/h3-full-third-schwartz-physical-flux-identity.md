# Complete physical H³ Schwartz transport: exact sixth-power spectral flux

**Pinned base:** `b8851e77` (reindex full physical H³ Schwartz transport density into sixth-power flux).

This patch closes the Fourier normalization of the **static signed physical third-order H³ commutator**, without using a packet approximation, a false positivity assumption, or an independent integrability hypothesis.

Let `f` be any real, `Point3`-solenoidal Schwartz velocity and let `U(ξ)` denote the complex Fourier transform of its three real components. For `p+q+r=0`, define the complex-bilinear—not sesquilinear—polarization contraction, and set `P=|p|²`, `Q=|q|²`, `R=|r|²`. The complete corrected six-order complex flux is

```
F(p,r) = (U(p)·U(r)) (r·U(q)) (R³−P³)
       + (U(p)·U(q)) (q·U(r)) (Q³−P³)
       + (U(q)·U(r)) (r·U(p)) (R³−Q³).
```

The prior modules established the complex six-orbit flux factorization, its equality to the sum of six measure-preserving ordered kernels, unconditional integrability of that ordered kernel, and pointwise reindexing of all **four** original `3+3+1` physical gradient placements plus three copies of the original `3+2+2` interpolation term.

Here the previously separate pieces are assembled: after commutation of all five finite coordinate sums with the absolutely convergent Fourier integral, the full complex physical coefficient equals `2*(2πi)^7 * ∫ H`, where `H` is the half-normalized physical density. The prior six-orbit theorem gives `∫F=6∫H`. Consequently

```
fullThirdSchwartzFourierCoefficient244(f) = ((2πi)^7 / 3) * ∫F
fullSchwartzThirdCommutator244(f) = ((2π)^7 / 3) * Im(∫F)
```

Here `(2πi)^7 = -i(2π)^7`. The coefficient `1/3` is `2/6`: the physical energy pairing's factor two over the actual six-order momentum symmetrization. All terms are absolutely integrable by the committed Schwartz kernel proofs. The physical `Point3` divergence predicate supplies spectral solenoidality through the established divergence bridge.

**Boundary.** This is an exact real-Schwartz static transport representation, not a Navier–Stokes continuation or global regularity theorem. The already proved adverse fixed-kinetic Schwartz family forbids deducing a universal static linear absorption bound from this representation alone. A PDE-time mechanism or a genuinely stronger scale-sensitive estimate remains necessary. In particular, equality of all three radii cancels the six-order flux, but two matching radii need not cancel the third transfer.

The new source appends the finite-sum/integral normalization proof to `FullThirdSchwartzPhysicalSevenBridge.lean` so it can reuse the previously verified *private* physical Fourier-slot definitions directly. `FullThirdSchwartzPhysicalFluxIdentity.lean` records the exact complex and real physical spectral-flux consequences. No original Lean declarations are weakened or replaced.

Lean compilation is not available in the patch-authoring environment; run `lake env lean` and the full repository audit in the user's project.

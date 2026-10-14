# Canonical-axis real Schwartz velocity

Base checkpoint: `1a1553e4` (reconstruct real Schwartz velocity from Hermitian Fourier packet).

The original packet is indexed by `Fin 3`, whereas the physical H³ Fourier carrier and the physical first-monomial aggregate are indexed by `Axis Depth.three`.

The new module uses the already-verified `h3Fin3EquivAxisThree` and `ContinuousLinearEquiv.piCongrLeft` to turn the smooth frequency packet into a complex Schwartz spectrum on `H3FourierPoint3`. Applying the prior Hermitian inverse-Fourier lemma componentwise builds a *real* Schwartz velocity in the canonical carrier, with an exactly recovered, reindexed Fourier spectrum. Finite-sum reindexing preserves Fourier incompressibility, and injectivity of Fourier transformation on Schwartz space establishes **physical divergence zero**.

Theorems target no PDE solution and introduce no existence premise for the real velocity: it is constructed directly. In particular, identifying the *integrated* six-order kernel across the two carriers requires a product-volume change-of-variables proof and is deliberately not claimed here; the next step combines that change of variables with the existing cyclic integral and physical first-monomial identity.

# Physical 243-slot first-monomial spatial-dilation theorem

**Baseline:** `b2c2dc9f` (`prove physical Point3 Schwartz dilation and incompressibility`).

The previous checkpoints supply (1) an actual positive spatial Schwartz dilation,
(2) exact directional derivative scaling through order four, (3) the
three-dimensional change-of-variables Jacobian on the real Euclidean carrier,
(4) the full H3 derivative-energy sums, and (5) the commuting physical Point3
realization and preservation of physical divergence.

This module addresses the previously separate cubic first-monomial identity.
The original `lowNormalRealSchwartzPoint3Monomial` is the finite sum over all
five indices `j,r,i,k,l` in `Axis Depth.three`. It has 3^5 = 243 slots,
retaining `spatialEnergyPairing`'s factor 2 and its sign.

Each slot contains exactly three differentiated velocity factors of orders
3, 2, and 2. Applied to `f_scale(x) = f(scale*x)`, the factors give
`scale^3 * scale^2 * scale^2 = scale^7`. The actual physical three-dimensional
Jacobian gives `scale^(-3)`. Hence for positive scale

    M(f_scale) = scale^4 * M(f).

The argument transports a real Schwartz triple integral through the already
proved `lowNormalH3Fourier_integral_comp_positive_smul` identity, then uses
the existing exact Point3 triple-product pairing and a finite-sum distributivity
step. No path, PDE, Fourier cancellation, solenoidality or concentration
assumption is required for the equality itself.

The result is **not** a Navier--Stokes nonextension theorem. It completes the
spatial-dilation homogeneity ingredient of the critical-half analysis; a
uniform sharp endpoint bound across all Schwartz profiles remains a separate
analytic problem.

## Verification

Run `lake env lean` on the new module, `lake build`, the source index and
fragment checks, and `lake env lean tools/audit/FirstMonomialTriad.lean`.
The archive was syntax-/integrity-reviewed but cannot be Lean-compiled in the
packaging environment. No `sorry`, `admit` or new axioms were added.

## Correction to the initial patch

The initial Lean check reported a rewrite mismatch because the monomial slot
contained `lowNormalSchwartzVelocityDilation scale hscale f j`, whereas the
three- and two-derivative scaling theorems are stated for
`lowNormalSchwartzDilation scale hscale (f j)`. Immediately after expanding
the Point3 triple pairing, the proof now explicitly simplifies the
componentwise velocity dilation definition. The helper lemma's `ring` was
also redundant after `field_simp`, so it was removed. Neither correction
changes the theorem statements or the seven-derivative/Jacobian argument.

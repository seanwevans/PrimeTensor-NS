# Actual H³ signed interpolation versus canonical Schwartz completion

Checkpoint: `76f18591` (`master`).

The old physical signed scalar is already identified with the complete sum of 243 genuine 3–2–2 spatial products, each integrable through L² × L⁴ × L⁴. The spectral completion supplies the same Schwartz family, with third-order jets converging strongly in L² and second-order jets converging strongly in L⁴. This increment makes the remaining scalar-limit argument precise.

For three Lp classes, form the first bounded map L⁴ × L⁴ → L² by Hölder, then the continuous bilinear pairing L² × L² → ℝ. Their composition is continuous and evaluates to the actual signed integral ∫ A(x) (B(x)C(x)) dx. The Lean development proves sequential continuity without assuming a finite-volume carrier or pointwise convergence.

For each ordered index `(j,r,i,k,l)`, evaluate the Schwartz third derivative in L² and the second and cross derivatives in L⁴. The third-jet identification theorem plus continuity of `matchedSpectralThirdFourierJets244` supplies its physical L² limit. `weightedH3CanonicalSecondJetL4Trace_tendsto244` provides both L⁴ limits. The continuous trilinear functional therefore yields precisely `h3CanonicalSignedFirstMonomialSlotIntegral244 hFourier j r i k l`.

Pass to the limit through five *finite* axis sums, retaining the exact normalization `2`, and use `lowNormalRealSchwartz_firstMonomial_eq_twice_slotSum` to recover the same Schwartz scalar already converging to `weightedH3CanonicalSignedFirstMonomial244`. Uniqueness of real sequential limits, together with `h3PathCanonicalFirstMonomialAggregate_eq_canonicalSecondL4Integral244`, gives the unconditional snapshot equality

```
h3PathCanonicalFirstMonomialAggregateAt u t =
  weightedH3CanonicalSignedFirstMonomial244
    (velocityH3SpectralStateAt u t hInt hMeas hFourier)
```

The derived subtraction-gap is exactly zero. This is a signed equality, **not** a cancellation or favorable-sign result, and does not close the separate gradient-transport discrepancy or Navier–Stokes global regularity.

## Audit

The accompanying registrar adds every exported theorem and the new functional definition to the existing `#check`/`#print axioms` ledger, keeps imports before declarations, and preserves original `PrimeTensor.lean` layout. No `sorry`, `admit`, axioms, or compile-time exemptions are added. Lean compilation is to be performed with the repository's own pinned mathlib revision.

# Physical angular Gram determinant — 896e4219

The preceding commit proves the actual physical L² normalized velocity derivative
`N' = E⁻¹ᐟ² Q` with source `R`, energy `E=‖U‖²`, and genuine dissipation
`D=-⟪U,R⟫`.

This checkpoint packages the *scalar Gram defect*

```
Δ(t) = E(t) ‖R(t)‖² - D(t)².
```

For `0<t<T` and `E(t)>0` it proves the exact pointwise identities

```
Δ(t) = E(t) ‖Q(t)‖² = E(t)² ‖N'(t)‖² ≥ 0.
```

It also identifies the equality case: Δ=0 iff Q=0 iff R is purely
longitudinal iff N'=0 at that instant. These statements follow from the
committed Pythagorean physical source decomposition and the genuine Hilbert
momentum derivative, without a standalone assumption about pressure or any
unproved endpoint regularity.

Mathematical significance: unlike `D` alone, Δ measures *directional* source
activity, independent of the kinetic-energy loss. It is the Hilbert-space
Gram determinant `‖U‖² ‖R‖² - ⟪U,R⟫²`, avoiding spurious 3D cross products.
This makes Δ a concrete scalar candidate for comparison with the signed H³
transport and radial/spectral concentration witnesses.

**Limitations:** E>0 is essential for normalized direction. No terminal
integrability of the Gram defect or transverse action is claimed; endpoint
strong L² convergence and smooth H³ continuation are distinct questions.

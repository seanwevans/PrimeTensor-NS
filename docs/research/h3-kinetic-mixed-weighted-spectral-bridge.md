# Weighted-H³ representatives pay the mixed sixth-flux Young moments

**Parent commit:** `574927e01427039a654c0ce9173740781295e77c` — derive asymmetric mixed Fourier Young bounds for native sixth flux.

## Actual three-component Fourier amplitudes

For a complex Schwartz vector `v`, set

```
P_v(ξ) = h3SchwartzTriadPolarization v (WithLp.ofLp ξ)
a_v(ξ) = h3TriadPolarizationNorm (P_v(ξ)).
```

The new Lean bridge explicitly identifies `a_v` with the previously proved
`h3TriadSpectralAmplitude v`. Given **genuine** weighted-H³ spectral
representatives `G_j = W₃ 𝓕(v_j)` almost everywhere, the repo's scalar
Plancherel/deweighting interfaces yield

```
∫ a_v² dξ ≤ Σ_j ‖G_j‖²,
∫ a_v  dξ ≤ C₀ Σ_j ‖G_j‖,
C₀ = h3SobolevDeweightingConstant.
```

The second estimate follows from the project's *actual* `L¹` Hölder
representative and the Euclidean-vector versus coordinate-sum inequality.
It is not an appeal to the false inclusion `L²(ℝ³) ⊂ L¹(ℝ³)`.

With `‖G_j‖ ≤ K` for all three components, the exact estimates reduce to

```
∫ a_v² ≤ 3 K²,       ∫ a_v ≤ 3 C₀ K.
```

## Three genuinely mixed inputs

For independent Schwartz vectors `v,w,h`, represented by three independent
weighted-H³ spectral vectors with coordinate ceilings `K_v,K_w,K_h`, the
previous true low-maximum flux/Young theorem now yields, for each `scale>0`,

```
∫_LowMax(R) |F₆(P_v,P_w,P_h)|
  ≤ 9 [2(R+1)]⁷
      * (scale²·3K_v² + scale⁻²·3K_h²)/2
      * (3C₀K_w).
```

The coefficient is in the existing Euclidean/physical frequency convention.
No phases have been modified: `F₆` is the exact, genuinely complex trilinear
sixth-power symbol. The reciprocal scale can be selected after the relative
size of outer spectral inputs is known.

## Frontier: mixed six-dimensional integrability

The last theorem still explicitly assumes global integrability of the
**mixed unsigned contraction budget** and integrability of the **mixed
sixth-power flux restricted to LowMax(R)**. They are not inferred merely from
weighted-H³ convergence. Establishing them automatically for three independent
Schwartz Fourier profiles, then transferring the result to two physical
snapshots and their difference, is the next mathematical step. Only then can
the physical low-band PDE freezing control the signed low-maximum transport.

There is no claim of a terminal-uniform H³ bound or Navier–Stokes continuation.

## Direct native vector-state corollary

The companion `thirdFullKineticWeightedSchwartz_velocityMoments_le244` applies
the finite-vector coordinate norm bound to replace the three coordinate
ceilings by `‖V‖` itself. The final
`thirdFullKinetic_lowMax_mixedSchwartzFlux_le_spectralVelocities244` similarly
states the mixed estimate directly with the THREE independent actual
`H3SpectralVelocityState` norms `‖V‖`, `‖W‖`, `‖H‖`. This is the interface for
the genuine solenoidal Schwartz recovery already implemented in the repo.

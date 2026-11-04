# Physical H³ jet energies and the signed quartic transport barrier

**Baseline:** `b6cbef2d` (`realize physical H3 PDE transport along solenoidal Schwartz density`).

## Scope

`FullThirdPhysicalJetEnergyQuarticBridge.lean` identifies the previously
constructed weighted-spectral quadratic/cubic energies with the original
physical-order energies. It then transports the existing signed 243-slot
quartic inequality to an actual Fourier-compatible physical H³ time slice.

The proof uses no new smoothing, Schwartz-realization, solenoidal, or sign
assumptions. It *does* require the usual `VelocityH3FourierCompatibleAt` for
the actual jet equality, and the path-class hypotheses for the interpolation
multiplicity-three identity.

## Exact energy identifications

The previous matched solenoidal density proved `E₂(Ψ_n)=E₂^can(V_n)` and
`E₃(Ψ_n)=E₃^can(V_n)`. The missing exact physical equalities are:

- `thirdFullPhysical_canonicalSecondJetEnergy_eq244`: for an encoded
  Fourier-compatible H³ velocity `U(t)`, `E₂^can(U(t)) = velocityH3Energy2At u t`.
- `thirdFullPhysical_canonicalThirdJetEnergy_eq244`: likewise
  `E₃^can(U(t)) = velocityH3Energy3At u t`.

The proof uses the exact 27/81 physical `L²` jet reconstruction, the isometry
`norm_h3ToFourierRealL2`, the `Fin 3` to `Axis Depth.three` reindexing lemmas,
and the actual physical jet square-energy equalities. **No coercivity or norm
comparison constant appears in either identity.**

## Physical quartic inequality

`thirdFullPhysical_signedMonomial_quarticEnergyBound244` proves

    |M_phys(u,t)|^4 <= K^4 E₂_phys(u,t) E₃_phys(u,t)^5,

with the preexisting `lowNormalRealSchwartz_holder244CriticalConstant` and
physical signed monomial `h3PathCanonicalFirstMonomialAggregateAt`.

`thirdFullPhysical_interpolationTransport_quarticEnergyBound244` uses the
already proved exact cyclic multiplicity three to give

    |I₃_phys(u,t)|^4 <= 3^4 K^4 E₂_phys(u,t) E₃_phys(u,t)^5.

The inequality constrains the interpolation contribution but does not
control its sign or imply viscosity absorption. In particular, it does not
close the separate longitudinal flux or terminal-energy obstruction.

## Verification

The registration audit checks each public declaration and prints Lean axioms.
Local static/archive validation is not Lean elaboration or kernel verification;
run `lake env lean` and `lake build` against the baseline repository.

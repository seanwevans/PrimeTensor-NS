import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedMonomialSymmetry

/-!
# Cyclic mixed-partial symmetry of all three signed H³ interpolation monomials

The preceding file established the exact identity between monomial types 0 and
1 after interchanging the first two third-derivative indices. Here spatial C³
regularity and equality of mixed partials also identify type 2 with type 0:

  P₂(j,i,k,l,r) = P₀(j,l,i,k,r).

Unlike a bound on absolute values, this is an equality of genuine signed
spatial-energy pairings. The third-derivative factor is invariant under a cyclic
permutation of its indices, and the two second-derivative factors agree after
one ordinary mixed-partial interchange. Thus every previously extracted signed
monomial witness can be represented within a single type-0 family of 3⁵ = 243
formal ordered index slots. The 1/729 witness threshold is unchanged; no
new cancellation estimate or unconditional continuation is proved.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

/-- Third-derivative cyclic symmetry identifies signed interpolation type 2
with signed type 0 after `(i,k,l) ↦ (l,i,k)`. The second derivative of the
velocity component also commutes its two coordinate partials. -/
theorem h3PathCanonical_thirdMonomial_eq_firstMonomial_cyclic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i k l r : PrimeTensor.Axis Depth.three) :
    h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2 =
      h3PathCanonicalInterpolationMonomialPairing u t j l i k r 0 := by
  obtain ⟨p, s, hp4⟩ := hClass.pressure_witness
  have htNS : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hC3 : SpatialC3 (loggedVelocityComponent u t j) := by
    change SpatialC3
      (fun x : Point3 =>
        (PrimeTensor.Bridge.logSpaceTimeVectorField u t x).component j)
    exact s.regularity.velocity_spatial_three t htNS j
  have hC2 : SpatialC2 (loggedVelocityComponent u t j) :=
    SpatialC3.toSpatialC2 hC3
  have hInner :
      spatial3.d k (spatial3.d l (loggedVelocityComponent u t j)) =
        spatial3.d l (spatial3.d k (loggedVelocityComponent u t j)) := by
    funext x
    exact hC2.spatial_d_comm x k l
  have hFirstC2 :
      SpatialC2 (spatial3.d k (loggedVelocityComponent u t j)) := by
    change SpatialC2
      (fun x => partialDeriv k (loggedVelocityComponent u t j) x)
    exact SpatialC3.partialDeriv_contDiff_two hC3 k
  have hCyclic :
      spatial3.d i (spatial3.d k
        (spatial3.d l (loggedVelocityComponent u t j))) =
      spatial3.d l (spatial3.d i
        (spatial3.d k (loggedVelocityComponent u t j))) := by
    rw [hInner]
    funext x
    exact hFirstC2.spatial_d_comm x i l
  have hProduct :
      thirdOrderInterpolationMonomial3 u t i k l j r =
        thirdOrderInterpolationMonomial1 u t l i k j r := by
    funext x
    change
      spatial3.d i (spatial3.d k (loggedVelocityComponent u t r)) x *
          spatial3.d r (spatial3.d l (loggedVelocityComponent u t j)) x =
        spatial3.d i (spatial3.d k (loggedVelocityComponent u t r)) x *
          spatial3.d l (spatial3.d r (loggedVelocityComponent u t j)) x
    exact congrArg
      (fun z : ℝ =>
        spatial3.d i (spatial3.d k (loggedVelocityComponent u t r)) x * z)
      (hC2.spatial_d_comm x r l)
  change
    spatialEnergyPairing
      (spatial3.d i (spatial3.d k
        (spatial3.d l (loggedVelocityComponent u t j))))
      (thirdOrderInterpolationMonomial3 u t i k l j r) =
    spatialEnergyPairing
      (spatial3.d l (spatial3.d i
        (spatial3.d k (loggedVelocityComponent u t j))))
      (thirdOrderInterpolationMonomial1 u t l i k j r)
  rw [hCyclic, hProduct]

/-- A lower bound for one signed monomial family automatically controls the
third monomial by cyclic reindexing of its actual physical pairing. -/
theorem h3PathCanonical_thirdMonomial_lower_of_firstMonomial_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t B : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hFirst : ∀ j i k l r : PrimeTensor.Axis Depth.three,
      B ≤ h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0)
    (j i k l r : PrimeTensor.Axis Depth.three) :
    B ≤ h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2 := by
  rw [h3PathCanonical_thirdMonomial_eq_firstMonomial_cyclic
    hClass ht j i k l r]
  exact hFirst j l i k r

/-- No independent type-1 or type-2 signed witness is needed: every one of
the nine real triple products in one coordinate pairing is a reindexed
instance of a type-0 triple product. -/
theorem h3PathCanonical_signedMonomial_first_only
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t B : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hWitness : ∃ j i k l r : PrimeTensor.Axis Depth.three,
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 < B ∨
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 < B ∨
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2 < B) :
    ∃ j i k l r : PrimeTensor.Axis Depth.three,
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 < B := by
  obtain ⟨j, i, k, l, r, hBad⟩ :=
    h3PathCanonical_signedMonomial_first_or_third hClass ht hWitness
  rcases hBad with hFirst | hThird
  · exact ⟨j, i, k, l, r, hFirst⟩
  · refine ⟨j, l, i, k, r, ?_⟩
    rw [← h3PathCanonical_thirdMonomial_eq_firstMonomial_cyclic
      hClass ht j i k l r]
    exact hThird

/-- The original physical signed transport adversity forces a genuine type-0
triple-product pairing below precisely the previously established 1/729
budget, without any extra gradient-absorption hypothesis. -/
theorem h3PathCanonical_signedAdversity_forces_firstMonomial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    ∃ j i k l r : PrimeTensor.Axis Depth.three,
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          velocityH3DissipationAt u t - M * velocityH3EnergyAt u t) / 729 := by
  exact h3PathCanonical_signedMonomial_first_only hClass ht
    (h3PathCanonical_signedAdversity_forces_explicitMonomial
      hH3 hClass ht hAdverse)

/-- If hypothetical nonextension occurs while the explicit gradient block
is absorbed by full dissipation on a strict terminal tail, arbitrarily late
witnesses can be represented *only* by type-0 triple products. -/
theorem h3PathCanonical_firstMonomial_witness_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R)
    (hAbsorption : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
          velocityH3DissipationAt u t) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ j i k l r : PrimeTensor.Axis Depth.three,
        h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 <
          -R * velocityH3EnergyAt u t := by
  obtain ⟨t, ht, j, i, k, l, r, hBad⟩ :=
    h3PathCanonical_twoMonomialTypes_witness_of_noExtension
      hH3 hNoExtension hClass hb hd hR hAbsorption
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  rcases hBad with hFirst | hThird
  · exact ⟨t, ht, j, i, k, l, r, hFirst⟩
  · refine ⟨t, ht, j, l, i, k, r, ?_⟩
    rw [← h3PathCanonical_thirdMonomial_eq_firstMonomial_cyclic
      hClass htClass j i k l r]
    exact hThird

/-- It suffices to bound only the type-0 signed physical triple-product
family. Both other families follow from exact mixed-partial identities. -/
theorem h3PathCanonical_extension_of_firstMonomialLowerBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R)
    (hAbsorption : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
          velocityH3DissipationAt u t)
    (hLower : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∀ j i k l r : PrimeTensor.Axis Depth.three,
        -R * velocityH3EnergyAt u t ≤
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, j, i, k, l, r, hBad⟩ :=
    h3PathCanonical_firstMonomial_witness_of_noExtension
      hH3 hNoExtension hClass hb hd hR hAbsorption
  exact (not_lt_of_ge (hLower t ht j i k l r)) hBad

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedInterpolationMonomial

/-!
# Mixed-partial symmetry removes an independent signed interpolation monomial

The existing physical interpolation commutator contains three monomial types
for every five-index tuple `(j,i,k,l,r)`.  The first two are not independent:

  P₁(j,i,k,l,r) = P₂(j,k,i,l,r).

The pointwise second-derivative products coincide *definitionally* when the
outer derivative indices are interchanged.  The third-derivative pairing factor
coincides by the proved `SpatialC2.spatial_d_comm` applied to the first
partial of a spatially `C³` velocity component.  No integration by parts,
absolute value estimate, or new analytic hypothesis enters this equality.

Consequently the physical signed nonextension witness can always be realized
by monomial type 1 or type 3 (Fin indices `0` or `2`).  Under the previously
stated *additional* gradient-absorption condition, hypothetical nonextension
forces arbitrarily negative normalized examples among those two types; a
uniform lower bound on only these two types then suffices for continuation.

This proves an exact index symmetry, not a cancellation between the two
remaining types and not unconditional continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

/-- The genuine signed type-1 and type-2 triple-product pairings are the
same physical integral after swapping the two outer third-derivative indices.
The required mixed-partial symmetry follows from the existing preterminal
Navier--Stokes `SpatialC3` regularity. -/
theorem h3PathCanonical_firstMonomial_eq_secondMonomial_swapped
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i k l r : PrimeTensor.Axis Depth.three) :
    h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 =
      h3PathCanonicalInterpolationMonomialPairing u t j k i l r 1 := by
  obtain ⟨p, s, hp4⟩ := hClass.pressure_witness
  have htNS : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hC3 : SpatialC3 (loggedVelocityComponent u t j) := by
    change SpatialC3
      (fun x : Point3 =>
        (PrimeTensor.Bridge.logSpaceTimeVectorField u t x).component j)
    exact s.regularity.velocity_spatial_three t htNS j
  have hC2 : SpatialC2
      (spatial3.d l (loggedVelocityComponent u t j)) := by
    change SpatialC2
      (fun x => partialDeriv l (loggedVelocityComponent u t j) x)
    exact SpatialC3.partialDeriv_contDiff_two hC3 l
  have hSwap :
      spatial3.d i (spatial3.d k
        (spatial3.d l (loggedVelocityComponent u t j))) =
      spatial3.d k (spatial3.d i
        (spatial3.d l (loggedVelocityComponent u t j))) := by
    funext x
    exact hC2.spatial_d_comm x i k
  change
    spatialEnergyPairing
      (spatial3.d i (spatial3.d k
        (spatial3.d l (loggedVelocityComponent u t j))))
      (thirdOrderInterpolationMonomial1 u t i k l j r) =
    spatialEnergyPairing
      (spatial3.d k (spatial3.d i
        (spatial3.d l (loggedVelocityComponent u t j))))
      (thirdOrderInterpolationMonomial1 u t i k l j r)
  exact congrArg
    (fun f : ScalarField3 =>
      spatialEnergyPairing f
        (thirdOrderInterpolationMonomial1 u t i k l j r)) hSwap

/-- A lower bound for type 1 automatically controls the swapped type 2.
It is enough to inspect 486 rather than 729 formally distinct signed slots. -/
theorem h3PathCanonical_secondMonomial_lower_of_firstMonomial_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t B : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hFirst : ∀ j i k l r : PrimeTensor.Axis Depth.three,
      B ≤ h3PathCanonicalInterpolationMonomialPairing
        u t j i k l r 0)
    (j i k l r : PrimeTensor.Axis Depth.three) :
    B ≤ h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 := by
  rw [← h3PathCanonical_firstMonomial_eq_secondMonomial_swapped
    hClass ht j k i l r]
  exact hFirst j k i l r

/-- A signed witness in one of the three monomial types can be reoriented
into type 1 or 3 only: type 2 is a permutation of type 1.  This is a
physical mixed-partial identity, not a pigeonhole inequality. -/
theorem h3PathCanonical_signedMonomial_first_or_third
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t B : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hWitness : ∃ j i k l r : PrimeTensor.Axis Depth.three,
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 < B ∨
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 < B ∨
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2 < B) :
    ∃ j i k l r : PrimeTensor.Axis Depth.three,
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 < B ∨
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2 < B := by
  obtain ⟨j, i, k, l, r, hBad⟩ := hWitness
  rcases hBad with hFirst | hSecond | hThird
  · exact ⟨j, i, k, l, r, Or.inl hFirst⟩
  · have hSwap := h3PathCanonical_firstMonomial_eq_secondMonomial_swapped
      hClass ht j k i l r
    exact ⟨j, k, i, l, r, Or.inl (by simpa only [hSwap] using hSecond)⟩
  · exact ⟨j, i, k, l, r, Or.inr hThird⟩

/-- The *unconditional-on-gradient-absorption* adverse transport reduction
can always choose a monomial of type 1 or 3, with the same 1/729 threshold
as the previously established fully expanded witness. -/
theorem h3PathCanonical_signedAdversity_forces_twoMonomialTypes
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
          velocityH3DissipationAt u t - M * velocityH3EnergyAt u t) / 729 ∨
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2 <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          velocityH3DissipationAt u t - M * velocityH3EnergyAt u t) / 729 := by
  exact h3PathCanonical_signedMonomial_first_or_third hClass ht
    (h3PathCanonical_signedAdversity_forces_explicitMonomial
      hH3 hClass ht hAdverse)

/-- Assuming gradient absorption on a strict tail, hypothetical nonextension
forces arbitrarily negative normalized type-1 or type-3 monomial pairings.
Type 2 is never needed as a separate witness family. -/
theorem h3PathCanonical_twoMonomialTypes_witness_of_noExtension
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
          -R * velocityH3EnergyAt u t ∨
        h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2 <
          -R * velocityH3EnergyAt u t := by
  obtain ⟨t, ht, j, i, k, l, r, hBad⟩ :=
    h3PathCanonical_signedMonomial_witness_of_noExtension
      hH3 hNoExtension hClass hb hd hR hAbsorption
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  obtain ⟨j', i', k', l', r', hBad'⟩ :=
    h3PathCanonical_signedMonomial_first_or_third hClass htClass
      ⟨j, i, k, l, r, hBad⟩
  exact ⟨t, ht, j', i', k', l', r', hBad'⟩

/-- Two typewise lower bounds now suffice: the type-2 lower bound follows
from type 1 by mixed-partial symmetry. The gradient-absorption hypothesis
remains explicit, and the result does not claim unconditional regularity. -/
theorem h3PathCanonical_extension_of_twoMonomialTypeLowerBounds
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
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 ∧
        -R * velocityH3EnergyAt u t ≤
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, j, i, k, l, r, hBad⟩ :=
    h3PathCanonical_twoMonomialTypes_witness_of_noExtension
      hH3 hNoExtension hClass hb hd hR hAbsorption
  rcases hBad with hFirst | hThird
  · exact (not_lt_of_ge (hLower t ht j i k l r).1) hFirst
  · exact (not_lt_of_ge (hLower t ht j i k l r).2) hThird

end Euclidean
end Bridge
end PrimeTensor

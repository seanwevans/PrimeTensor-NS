import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopInterpolationFrontier
import PrimeTensor.Fluid.Vorticity.H3.Axis.Sum

/-!
# Extract an actual signed coordinate pairing from the third-order interpolation block

The earlier exact PDE identity writes the top nonlinear transport as G3+I3,
where G3 is the controlled gradient commutator and I3 is the sum of genuine
third-derivative / second-derivative-product spatial pairings. The latter is
not an unspecified scalar: it sums four ordered indices, each over the three
Euclidean axes, and thus exactly 81 signed coordinate pairings.

An elementary finite pigeonhole argument says that if I3 < 81 B, one of its
81 physical pairings is strictly below B. Apply this to the signed physical
nonextension deficit

  I3 < 24*C1*sqrt(E)*E3 - D - M*E.

Without extra hypotheses, this produces a selected coordinate pairing below
the corresponding signed residual divided by 81. If dissipation absorbs the
24-gradient allowance on a terminal tail, it further gives, for every R>=0,
selected late times and coordinates with

  coordinatePairing < -R*E.

Conversely, a uniform normalized lower bound for all 81 pairings together
with gradient absorption on a strict terminal tail implies continuation.
Neither the gradient-absorption condition nor that lower bound is asserted
unconditionally. No new PDE sign cancellation is assumed or proved.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable local instance axisFintypeH3SignedInterpolationCoordinate
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A constant summed over the four ordered three-dimensional indices is
exactly 81 copies of that constant. -/
private theorem h3PathCanonical_fourAxis_constant_sum
    (B : ℝ) :
    (∑ _j : PrimeTensor.Axis Depth.three,
      ∑ _i : PrimeTensor.Axis Depth.three,
        ∑ _k : PrimeTensor.Axis Depth.three,
          ∑ _l : PrimeTensor.Axis Depth.three, B) = 81 * B := by
  simp_rw [axis_sum_three]
  ring

/-- Finite pigeonhole extraction for the 81 actual coordinate slots;
no positivity assumption on the threshold is required. -/
theorem h3PathCanonical_fourAxis_exists_lt_of_sum_lt
    (f : PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three → ℝ)
    (B : ℝ)
    (hSum :
      (∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three, f j i k l) < 81 * B) :
    ∃ j i k l : PrimeTensor.Axis Depth.three, f j i k l < B := by
  classical
  by_contra hNone
  have hEvery (j i k l : PrimeTensor.Axis Depth.three) :
      B ≤ f j i k l := by
    apply le_of_not_gt
    intro hBad
    exact hNone ⟨j, i, k, l, hBad⟩
  have hLower :
      (∑ _j : PrimeTensor.Axis Depth.three,
        ∑ _i : PrimeTensor.Axis Depth.three,
          ∑ _k : PrimeTensor.Axis Depth.three,
            ∑ _l : PrimeTensor.Axis Depth.three, B) ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three, f j i k l := by
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro k hk
    apply Finset.sum_le_sum
    intro l hl
    exact hEvery j i k l
  rw [h3PathCanonical_fourAxis_constant_sum B] at hLower
  exact (not_lt_of_ge hLower) hSum

/-- One genuine physical signed spatial pairing in the 81-slot third-order
interpolation commutator. This is not its absolute value or a majorant. -/
noncomputable def h3PathCanonicalInterpolationCoordinatePairing
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (j i k l : PrimeTensor.Axis Depth.three) : ℝ :=
  spatialEnergyPairing
    (spatial3.d i
      (spatial3.d k
        (spatial3.d l (loggedVelocityComponent u t j))))
    (thirdTransportCommutatorInterpolationBlock
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j)

/-- Identify the genuine interpolation block with the signed coordinate
sum, without replacing any term by an absolute value. -/
theorem h3PathCanonical_interpolation_eq_sum_coordinatePairings
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    thirdOrderInterpolationTransportSum u t =
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              h3PathCanonicalInterpolationCoordinatePairing u t j i k l := by
  rfl

/-- A strict upper bound on the full *signed* interpolation transport
forces one actual coordinate pairing strictly below its 1/81 share. -/
theorem h3PathCanonical_interpolation_coordinate_lt_of_sum_lt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t B : ℝ)
    (hI : thirdOrderInterpolationTransportSum u t < 81 * B) :
    ∃ j i k l : PrimeTensor.Axis Depth.three,
      h3PathCanonicalInterpolationCoordinatePairing u t j i k l < B := by
  rw [h3PathCanonical_interpolation_eq_sum_coordinatePairings] at hI
  exact h3PathCanonical_fourAxis_exists_lt_of_sum_lt
    (h3PathCanonicalInterpolationCoordinatePairing u t) B hI

/-- The signed physical deficit is localized to one of the 81 coordinate
pairings, whenever the requested coordinate threshold covers that deficit.
This is unconditional on any gradient-absorption assumption. -/
theorem h3PathCanonical_signedAdversity_forces_coordinateDeficit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t)
    (hBudget :
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          velocityH3DissipationAt u t - M * velocityH3EnergyAt u t ≤
        81 * B) :
    ∃ j i k l : PrimeTensor.Axis Depth.three,
      h3PathCanonicalInterpolationCoordinatePairing u t j i k l < B := by
  have hDeficit := h3PathCanonical_signedAdversity_forces_interpolationDeficit
    hH3 hClass ht hAdverse
  have hI : thirdOrderInterpolationTransportSum u t < 81 * B := by
    linarith only [hDeficit, hBudget]
  exact h3PathCanonical_interpolation_coordinate_lt_of_sum_lt u t B hI

/-- At *every* genuine signed top-transport witness there is an actual
coordinate pairing below one eighty-first of the remaining physical
interpolation budget. This requires no gradient-absorption hypothesis. -/
theorem h3PathCanonical_signedAdversity_forces_explicit_coordinateDeficit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    ∃ j i k l : PrimeTensor.Axis Depth.three,
      81 * h3PathCanonicalInterpolationCoordinatePairing u t j i k l <
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          velocityH3DissipationAt u t - M * velocityH3EnergyAt u t := by
  let Q : ℝ :=
    24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
      velocityH3DissipationAt u t - M * velocityH3EnergyAt u t
  have hBudget :
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
        velocityH3DissipationAt u t - M * velocityH3EnergyAt u t ≤
      81 * (Q / 81) := by
    change Q ≤ 81 * (Q / 81)
    rw [show (81 : ℝ) * (Q / 81) = Q by ring]
  obtain ⟨j, i, k, l, hPair⟩ :=
    h3PathCanonical_signedAdversity_forces_coordinateDeficit
      (B := Q / 81) hH3 hClass ht hAdverse hBudget
  refine ⟨j, i, k, l, ?_⟩
  change 81 * h3PathCanonicalInterpolationCoordinatePairing u t j i k l < Q
  calc
    81 * h3PathCanonicalInterpolationCoordinatePairing u t j i k l <
        81 * (Q / 81) :=
      mul_lt_mul_of_pos_left hPair (by norm_num)
    _ = Q := by ring

/-- Hypothetical nonextension forces a concrete coordinate-level signed
interpolation deficit arbitrarily late, without assuming that the separate
gradient commutator has already been absorbed. -/
theorem h3PathCanonical_explicit_coordinateDeficit_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ j i k l : PrimeTensor.Axis Depth.three,
        81 * h3PathCanonicalInterpolationCoordinatePairing u t j i k l <
          24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
            velocityH3DissipationAt u t - M * velocityH3EnergyAt u t := by
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hM
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  exact ⟨t, ht,
    h3PathCanonical_signedAdversity_forces_explicit_coordinateDeficit
      hH3 hClass htClass hAdverse⟩

/-- With a physically realized gradient absorption at the adverse instant,
one of the 81 interpolation coordinate pairings must have negative
normalized size exceeding a prescribed nonnegative rate. -/
theorem h3PathCanonical_interpolation_coordinate_adverse_of_gradientAbsorption
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAdverse :
      (81 * R) * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t)
    (hAbsorption :
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
          velocityH3DissipationAt u t) :
    ∃ j i k l : PrimeTensor.Axis Depth.three,
      h3PathCanonicalInterpolationCoordinatePairing u t j i k l <
        -R * velocityH3EnergyAt u t := by
  have hInterp := h3PathCanonical_signedInterpolation_adverse_of_gradientAbsorption
    hH3 hClass ht hAdverse hAbsorption
  have hI : thirdOrderInterpolationTransportSum u t <
      81 * (-R * velocityH3EnergyAt u t) := by
    nlinarith only [hInterp]
  exact h3PathCanonical_interpolation_coordinate_lt_of_sum_lt
    u t (-R * velocityH3EnergyAt u t) hI

/-- Under a tail-wide *explicit* gradient-absorption hypothesis,
hypothetical nonextension forces an arbitrarily adverse normalized signed
interpolation coordinate pairing on every later strict subtail. -/
theorem h3PathCanonical_interpolation_coordinate_witness_of_noExtension
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
      ∃ j i k l : PrimeTensor.Axis Depth.three,
        h3PathCanonicalInterpolationCoordinatePairing u t j i k l <
          -R * velocityH3EnergyAt u t := by
  have hM : 0 ≤ 81 * R := by positivity
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hM
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  exact ⟨t, ht,
    h3PathCanonical_interpolation_coordinate_adverse_of_gradientAbsorption
      hH3 hClass htClass hAdverse (hAbsorption t ht)⟩

/-- A tail-wide normalized lower bound on *each* signed interpolation
coordinate pairing, together with gradient absorption, excludes the exact
coordinate witness and hence yields smooth continuation. -/
theorem h3PathCanonical_extension_of_coordinateInterpolationLowerBound
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
      ∀ j i k l : PrimeTensor.Axis Depth.three,
        -R * velocityH3EnergyAt u t ≤
          h3PathCanonicalInterpolationCoordinatePairing u t j i k l) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, j, i, k, l, hBad⟩ :=
    h3PathCanonical_interpolation_coordinate_witness_of_noExtension
      hH3 hNoExtension hClass hb hd hR hAbsorption
  exact (not_lt_of_ge (hLower t ht j i k l)) hBad

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxAdverseTailEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalHighRadialViscousCoercivity
import Mathlib.Tactic

/-!
# Adverse signed low-maximum sixth flux: genuine physical viscous charge

An adverse signed imaginary sixth-flux excursion in a strict physical gap
previously forced a high-H3 tail at one of the two ACTUAL observation times,
provided the recovery errors and the actual projected momentum source clock
could not pay half the excursion. Here the existing physical high-radial
viscous coercivity charges that SAME observation time to the genuine full
fourth-derivative H3 dissipation.

The theorem is also stated as an unconditional physical alternative: either
the weighted recovery/source charge is large, or an actual observation-time
viscous spike pays the cutoff-squared flux threshold. It assumes neither a
terminal-uniform H3 ceiling nor a lower bound on the duration of a spike.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev VA3 := PrimeTensor.Axis Depth.three
private abbrev VV3 := H3FourierPoint3

noncomputable local instance axisFintypeKineticSignedViscousGate244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Square the actual high-frequency mass charge and then use the exact
physical H3 fourth-derivative dissipation. The axis carrier uses the sup
norm, so the imported coercivity theorem is necessary. -/
private theorem thirdFullKinetic_signedLowMax_tailCharge_to_viscous244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (η A : ℝ) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hTail : η / 4 ≤ A *
      ‖thirdFullSpectralVelocityHighRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)‖) :
    ((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2 ≤
      A ^ 2 * velocityH3DissipationAt u t := by
  have hSquare : (η / 4) ^ 2 ≤
      (A * ‖thirdFullSpectralVelocityHighRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)‖) ^ 2 :=
    (sq_le_sq₀ (div_nonneg hη (by norm_num))
      (mul_nonneg hA (norm_nonneg _))).mpr hTail
  have hViscous := thirdFullPhysical_fullViscousCoercivity244
    hH3 hClass t ht R
  calc
    ((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2 ≤
        ((R : ℝ) + 1) ^ 2 *
          (A * ‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hSquare (sq_nonneg _)
    _ = A ^ 2 * (((R : ℝ) + 1) ^ 2 *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) := by ring
    _ ≤ A ^ 2 * velocityH3DissipationAt u t :=
      mul_le_mul_of_nonneg_left hViscous (sq_nonneg _)

/-- A *genuine* adverse signed sixth-flux increment forces a physical
three-way alternative at the ORIGINAL two strict gap observation times.
The first branch retains the true physical projected source L1 action and
the two distinct weighted-H3 recovery errors. If it does not pay half the
adverse margin, then either observation time carries an explicit quadratic
H3 viscous spike. There is no assumed H3 uniform bound. -/
theorem thirdFullPhysical_strictGap_signedLowMax_viscousOrClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Icc x y) (ht : t ∈ Set.Icc x y)
    (v w : VA3 → SchwartzMap VV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : VA3,
      (V (h3ClassicalizationFinOfAxis j) : VV3 → ℂ) =ᵐ[volume]
        (fun ξ : VV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : VA3,
      (W (h3ClassicalizationFinOfAxis j) : VV3 → ℂ) =ᵐ[volume]
        (fun ξ : VV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (η : ℝ) (hη : 0 < η)
    (hAdverse : η ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im|) :
    η / 2 < thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
      (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
        thirdFullFiniteBandH3WeightCeiling244 R *
          (∫ r in x..y,
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
        ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖) ∨
    (((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2 ≤
      (thirdFullKineticSignedLowMaxFluxClockWeight244 R V W) ^ 2 *
        velocityH3DissipationAt u t ∨
     ((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2 ≤
      (thirdFullKineticSignedLowMaxFluxClockWeight244 R V W) ^ 2 *
        velocityH3DissipationAt u s) := by
  let A : ℝ := thirdFullKineticSignedLowMaxFluxClockWeight244 R V W
  let E : ℝ :=
    ‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
      thirdFullFiniteBandH3WeightCeiling244 R *
        (∫ r in x..y,
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
      ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖
  have hA : 0 ≤ A := by
    dsimp only [A, thirdFullKineticSignedLowMaxFluxClockWeight244]
    have hC : 0 ≤ h3SobolevDeweightingConstant :=
      h3SobolevDeweightingConstant_nonneg
    positivity
  have hx0 : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hx.1, hx.2⟩
  have hy0 : y ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hy.1, hy.2⟩
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  by_cases hSmall : A * E ≤ η / 2
  · right
    have hTail := thirdFullPhysical_strictGap_signedLowMax_oneHighTail244
      hH3 R x y hx0 hy0 hxy s t hs ht v w V W hv hw
      η hη hAdverse (by simpa only [A, E] using hSmall)
    rcases hTail with hAtT | hAtS
    · left
      exact thirdFullKinetic_signedLowMax_tailCharge_to_viscous244
        hH3 hClass R t htClass η A hη.le hA
        (by simpa only [A] using hAtT)
    · right
      exact thirdFullKinetic_signedLowMax_tailCharge_to_viscous244
        hH3 hClass R s hsClass η A hη.le hA
        (by simpa only [A] using hAtS)
  · left
    change η / 2 < A * E
    exact lt_of_not_ge hSmall

/-- If the recovery and physical PDE clock pay no more than half the signed
margin, the SUM of the physical H3 viscous densities at the two original
gap observation times pays one squared high-frequency charge. The estimate
is pointwise in time: it asserts no unproved persistence width. -/
theorem thirdFullPhysical_strictGap_signedLowMax_twoTimeViscousCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Icc x y) (ht : t ∈ Set.Icc x y)
    (v w : VA3 → SchwartzMap VV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : VA3,
      (V (h3ClassicalizationFinOfAxis j) : VV3 → ℂ) =ᵐ[volume]
        (fun ξ : VV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : VA3,
      (W (h3ClassicalizationFinOfAxis j) : VV3 → ℂ) =ᵐ[volume]
        (fun ξ : VV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (η : ℝ) (hη : 0 < η)
    (hAdverse : η ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im|)
    (hSmall :
      thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
        (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
          thirdFullFiniteBandH3WeightCeiling244 R *
            (∫ r in x..y,
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
          ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖) ≤ η / 2) :
    ((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2 ≤
      (thirdFullKineticSignedLowMaxFluxClockWeight244 R V W) ^ 2 *
        (velocityH3DissipationAt u t + velocityH3DissipationAt u s) := by
  let A : ℝ := thirdFullKineticSignedLowMaxFluxClockWeight244 R V W
  have hAlternative := thirdFullPhysical_strictGap_signedLowMax_viscousOrClock244
    hH3 hClass R x y hx hy hxy s t hs ht v w V W hv hw η hη hAdverse
  have hNot : ¬ η / 2 < A *
      (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
        thirdFullFiniteBandH3WeightCeiling244 R *
          (∫ r in x..y,
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
        ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖) := by
    exact not_lt.mpr hSmall
  rcases hAlternative with hClock | hVisc
  · exact False.elim (hNot hClock)
  · have hsClass : s ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    have hDissS : 0 ≤ velocityH3DissipationAt u s :=
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)).trans
        (thirdFullPhysical_fullViscousCoercivity244
          hH3 hClass s hsClass R)
    have hDissT : 0 ≤ velocityH3DissipationAt u t :=
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)).trans
        (thirdFullPhysical_fullViscousCoercivity244
          hH3 hClass t htClass R)
    rcases hVisc with hAtT | hAtS
    · calc
        ((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2 ≤
            A ^ 2 * velocityH3DissipationAt u t := hAtT
        _ ≤ A ^ 2 *
              (velocityH3DissipationAt u t + velocityH3DissipationAt u s) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hDissS) (sq_nonneg _)
    · calc
        ((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2 ≤
            A ^ 2 * velocityH3DissipationAt u s := hAtS
        _ ≤ A ^ 2 *
              (velocityH3DissipationAt u t + velocityH3DissipationAt u s) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hDissT) (sq_nonneg _)

end
end PrimeTensor.FirstMonomialTriad

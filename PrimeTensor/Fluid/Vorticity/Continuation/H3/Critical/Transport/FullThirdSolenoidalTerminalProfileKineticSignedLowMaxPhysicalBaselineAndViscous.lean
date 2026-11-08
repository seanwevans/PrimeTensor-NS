import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCalibratedGapClock
import Mathlib.Tactic

/-!
# Physical baseline and physical viscous height of the signed LowMax flux

The energy-calibrated gap clock eliminated the Schwartz errors from the source
branch, but left a Schwartz baseline and a Schwartz-dependent viscous height.
The genuinely integrable mixed sixth flux gives a diagonal CUBIC reference
bound. The two recovered H3 states lie within one of their physical states;
thus the reference baseline has an actual physical early-time H3 bound, and
the annular height has a physical lower bound.

The resulting four-way signed replenishment obstruction on the original gap
contains only actual physical states, the projected source and dissipation.
It does NOT say any of the alternatives is impossible at a moving radius.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology FourierTransform
open scoped BigOperators Interval ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev PA3 := PrimeTensor.Axis Depth.three
private abbrev PV3 := H3FourierPoint3

noncomputable local instance axisFintypePhysicalBaseline244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The physical baseline ceiling is CUBIC in the original H3 state norm.
The radial power seven is kept, rather than replaced by an unknown constant. -/
noncomputable def thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244
    (R : ℕ) (Y : H3SpectralVelocityState) : ℝ :=
  (81 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant) *
    (‖Y‖ + 1) ^ 3

/-- The signed LowMax imaginary flux of an exact Schwartz recovery is
bounded by the original physical H3 norm at its reference time. This uses
the native three-profile mixed Fourier bound at unit Young scale: there is
no assumption that the signed LowMax cubic vanishes at the earlier time. -/
theorem thirdFullKinetic_signedLowMax_referenceBaseline_le_physical244
    (R : ℕ) (q : PA3 → SchwartzMap PV3 ℂ)
    (W Y : H3SpectralVelocityState)
    (hq : ∀ j : PA3,
      (W (h3ClassicalizationFinOfAxis j) : PV3 → ℂ) =ᵐ[volume]
        (fun ξ : PV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (q j)) ξ))
    (hNear : ‖Y - W‖ ≤ 1) :
    |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R q).im| ≤
      thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y := by
  have hWBound : ‖W‖ ≤ ‖Y‖ + 1 := by
    have hTriangle : ‖W‖ ≤ ‖Y - W‖ + ‖Y‖ := by
      calc
        ‖W‖ = ‖(W - Y) + Y‖ := by rw [sub_add_cancel]
        _ ≤ ‖W - Y‖ + ‖Y‖ := norm_add_le _ _
        _ = ‖Y - W‖ + ‖Y‖ := by rw [norm_sub_rev]
    linarith only [hTriangle, hNear]
  have hPower : ‖W‖ ^ 3 ≤ (‖Y‖ + 1) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg W) hWBound 3
  have hCoefficient : 0 ≤
      81 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant := by
    positivity [h3SobolevDeweightingConstant_nonneg]
  have hMixed :=
    thirdFullKinetic_lowMax_mixedSchwartzFlux_autoWeightedH3_244
      R q q q W W W hq hq hq 1 (by norm_num)
  have hCubic :
      (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        ‖thirdFullKineticMixedPolarSixthFlux244
          (thirdFullKineticSchwartzPolarization244 q)
          (thirdFullKineticSchwartzPolarization244 q)
          (thirdFullKineticSchwartzPolarization244 q) z‖
          ∂volume.prod volume) ≤
      (81 * (2 * ((R : ℝ) + 1)) ^ 7 *
        h3SobolevDeweightingConstant) * ‖W‖ ^ 3 := by
    convert hMixed using 1 <;> norm_num <;> ring
  let F := thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R q
  have hIntegral :
      ‖F‖ ≤
        ∫ z in (thirdFullHighMaxSet244 R)ᶜ,
          ‖thirdFullKineticMixedPolarSixthFlux244
            (thirdFullKineticSchwartzPolarization244 q)
            (thirdFullKineticSchwartzPolarization244 q)
            (thirdFullKineticSchwartzPolarization244 q) z‖
            ∂volume.prod volume := by
    dsimp only [F, thirdFullKineticSchwartzSignedLowMaxFluxIntegral244]
    exact norm_integral_le_integral_norm _
  calc
    |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R q).im| ≤
        ‖F‖ := Complex.abs_im_le_norm _
    _ ≤ _ := hIntegral
    _ ≤ (81 * (2 * ((R : ℝ) + 1)) ^ 7 *
          h3SobolevDeweightingConstant) * ‖W‖ ^ 3 := hCubic
    _ ≤ thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y := by
      unfold thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244
      exact mul_le_mul_of_nonneg_left hPower hCoefficient

/-- This lower physical annular height is independent of both recovered
Schwartz states. It retains the exact previous (R+1)^2 signed amplitude. -/
noncomputable def thirdFullKineticSignedLowMaxPhysicalViscousHeight244
    (R : ℕ) (X Y : H3SpectralVelocityState) (eta : ℝ) : ℝ :=
  (((R : ℝ) + 1) ^ 2 * (eta / 4) ^ 2) /
    (2 * ((thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y) ^ 2 + 1))

/-- Calibrated recoveries cannot decrease the old viscous height below the
physical height defined using the same actual endpoint H3 norms. -/
theorem thirdFullKinetic_signedLowMax_physicalHeight_le_recovered244
    (R : ℕ) (X Y V W : H3SpectralVelocityState)
    (eta : ℝ)
    (hV : ‖V - X‖ ≤ 1) (hW : ‖Y - W‖ ≤ 1) :
    thirdFullKineticSignedLowMaxPhysicalViscousHeight244 R X Y eta ≤
      thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W eta := by
  let A : ℝ := thirdFullKineticSignedLowMaxFluxClockWeight244 R V W
  let B : ℝ := thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y
  have hA : 0 ≤ A := by
    dsimp only [A, thirdFullKineticSignedLowMaxFluxClockWeight244]
    positivity [h3SobolevDeweightingConstant_nonneg]
  have hAB : A ≤ B :=
    thirdFullKinetic_signedLowMax_clockWeight_le_physical244
      R X Y V W hV hW
  have hSquare : A ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hA hAB 2
  have hDen : 2 * (A ^ 2 + 1) ≤ 2 * (B ^ 2 + 1) := by
    nlinarith only [hSquare]
  have hDA : 0 < 2 * (A ^ 2 + 1) := by positivity
  have hDB : 0 < 2 * (B ^ 2 + 1) := by positivity
  change (((R : ℝ) + 1) ^ 2 * (eta / 4) ^ 2) /
      (2 * (B ^ 2 + 1)) ≤
    (((R : ℝ) + 1) ^ 2 * (eta / 4) ^ 2) /
      (2 * (A ^ 2 + 1))
  apply (div_le_div_iff₀ hDB hDA).2
  exact mul_le_mul_of_nonneg_left hDen (by positivity)

/-- All four costs of physical signed replenishment on a strict kinetic gap
are now expressed in terms of ACTUAL physical H3 states, source and full
physical dissipation. The only remaining moving quantities are true physical
quantities: R, the endpoint norms, the source integral and viscous width. -/
theorem thirdFullPhysical_gapAdverseThird_physicalLowMaxFourCosts244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (x y t : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T) (hxy : x < y)
    (ht : t ∈ Set.Icc x y)
    (eta gamma : ℝ) (hEta : 0 < eta) (hGamma : 0 < gamma)
    (hAdverse : eta < -velocityH3TransportDerivative3At u t) :
    (eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
      (1944 * h3SobolevFirstMomentDeweightingConstant *
        (velocityH3EnergyAt u t + 1) *
        (‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ + gamma) ^ 2)) ∨
    (let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
     let X := h3AuditActualSpectralVelocityTotal hH3 t
     let Y := h3AuditActualSpectralVelocityTotal hH3 x
     (mu / 2 ≤ thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y) ∨
     (mu / 8 < thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y *
       (thirdFullFiniteBandH3WeightCeiling244 R *
         (∫ r in x..y,
           ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume))) ∨
     (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
       ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
       width * (thirdFullKineticSignedLowMaxPhysicalViscousHeight244
         R X Y (mu / 2) / 4) ≤
         ∫ r in x..y, velocityH3DissipationAt u r ∂volume)) := by
  let X : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let Y : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 x
  let mu : ℝ := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
  have hMu : 0 < mu :=
    thirdFullKineticSignedLowMaxPhysicalMargin_pos244 eta hEta
  have hD :
      thirdFullKineticSignedLowMaxCalibratedTolerance244 R X Y mu ≤ 1 :=
    (thirdFullKinetic_signedLowMax_calibratedTolerance_pos244
      R X Y mu hMu).2
  have hAlt :=
    thirdFullPhysical_gapAdverseThird_calibratedSignedLowMaxSourceOrCharge244
      hH3 hClass hDInt b hb R x y t hx hy hxy ht
      eta gamma hEta hGamma hAdverse
  rcases hAlt with hTail | ⟨q, _p, W, V, hq, _hp, _hSolQ, _hSolP, hData⟩
  · exact Or.inl hTail
  · right
    rcases hData with ⟨hNearP, hNearQ, hBranches⟩
    have hVOne : ‖V - X‖ ≤ 1 := hNearP.le.trans hD
    have hWOne : ‖Y - W‖ ≤ 1 := hNearQ.le.trans hD
    rcases hBranches with hBaseline | hSource | ⟨z, width, hz, hWidth, hInside, hCost⟩
    · exact Or.inl ((hBaseline.trans
        (thirdFullKinetic_signedLowMax_referenceBaseline_le_physical244
          R q W Y hq hWOne)))
    · exact Or.inr (Or.inl hSource)
    · have hHeight :
          thirdFullKineticSignedLowMaxPhysicalViscousHeight244
            R X Y (mu / 2) ≤
            thirdFullKineticSignedLowMaxPDEViscousHeight244
              R V W (mu / 2) :=
        thirdFullKinetic_signedLowMax_physicalHeight_le_recovered244
          R X Y V W (mu / 2) hVOne hWOne
      have hCharge :
          width * (thirdFullKineticSignedLowMaxPhysicalViscousHeight244
            R X Y (mu / 2) / 4) ≤
          width * (thirdFullKineticSignedLowMaxPDEViscousHeight244
            R V W (mu / 2) / 4) := by
        calc
          _ = (width / 4) *
              thirdFullKineticSignedLowMaxPhysicalViscousHeight244
                R X Y (mu / 2) := by ring
          _ ≤ (width / 4) *
              thirdFullKineticSignedLowMaxPDEViscousHeight244
                R V W (mu / 2) :=
            mul_le_mul_of_nonneg_left hHeight (by positivity)
          _ = _ := by ring
      exact Or.inr (Or.inr
        ⟨z, width, hz, hWidth, hInside, hCharge.trans hCost⟩)

/-- The genuine integrated signed gap surplus therefore has an entirely
physical four-way necessary condition on the ORIGINAL interval. -/
theorem thirdFullPhysical_gapSignedSurplus_physicalLowMaxFourCosts244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T) (hxy : x < y)
    (eta gamma : ℝ) (hEta : 0 < eta) (hGamma : 0 < gamma)
    (hExcess : thirdFullKineticGapLowOrderMargin244 u eta x y <
      thirdFullKineticGapSignedSurplus244 u x y) :
    ∃ t : ℝ, t ∈ Set.Icc x y ∧
      eta < -velocityH3TransportDerivative3At u t ∧
      ((eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
        (1944 * h3SobolevFirstMomentDeweightingConstant *
          (velocityH3EnergyAt u t + 1) *
          (‖thirdFullSpectralVelocityHighRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 t)‖ + gamma) ^ 2)) ∨
      (let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
       let X := h3AuditActualSpectralVelocityTotal hH3 t
       let Y := h3AuditActualSpectralVelocityTotal hH3 x
       (mu / 2 ≤ thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y) ∨
       (mu / 8 < thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y *
         (thirdFullFiniteBandH3WeightCeiling244 R *
           (∫ r in x..y,
             ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume))) ∨
       (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
         ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
         width * (thirdFullKineticSignedLowMaxPhysicalViscousHeight244
           R X Y (mu / 2) / 4) ≤
           ∫ r in x..y, velocityH3DissipationAt u r ∂volume))) := by
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hyClass : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hy.1, hy.2⟩
  obtain ⟨t, ht, hAdverse⟩ :=
    thirdFullPhysical_gapLowOrderExcess_forces_adverseThird244
      hH3 hClass x y eta hxClass hyClass hxy hEta hExcess
  exact ⟨t, ht, hAdverse,
    thirdFullPhysical_gapAdverseThird_physicalLowMaxFourCosts244
      hH3 hClass hDInt b hb R x y t hx hy hxy ht
      eta gamma hEta hGamma hAdverse⟩

end
end PrimeTensor.FirstMonomialTriad

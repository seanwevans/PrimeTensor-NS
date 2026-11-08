import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxPhysicalGapReplenishment
import Mathlib.Tactic

/-!
# Physical energy-calibrated LowMax recovery: removing the artificial error clock

The previous physical signed replenishment theorem constructs both exact
Schwartz Fourier recoveries, but its clock still contains their arbitrarily
small H3 approximation errors multiplied by a recovery-dependent seventh-power
radial / cubic amplitude coefficient.

Here the approximation tolerances are chosen **before** recovery, from the
actual physical H3 endpoint norms and the prescribed radius and signed margin.
Both recovery norms are thereby bounded by physical norms plus one. The
recovery-dependent coefficient is bounded by an explicit physical coefficient,
and both H3 approximation errors together spend at most 1/16 of the signed
one-sided margin. Hence the former clock arm forces an actual PDE SOURCE L1
cost on the very same physical gap. No uniform-in-radius or terminal physical
energy bound is asserted. The earlier signed LowMax baseline remains a real
alternative, as does high-frequency / physical annular viscous dissipation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology FourierTransform
open scoped BigOperators Interval ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev GA3 := PrimeTensor.Axis Depth.three
private abbrev GV3 := H3FourierPoint3

noncomputable local instance axisFintypeCalibratedGapClock244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- An explicit amplitude ceiling depending on the two ACTUAL physical H3
spectral states, not their subsequently constructed Schwartz approximations. -/
noncomputable def thirdFullKineticSignedLowMaxPhysicalClockCeiling244
    (R : ℕ) (X Y : H3SpectralVelocityState) : ℝ :=
  (243 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant) *
    (3 + ‖X‖ + ‖Y‖) ^ 3

/-- Positive recovery tolerance, calibrated before selecting either
Schwartz profile. The min with one controls both recovered H3 norms. -/
noncomputable def thirdFullKineticSignedLowMaxCalibratedTolerance244
    (R : ℕ) (X Y : H3SpectralVelocityState) (mu : ℝ) : ℝ :=
  min 1 (mu /
    (32 * (thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y + 1)))

theorem thirdFullKinetic_signedLowMax_calibratedTolerance_pos244
    (R : ℕ) (X Y : H3SpectralVelocityState) (mu : ℝ)
    (hMu : 0 < mu) :
    0 < thirdFullKineticSignedLowMaxCalibratedTolerance244 R X Y mu ∧
    thirdFullKineticSignedLowMaxCalibratedTolerance244 R X Y mu ≤ 1 := by
  have hCeil : 0 ≤ thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y := by
    unfold thirdFullKineticSignedLowMaxPhysicalClockCeiling244
    positivity [h3SobolevDeweightingConstant_nonneg]
  have hDen : 0 <
      32 * (thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y + 1) := by
    linarith only [hCeil]
  unfold thirdFullKineticSignedLowMaxCalibratedTolerance244
  exact ⟨lt_min_iff.mpr ⟨by norm_num, div_pos hMu hDen⟩,
    min_le_left _ _⟩

/-- The coefficient of the *actual* Schwartz pair cannot exceed the
physical coefficient if both spectral recovery errors are less than one. -/
theorem thirdFullKinetic_signedLowMax_clockWeight_le_physical244
    (R : ℕ) (X Y V W : H3SpectralVelocityState)
    (hV : ‖V - X‖ ≤ 1) (hW : ‖Y - W‖ ≤ 1) :
    thirdFullKineticSignedLowMaxFluxClockWeight244 R V W ≤
      thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y := by
  have hVNorm : ‖V‖ ≤ ‖V - X‖ + ‖X‖ := by
    calc
      ‖V‖ = ‖(V - X) + X‖ := by rw [sub_add_cancel]
      _ ≤ ‖V - X‖ + ‖X‖ := norm_add_le _ _
  have hWNorm : ‖W‖ ≤ ‖Y - W‖ + ‖Y‖ := by
    calc
      ‖W‖ = ‖(W - Y) + Y‖ := by rw [sub_add_cancel]
      _ ≤ ‖W - Y‖ + ‖Y‖ := norm_add_le _ _
      _ = ‖Y - W‖ + ‖Y‖ := by rw [norm_sub_rev]
  have hSum : 1 + ‖V‖ + ‖W‖ ≤ 3 + ‖X‖ + ‖Y‖ := by
    linarith only [hVNorm, hWNorm, hV, hW]
  have hPow : (1 + ‖V‖ + ‖W‖) ^ 3 ≤
      (3 + ‖X‖ + ‖Y‖) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hSum 3
  have hC : 0 ≤
      243 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant := by
    positivity [h3SobolevDeweightingConstant_nonneg]
  unfold thirdFullKineticSignedLowMaxFluxClockWeight244
    thirdFullKineticSignedLowMaxPhysicalClockCeiling244
  exact mul_le_mul_of_nonneg_left hPow hC

/-- Both automatically chosen physical recovery errors together consume
at most 1/16 of the signed one-sided margin, after the EXACT seventh-power
radial and cubic amplitude coefficient is applied. -/
theorem thirdFullKinetic_signedLowMax_calibratedErrors_le244
    (R : ℕ) (X Y V W : H3SpectralVelocityState)
    (mu : ℝ) (hMu : 0 < mu)
    (hV : ‖V - X‖ <
      thirdFullKineticSignedLowMaxCalibratedTolerance244 R X Y mu)
    (hW : ‖Y - W‖ <
      thirdFullKineticSignedLowMaxCalibratedTolerance244 R X Y mu) :
    thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
        (‖V - X‖ + ‖Y - W‖) ≤ mu / 16 := by
  let C : ℝ := thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y
  let d : ℝ := thirdFullKineticSignedLowMaxCalibratedTolerance244 R X Y mu
  have hCeil : 0 ≤ C := by
    dsimp only [C, thirdFullKineticSignedLowMaxPhysicalClockCeiling244]
    positivity [h3SobolevDeweightingConstant_nonneg]
  have hD : 0 < d ∧ d ≤ 1 :=
    thirdFullKinetic_signedLowMax_calibratedTolerance_pos244 R X Y mu hMu
  have hVOne : ‖V - X‖ ≤ 1 := (le_of_lt hV).trans hD.2
  have hWOne : ‖Y - W‖ ≤ 1 := (le_of_lt hW).trans hD.2
  have hA : thirdFullKineticSignedLowMaxFluxClockWeight244 R V W ≤ C :=
    thirdFullKinetic_signedLowMax_clockWeight_le_physical244
      R X Y V W hVOne hWOne
  have hCOne : 0 < C + 1 := by linarith only [hCeil]
  have hUpperD : d ≤ mu / (32 * (C + 1)) := by
    dsimp only [d, thirdFullKineticSignedLowMaxCalibratedTolerance244, C]
    exact min_le_right _ _
  have hCLe : C ≤ C + 1 := by linarith
  have hScale : C * d ≤ mu / 32 := by
    calc
      C * d ≤ (C + 1) * d :=
        mul_le_mul_of_nonneg_right hCLe hD.1.le
      _ ≤ (C + 1) * (mu / (32 * (C + 1))) :=
        mul_le_mul_of_nonneg_left hUpperD hCOne.le
      _ = mu / 32 := by
        have hNe : C + 1 ≠ 0 := ne_of_gt hCOne
        field_simp [hNe]
  calc
    thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
        (‖V - X‖ + ‖Y - W‖) ≤
      C * (‖V - X‖ + ‖Y - W‖) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ ≤ C * (2 * d) := by
      apply mul_le_mul_of_nonneg_left _ hCeil
      linarith only [hV, hW]
    _ = 2 * (C * d) := by ring
    _ ≤ 2 * (mu / 32) :=
      mul_le_mul_of_nonneg_left hScale (by norm_num)
    _ = mu / 16 := by ring

/-- An amplitude-calibrated signed LowMax clock therefore entails a
PHYSICAL projected-source L1 action, with all approximation errors removed. -/
theorem thirdFullKinetic_signedLowMax_calibratedClock_forcesSource244
    (mu A S eV eW : ℝ)
    (hMu : 0 < mu)
    (hError : A * (eV + eW) ≤ mu / 16)
    (hClock : mu / 4 < A * (eV + S + eW)) :
    mu / 8 < A * S := by
  have hIdentity : A * (eV + S + eW) =
      A * (eV + eW) + A * S := by ring
  rw [hIdentity] at hClock
  linarith only [hError, hClock, hMu]

/-! ## Physical integrated-gap realization, with no assumed Schwartz profiles -/

/-- The actual adverse third-transport observation yields EITHER its
high-radial tail or two automatically constructed, exactly represented,
real-solenoidal physical Schwartz recoveries whose errors are calibrated
against the physical H3 endpoint norms. The earlier baseline remains a
separate genuine signed flux. In the clock arm the ONLY surviving term is
the physical projected-source L1 action on the original gap. -/
theorem thirdFullPhysical_gapAdverseThird_calibratedSignedLowMaxSourceOrCharge244
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
    ∃ (q p : GA3 → SchwartzMap GV3 ℂ)
      (W V : H3SpectralVelocityState),
      (∀ j : GA3,
        (W (h3ClassicalizationFinOfAxis j) : GV3 → ℂ) =ᵐ[volume]
          (fun ξ : GV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (q j)) ξ)) ∧
      (∀ j : GA3,
        (V (h3ClassicalizationFinOfAxis j) : GV3 → ℂ) =ᵐ[volume]
          (fun ξ : GV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (p j)) ξ)) ∧
      (∀ ξ : GV3, ∑ j : GA3,
        fderiv ℝ (q j) ξ (h3FourierAxisDirection j) = 0) ∧
      (∀ ξ : GV3, ∑ j : GA3,
        fderiv ℝ (p j) ξ (h3FourierAxisDirection j) = 0) ∧
      (let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
       let d := thirdFullKineticSignedLowMaxCalibratedTolerance244 R
         (h3AuditActualSpectralVelocityTotal hH3 t)
         (h3AuditActualSpectralVelocityTotal hH3 x) mu
       ‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ < d ∧
       ‖h3AuditActualSpectralVelocityTotal hH3 x - W‖ < d ∧
       ((mu / 2 ≤
           |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R q).im|) ∨
        (mu / 8 < thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 x) *
          (thirdFullFiniteBandH3WeightCeiling244 R *
            (∫ r in x..y,
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume))) ∨
        (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
          ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
          width * (thirdFullKineticSignedLowMaxPDEViscousHeight244
            R V W (mu / 2) / 4) ≤
            ∫ r in x..y, velocityH3DissipationAt u r ∂volume))) := by
  let X : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let Y : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 x
  let mu : ℝ := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
  let d : ℝ := thirdFullKineticSignedLowMaxCalibratedTolerance244 R X Y mu
  have hMu : 0 < mu :=
    thirdFullKineticSignedLowMaxPhysicalMargin_pos244 eta hEta
  have hd : 0 < d :=
    (thirdFullKinetic_signedLowMax_calibratedTolerance_pos244
      R X Y mu hMu).1
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  obtain ⟨q, W, hq, hSolQ, hNearQ⟩ :=
    thirdFullPhysical_snapshot_signedLowMax_referenceRecovery244
      hH3 hClass hxClass d hd
  have hAlternative :=
    thirdFullPhysical_strictGap_adverseThird_tailOrBaselineClockCost244
      hH3 hClass hDInt b hb R x y hx hy hxy
      x t ⟨le_rfl, hxy.le⟩ ht q W hq
      eta gamma d hEta hGamma hd hAdverse
  rcases hAlternative with hTail | ⟨p, V, hp, hSolP, hNearP, hBranches⟩
  · exact Or.inl hTail
  · right
    refine ⟨q, p, W, V, hq, hp, hSolQ, hSolP, ?_⟩
    refine ⟨hNearP, hNearQ, ?_⟩
    rcases hBranches with hBaseline | hClock | hCharge
    · exact Or.inl hBaseline
    · right; left
      have hErrors :
          thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
            (‖V - X‖ + ‖Y - W‖) ≤ mu / 16 :=
        thirdFullKinetic_signedLowMax_calibratedErrors_le244
          R X Y V W mu hMu hNearP hNearQ
      have hSourceNonneg : 0 ≤
          thirdFullFiniteBandH3WeightCeiling244 R *
            (∫ r in x..y,
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) :=
        mul_nonneg (thirdFullFiniteBandH3WeightCeiling_nonneg244 R)
          (intervalIntegral.integral_nonneg hxy.le
            (fun r _ => norm_nonneg _))
      have hOne : d ≤ 1 :=
        (thirdFullKinetic_signedLowMax_calibratedTolerance_pos244
          R X Y mu hMu).2
      have hA : thirdFullKineticSignedLowMaxFluxClockWeight244 R V W ≤
          thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y :=
        thirdFullKinetic_signedLowMax_clockWeight_le_physical244 R X Y V W
          (hNearP.le.trans hOne) (hNearQ.le.trans hOne)
      have hActual :=
        thirdFullKinetic_signedLowMax_calibratedClock_forcesSource244
          mu (thirdFullKineticSignedLowMaxFluxClockWeight244 R V W)
          (thirdFullFiniteBandH3WeightCeiling244 R *
            (∫ r in x..y,
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume))
          (‖V - X‖) (‖Y - W‖) hMu hErrors hClock
      exact lt_of_lt_of_le hActual
        (mul_le_mul_of_nonneg_right hA hSourceNonneg)
    · exact Or.inr (Or.inr hCharge)

/-- The ORIGINAL physical integrated signed surplus produces the above
energy-calibrated two-recovery source/viscous alternative automatically.
The adverse time is selected by the actual Navier-Stokes signed energy law. -/
theorem thirdFullPhysical_gapSignedSurplus_calibratedSignedLowMaxSourceOrCharge244
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
        ∃ (q p : GA3 → SchwartzMap GV3 ℂ)
          (W V : H3SpectralVelocityState),
          (∀ j : GA3,
            (W (h3ClassicalizationFinOfAxis j) : GV3 → ℂ) =ᵐ[volume]
              (fun ξ : GV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (q j)) ξ)) ∧
          (∀ j : GA3,
            (V (h3ClassicalizationFinOfAxis j) : GV3 → ℂ) =ᵐ[volume]
              (fun ξ : GV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (p j)) ξ)) ∧
          (∀ ξ : GV3, ∑ j : GA3,
            fderiv ℝ (q j) ξ (h3FourierAxisDirection j) = 0) ∧
          (∀ ξ : GV3, ∑ j : GA3,
            fderiv ℝ (p j) ξ (h3FourierAxisDirection j) = 0) ∧
          (let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
           let d := thirdFullKineticSignedLowMaxCalibratedTolerance244 R
             (h3AuditActualSpectralVelocityTotal hH3 t)
             (h3AuditActualSpectralVelocityTotal hH3 x) mu
           ‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ < d ∧
           ‖h3AuditActualSpectralVelocityTotal hH3 x - W‖ < d ∧
           ((mu / 2 ≤
               |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R q).im|) ∨
            (mu / 8 < thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R
              (h3AuditActualSpectralVelocityTotal hH3 t)
              (h3AuditActualSpectralVelocityTotal hH3 x) *
              (thirdFullFiniteBandH3WeightCeiling244 R *
                (∫ r in x..y,
                  ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume))) ∨
            (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
              ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
              width * (thirdFullKineticSignedLowMaxPDEViscousHeight244
                R V W (mu / 2) / 4) ≤
                ∫ r in x..y, velocityH3DissipationAt u r ∂volume)))) := by
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hyClass : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hy.1, hy.2⟩
  obtain ⟨t, ht, hAdverse⟩ :=
    thirdFullPhysical_gapLowOrderExcess_forces_adverseThird244
      hH3 hClass x y eta hxClass hyClass hxy hEta hExcess
  exact ⟨t, ht, hAdverse,
    thirdFullPhysical_gapAdverseThird_calibratedSignedLowMaxSourceOrCharge244
      hH3 hClass hDInt b hb R x y t hx hy hxy ht
      eta gamma hEta hGamma hAdverse⟩

end
end PrimeTensor.FirstMonomialTriad

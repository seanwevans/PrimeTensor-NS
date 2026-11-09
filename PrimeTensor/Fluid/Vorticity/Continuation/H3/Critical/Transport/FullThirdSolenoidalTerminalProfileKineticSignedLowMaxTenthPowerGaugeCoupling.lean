import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxGaugeRateBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxRadialTenthPowerEscape
import Mathlib.Tactic

/-!
# Signed sixth flux: synchronize the tenth-power source gate with the kinetic gauge

The accepted tenth-power theorem controls the physical projected-source clock
by 62208*C₀*(J+1)^10*(3+2*E)^3 whenever the natural radius and both actual
H3 state norms lie under prescribed caps J and E. Its cofinal theorem
therefore leaves a physical baseline, radius/energy escape, an earlier
integrated viscous charge, or a gamma-regularized high-radial carrier.

The accepted kinetic gauge theorem supplies the missing physical cost of that
last carrier: clock compression, outer annulus Q beyond an arbitrary gauge G,
or a finite kinetic-rate payment. Its cofinal index is uniform in G, radius,
and the physical observation time. Here the positive gamma is eliminated
BEFORE passing to that theorem and the two cofinal thresholds are intersected.

The result is conditional on an actual adverse physical third-order sample.
A companion derives such a sample from the original signed gap surplus.
Neither the original earlier baseline nor the gap clock is assumed to vanish.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Exactly the gamma-INDEPENDENT part of the accepted tenth-power
radius/physical-energy obstruction. The last disjunct is the original
positive-width integrated quadratic-height charge, not a pointwise spike. -/
def ThirdFullKineticSignedLowMaxTenthPowerResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R J : ℕ) (E eta epsilon x y t : ℝ) : Prop :=
  let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
  let X := h3AuditActualSpectralVelocityTotal hH3 t
  let Y := h3AuditActualSpectralVelocityTotal hH3 x
  (mu / 2 ≤ thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y) ∨
  (J < R ∨ E < velocityH3EnergyAt u t ∨ E < velocityH3EnergyAt u x) ∨
  (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
    ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
    width * (thirdFullKineticSignedLowMaxPhysicalViscousHeight244
      R X Y (mu / 2) / 4) < epsilon)

/-- The COMPLETE anchored signed sixth-flux obstruction at an adverse
physical sample. The original tenth-power residual is explicit; the last
arm pays the high-radial carrier by a kinetic CLOCK, OUTER cutoff, or RATE.
Crucially, the rate uses the earlier fixed kinetic anchor b, not the
moving kinetic gap left endpoint. -/
def ThirdFullKineticSignedLowMaxTenthGaugeCoupling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (R J G : ℕ) (E eta epsilon x y t : ℝ) : Prop :=
  ThirdFullKineticSignedLowMaxTenthPowerResidual244
    hH3 R J E eta epsilon x y t ∨
  (∃ Q : ℕ, R ≤ Q ∧
    (let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
       R eta (velocityH3EnergyAt u t)
     let C := 2 * (∑ j ∈ Finset.range (G + 1),
       thirdFullPhysicalKineticLowBandDissipationRate244 j
         (velocityH3Energy0At u b)) + 1
     (y - x) * H < 16 * epsilon ∨ G < Q ∨ H ^ 2 < 32 * C * epsilon))

/-- An explicit fixed-energy positive floor for the linear signed-flux
high-radial viscous height. It depends only on the adverse margin and the
physical energy cap, not on time or the inner natural Fourier radius. -/
noncomputable def thirdFullKineticSignedLowMaxCappedLinearHeightFloor244
    (eta E : ℝ) : ℝ :=
  eta / (8 * (thirdFullKineticSignedLowMaxPhysicalHighTailFactor244 E + 1))

/-- The kinetic energy factor is nonnegative for a nonnegative physical
energy cap; therefore the fixed floor is strictly positive. -/
theorem thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244
    (eta E : ℝ) (hEta : 0 < eta) (hE : 0 ≤ E) :
    0 < thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E := by
  have hMoment : 0 ≤ h3SobolevFirstMomentDeweightingConstant :=
    h3SobolevFirstMomentDeweightingConstant_nonneg
  have hEnergy : 0 ≤ E + 1 := by linarith only [hE]
  have hFactor : 0 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244 E := by
    unfold thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
    exact mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by norm_num) hMoment) hEnergy)
  unfold thirdFullKineticSignedLowMaxCappedLinearHeightFloor244
  exact div_pos hEta (by linarith only [hFactor])

/-- If the actual physical H3 energy at an adverse time is at most E, then
the linear-margin high-radial viscous height has a concrete lower floor.
This is a genuine quantitative amplification of the tenth-power cap: the
high-radial carrier cannot disappear by merely adjusting a Schwartz gamma. -/
theorem thirdFullKinetic_signedLowMax_linearHeight_ge_cappedFloor244
    (R : ℕ) (eta Et E : ℝ)
    (hEta : 0 < eta) (hEt : 0 ≤ Et) (hEtE : Et ≤ E) :
    thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E ≤
      thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244 R eta Et := by
  let K : ℝ := ((2 * Real.pi) ^ 7 / 3) *
    (1944 * h3SobolevFirstMomentDeweightingConstant)
  have hMoment : 0 ≤ h3SobolevFirstMomentDeweightingConstant :=
    h3SobolevFirstMomentDeweightingConstant_nonneg
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by positivity)
      (mul_nonneg (by norm_num) hMoment)
  have hFactor (Z : ℝ) :
      thirdFullKineticSignedLowMaxPhysicalHighTailFactor244 Z =
        K * (Z + 1) := by
    unfold thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
    dsimp only [K]
    ring
  let At : ℝ := thirdFullKineticSignedLowMaxPhysicalHighTailFactor244 Et
  let AE : ℝ := thirdFullKineticSignedLowMaxPhysicalHighTailFactor244 E
  have hAt0 : 0 ≤ At := by
    rw [show At = K * (Et + 1) from hFactor Et]
    exact mul_nonneg hK (by linarith only [hEt])
  have hAE0 : 0 ≤ AE := by
    rw [show AE = K * (E + 1) from hFactor E]
    exact mul_nonneg hK (by linarith only [hEt, hEtE])
  have hAB : At ≤ AE := by
    rw [show At = K * (Et + 1) from hFactor Et,
      show AE = K * (E + 1) from hFactor E]
    exact mul_le_mul_of_nonneg_left (by linarith only [hEtE]) hK
  have hDenAt : 0 < 2 * (At + 1) := by linarith only [hAt0]
  have hDenAE : 0 < 8 * (AE + 1) := by linarith only [hAE0]
  let r : ℝ := (R : ℝ) + 1
  have hr : 1 ≤ r := by
    dsimp only [r]
    have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
    linarith only [hR]
  have hrSq : 1 ≤ r ^ 2 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hr 2)
  have hCompare : 2 * (At + 1) ≤ 2 * (AE + 1) := by
    linarith only [hAB]
  have hFloorNonneg : 0 ≤ eta / (8 * (AE + 1)) :=
    div_nonneg hEta.le hDenAE.le
  have hFraction :
      eta / (8 * (AE + 1)) * (2 * (At + 1)) ≤ eta / 4 := by
    calc
      eta / (8 * (AE + 1)) * (2 * (At + 1)) ≤
          eta / (8 * (AE + 1)) * (2 * (AE + 1)) :=
        mul_le_mul_of_nonneg_left hCompare hFloorNonneg
      _ = eta / 4 := by
        have hAEone : AE + 1 ≠ 0 :=
          ne_of_gt (by linarith only [hAE0] : 0 < AE + 1)
        field_simp [hAEone] <;> ring
  have hRadiusWeighted : eta / 2 ≤ r ^ 2 * (eta / 2) := by
    have hScaled := mul_le_mul_of_nonneg_right hrSq
      (div_nonneg hEta.le (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith only [hScaled]
  have hTarget : eta / 4 ≤ r ^ 2 * (eta / 2) := by
    linarith only [hRadiusWeighted, hEta]
  change eta / (8 * (AE + 1)) ≤
    (r ^ 2 * (eta / 2)) / (2 * (At + 1))
  apply (le_div_iff₀ hDenAt).mpr
  exact hFraction.trans hTarget

/-- On all sufficiently late ORIGINAL kinetic gaps, every genuine adverse
physical sample satisfies a single synchronized tenth-power/gauge-rate
alternative. The tail recovery tolerance is removed at the SAME sample;
the cofinal index is independent of G, R and t. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tenthGaugeCoupling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (tau : ℕ → ℝ) (N : ℕ → ℕ)
    (delta : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k => tau (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      tau (v k) + delta (v k) < tau (v l))
    (hWindows : ∀ k : ℕ,
      tau (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (tau (v k)) (v k) (N (v k))
        (M (v k)) (delta (v k)))
    (eta : ℝ) (hEta : 0 < eta)
    (J : ℕ) (E epsilon : ℝ) (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (G R : ℕ) (t : ℝ),
        t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        eta < -velocityH3TransportDerivative3At u t →
        ThirdFullKineticSignedLowMaxTenthGaugeCoupling244
          hH3 b R J G E eta epsilon
          (tau (v k) + delta (v k)) (tau (v (k + 1))) t := by
  have hRadius := thirdFullPhysical_kineticGaps_signedLowMax_radiusEnergyEscape244
    hH3 hClass hDInt b hb M tau N delta v
    hLimit hSeparated hWindows eta hEta J E epsilon hE hEpsilon
  have hGauge := thirdFullPhysical_kineticGaps_signedLowMax_tailGaugeRateOrClock244
    hH3 hClass hDInt b hb M tau N delta v
    hLimit hSeparated hWindows eta epsilon hEta hEpsilon
  filter_upwards [hRadius, hGauge] with k hkRadius hkGauge
  intro G R t ht hAdverse
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  let X : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let A : ℝ := thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
    (velocityH3EnergyAt u t)
  let H : ℝ := ‖thirdFullSpectralVelocityHighRadialApply244 R X‖
  let Bad : Prop := ThirdFullKineticSignedLowMaxTenthPowerResidual244
    hH3 R J E eta epsilon x y t
  have hEach (gamma : ℝ) (hGamma : 0 < gamma) :
      eta / 2 < A * (H + gamma) ^ 2 ∨ Bad := by
    have hPrev := hkRadius R gamma hGamma t ht hAdverse
    change (eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
      (1944 * h3SobolevFirstMomentDeweightingConstant *
        (velocityH3EnergyAt u t + 1) * (H + gamma) ^ 2)) ∨ Bad at hPrev
    rcases hPrev with hTail | hOther
    · left
      simpa only [A, H, thirdFullKineticSignedLowMaxPhysicalHighTailFactor244,
        mul_assoc] using hTail
    · exact Or.inr hOther
  have hZero := thirdFull_scalar_signedLowMax_removePositiveTailTolerance244
    (eta / 2) A H Bad hEach
  have hCarrier :
      eta / 2 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R X‖ ^ 2 ∨ Bad := by
    simpa only [A, H] using hZero
  change Bad ∨
    (∃ Q : ℕ, R ≤ Q ∧
      (let HH := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
         R eta (velocityH3EnergyAt u t)
       let C := 2 * (∑ j ∈ Finset.range (G + 1),
         thirdFullPhysicalKineticLowBandDissipationRate244 j
           (velocityH3Energy0At u b)) + 1
       (y - x) * HH < 16 * epsilon ∨ G < Q ∨
         HH ^ 2 < 32 * C * epsilon))
  rcases hCarrier with hTail | hRest
  · right
    exact hkGauge G R t ht (by simpa only [X] using hTail)
  · exact Or.inl hRest

/-- The coupling has a direct cutoff-forcing conclusion whenever the
original tenth-power residual, kinetic gap clock and finite-rate payment
are independently excluded. It is NOT an unconditional radius escape. -/
theorem thirdFullKinetic_signedLowMax_tenthGauge_forcesOuterCutoff244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (R J G : ℕ) (E eta epsilon x y t : ℝ)
    (hCoupled : ThirdFullKineticSignedLowMaxTenthGaugeCoupling244
      hH3 b R J G E eta epsilon x y t)
    (hResidual : ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
      hH3 R J E eta epsilon x y t)
    (hClock : 16 * epsilon ≤ (y - x) *
      thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
        R eta (velocityH3EnergyAt u t))
    (hRate : 32 * (2 * (∑ j ∈ Finset.range (G + 1),
      thirdFullPhysicalKineticLowBandDissipationRate244 j
        (velocityH3Energy0At u b)) + 1) * epsilon ≤
      (thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
        R eta (velocityH3EnergyAt u t)) ^ 2) :
    ∃ Q : ℕ, R ≤ Q ∧ G < Q := by
  change ThirdFullKineticSignedLowMaxTenthPowerResidual244
      hH3 R J E eta epsilon x y t ∨
    (∃ Q : ℕ, R ≤ Q ∧
      (let HH := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
         R eta (velocityH3EnergyAt u t)
       let C := 2 * (∑ j ∈ Finset.range (G + 1),
         thirdFullPhysicalKineticLowBandDissipationRate244 j
           (velocityH3Energy0At u b)) + 1
       (y - x) * HH < 16 * epsilon ∨ G < Q ∨
         HH ^ 2 < 32 * C * epsilon)) at hCoupled
  rcases hCoupled with hBad | ⟨Q, hRQ, hAlt⟩
  · exact False.elim (hResidual hBad)
  refine ⟨Q, hRQ, ?_⟩
  rcases hAlt with hShort | hRest
  · exact False.elim ((not_lt_of_ge hClock) hShort)
  rcases hRest with hGauge | hSmall
  · exact hGauge
  · exact False.elim ((not_lt_of_ge hRate) hSmall)

/-- Quantitative cutoff forcing under a physical H3 energy cap.
The gap-clock and finite-gauge hypotheses use the FIXED floor from the
energy cap, not the potentially moving actual H3 energy coefficient. -/
theorem thirdFullKinetic_signedLowMax_tenthGauge_forcesOuter_of_energyCap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (R J G : ℕ) (E eta epsilon x y t : ℝ)
    (hEta : 0 < eta) (hxy : x < y)
    (hCoupled : ThirdFullKineticSignedLowMaxTenthGaugeCoupling244
      hH3 b R J G E eta epsilon x y t)
    (hResidual : ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
      hH3 R J E eta epsilon x y t)
    (hEnergyCap : velocityH3EnergyAt u t ≤ E)
    (hClock : 16 * epsilon ≤ (y - x) *
      thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E)
    (hRate : 32 * (2 * (∑ j ∈ Finset.range (G + 1),
      thirdFullPhysicalKineticLowBandDissipationRate244 j
        (velocityH3Energy0At u b)) + 1) * epsilon ≤
      (thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2) :
    ∃ Q : ℕ, R ≤ Q ∧ G < Q := by
  have hEt : 0 ≤ velocityH3EnergyAt u t := by
    have hOne := one_le_velocityH3EnergyAt u t
    linarith only [hOne]
  have hFloor := thirdFullKinetic_signedLowMax_linearHeight_ge_cappedFloor244
    R eta (velocityH3EnergyAt u t) E hEta hEt hEnergyCap
  have hGap : 0 ≤ y - x := sub_nonneg.mpr hxy.le
  have hClockActual : 16 * epsilon ≤ (y - x) *
      thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
        R eta (velocityH3EnergyAt u t) :=
    hClock.trans (mul_le_mul_of_nonneg_left hFloor hGap)
  have hFloorPos : 0 ≤
      thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E :=
    (thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244
      eta E hEta (hEt.trans hEnergyCap)).le
  have hSquare := pow_le_pow_left₀ hFloorPos hFloor 2
  have hRateActual : 32 * (2 * (∑ j ∈ Finset.range (G + 1),
      thirdFullPhysicalKineticLowBandDissipationRate244 j
        (velocityH3Energy0At u b)) + 1) * epsilon ≤
      (thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
        R eta (velocityH3EnergyAt u t)) ^ 2 := by
    exact hRate.trans (by simpa only using hSquare)
  exact thirdFullKinetic_signedLowMax_tenthGauge_forcesOuterCutoff244
    hH3 b R J G E eta epsilon x y t
    hCoupled hResidual hClockActual hRateActual

/-- A signed physical gap surplus exceeding its lower-order margin supplies
the actual adverse time for the complete tenth-power/gauge-rate coupling. -/
theorem thirdFullPhysical_kineticGaps_signedSurplus_tenthGaugeCoupling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (tau : ℕ → ℝ) (N : ℕ → ℕ)
    (delta : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k => tau (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      tau (v k) + delta (v k) < tau (v l))
    (hWindows : ∀ k : ℕ,
      tau (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (tau (v k)) (v k) (N (v k))
        (M (v k)) (delta (v k)))
    (eta : ℝ) (hEta : 0 < eta)
    (J : ℕ) (E epsilon : ℝ) (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (G R : ℕ),
        thirdFullKineticGapLowOrderMargin244 u eta
            (tau (v k) + delta (v k)) (tau (v (k + 1))) <
          thirdFullKineticGapSignedSurplus244 u
            (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        ∃ t : ℝ,
          t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) ∧
          eta < -velocityH3TransportDerivative3At u t ∧
          ThirdFullKineticSignedLowMaxTenthGaugeCoupling244
            hH3 b R J G E eta epsilon
            (tau (v k) + delta (v k)) (tau (v (k + 1))) t := by
  have hEventually :=
    thirdFullPhysical_kineticGaps_signedLowMax_tenthGaugeCoupling244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta hEta J E epsilon hE hEpsilon
  filter_upwards [hEventually] with k hk
  intro G R hExcess
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  have hx : x ∈ Set.Ioo a T := by
    obtain ⟨htWin, hw⟩ := hWindows k
    rcases hw with ⟨_, hd, _, he, _, _⟩
    exact ⟨by linarith only [hb.1, htWin.1, hd], he⟩
  have hy : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hWindows (k + 1)).1.1,
      (hWindows (k + 1)).1.2⟩
  have hxy : x < y := hSeparated k (k + 1) (Nat.lt_succ_self k)
  obtain ⟨t, ht, hAdverse⟩ :=
    thirdFullPhysical_gapLowOrderExcess_forces_adverseThird244
      hH3 hClass x y eta hx hy hxy hEta hExcess
  exact ⟨t, ht, hAdverse, hk G R t ht hAdverse⟩

end
end PrimeTensor.FirstMonomialTriad

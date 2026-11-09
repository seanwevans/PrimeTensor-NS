import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxLinearInGapViscous
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticAnnularDissipationRate
import Mathlib.Tactic

/-!
# Signed sixth flux: symmetric kinetic persistence and explicit rate/clock compression

The previous physical theorem proves a positive-width annular charge inside an
original kinetic gap but does not quantify the width by the kinetic-only rate.
The existing finite-annulus kinetic Lipschitz bound is valid in BOTH temporal
directions. Choose the longer side of any adverse time inside the original
closed gap, and retain the SAME finite annulus supplied by the highpass floor.
A symmetric min clock preserves its positive annular height without source
maxima or a Schwartz profile. The resulting exact in-gap charge forces either
shrinking gap length times physical height, or a large kinetic-only annular
rate relative to the squared physical height and the vanishing gap charge.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The genuine two-sided finite-annulus variation rate, controlled solely
by the earlier physical kinetic energy anchor and the two natural radii. -/
noncomputable def thirdFullKineticSignedLowMaxKineticAnnulusRate244
    (R N : ℕ) (E : ℝ) : ℝ :=
  thirdFullPhysicalKineticLowBandDissipationRate244 N E +
    thirdFullPhysicalKineticLowBandDissipationRate244 R E

theorem thirdFullKinetic_signedLowMax_kineticAnnulusRate_nonneg244
    (R N : ℕ) (E : ℝ) :
    0 ≤ thirdFullKineticSignedLowMaxKineticAnnulusRate244 R N E := by
  unfold thirdFullKineticSignedLowMaxKineticAnnulusRate244
  exact add_nonneg
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 N E)
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 R E)

/-- The gap quarter is available on at least one side of EVERY t in [x,y].
The other minimum term is the kinetic-only annular variation clock. -/
noncomputable def thirdFullKineticSignedLowMaxSymmetricGapWidth244
    (R N : ℕ) (E H x y : ℝ) : ℝ :=
  min ((y - x) / 4)
    (H / (8 * (thirdFullKineticSignedLowMaxKineticAnnulusRate244 R N E + 1)))

theorem thirdFullKinetic_signedLowMax_symmetricWidth_budget244
    (R N : ℕ) (E H x y : ℝ)
    (hH : 0 < H) (hxy : x < y) :
    let L := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R N E
    let w := thirdFullKineticSignedLowMaxSymmetricGapWidth244 R N E H x y
    0 < w ∧ w ≤ (y - x) / 4 ∧ L * w ≤ H / 8 := by
  let L : ℝ := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R N E
  let w : ℝ := thirdFullKineticSignedLowMaxSymmetricGapWidth244 R N E H x y
  have hL : 0 ≤ L := thirdFullKinetic_signedLowMax_kineticAnnulusRate_nonneg244 R N E
  have hL1 : 0 < L + 1 := by linarith only [hL]
  have hGap : 0 < (y - x) / 4 := by linarith only [hxy]
  have hFraction : 0 < H / (8 * (L + 1)) := by positivity
  have hw : 0 < w := by
    change 0 < min ((y - x) / 4) (H / (8 * (L + 1)))
    exact lt_min hGap hFraction
  have hQuarter : w ≤ (y - x) / 4 := by
    change min ((y - x) / 4) (H / (8 * (L + 1))) ≤ _
    exact min_le_left _ _
  have hRatio : w ≤ H / (8 * (L + 1)) := by
    change min ((y - x) / 4) (H / (8 * (L + 1))) ≤ _
    exact min_le_right _ _
  have hCost : L * w ≤ H / 8 := by
    calc
      L * w ≤ (L + 1) * w :=
        mul_le_mul_of_nonneg_right (by linarith : L ≤ L + 1) hw.le
      _ ≤ (L + 1) * (H / (8 * (L + 1))) :=
        mul_le_mul_of_nonneg_left hRatio hL1.le
      _ = H / 8 := by
        field_simp [ne_of_gt hL1]
  exact ⟨hw, hQuarter, hCost⟩

/-- Exact scalar alternative produced by the symmetric min clock and a
positive integrated annular charge, retaining every rate coefficient. -/
theorem thirdFullKinetic_signedLowMax_symmetricCharge_clockOrRate244
    (x y H L D : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (_hxy : x < y)
    (hCharge : min ((y - x) / 4) (H / (8 * (L + 1))) * (H / 4) ≤ D) :
    (y - x) * H ≤ 16 * D ∨ H ^ 2 ≤ 32 * (L + 1) * D := by
  have hL1 : 0 < L + 1 := by linarith only [hL]
  rcases le_total ((y - x) / 4) (H / (8 * (L + 1))) with hLeft | hRight
  · left
    rw [min_eq_left hLeft] at hCharge
    nlinarith only [hCharge]
  · right
    rw [min_eq_right hRight] at hCharge
    have hIdentity : H ^ 2 / (32 * (L + 1)) =
        (H / (8 * (L + 1))) * (H / 4) := by
      field_simp [ne_of_gt hL1] <;> norm_num
    have hRatio : H ^ 2 / (32 * (L + 1)) ≤ D := by
      rw [hIdentity]
      exact hCharge
    have hDen : 0 < 32 * (L + 1) := by positivity
    have hMul := (div_le_iff₀ hDen).mp hRatio
    nlinarith only [hMul]

/-- Any certified high-radial annulus at ANY time in the closed kinetic gap
persists at quarter height on the longer available side of that time. The
symmetric width is explicit and depends only on the TWO kinetic cutoff rates,
not an attained full-H3 state or an instantaneous projected-source maximum. -/
theorem thirdFullPhysical_signedLowMax_symmetricKineticInGapCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (H x y t : ℝ)
    (hH : 0 < H) (hx : x ∈ Set.Ioo b T)
    (hy : y ∈ Set.Ioo b T) (hxy : x < y)
    (ht : t ∈ Set.Icc x y)
    (hWindow : ThirdFullKineticSignedLowMaxCertifiedAnnularWindow244
      hH3 R H t) :
    ∃ (N : ℕ) (w : ℝ), R ≤ N ∧
      w = thirdFullKineticSignedLowMaxSymmetricGapWidth244 R N
        (velocityH3Energy0At u b) H x y ∧
      0 < w ∧
      ((t + w < y) ∨ (x < t - w)) ∧
      w * (H / 4) ≤
        ∫ r in x..y, velocityH3DissipationAt u r ∂volume := by
  obtain ⟨N, K, C, delta, hRN, _hK, _hC, _hDelta, _hDeltaOne,
    _hDeltaT, _hState, _hSource, hAt, _hWidth, _hFloor, _hCost⟩ := hWindow
  let E : ℝ := velocityH3Energy0At u b
  let L : ℝ := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R N E
  let w : ℝ := thirdFullKineticSignedLowMaxSymmetricGapWidth244 R N E H x y
  obtain ⟨hw, hQuarter, hRate⟩ :=
    thirdFullKinetic_signedLowMax_symmetricWidth_budget244 R N E H x y hH hxy
  have hL : 0 ≤ L := thirdFullKinetic_signedLowMax_kineticAnnulusRate_nonneg244 R N E
  let U : ℝ → H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3
  let Ann : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1) (U r) -
      h3PathActualLowRadialDissipation244 ((R : ℝ) + 1) (U r)
  let D : ℝ → ℝ := velocityH3DissipationAt u
  have hPeak : H / 2 < Ann t := hAt
  have hxClass : x ∈ Set.Ioo a T := ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hyClass : y ∈ Set.Ioo a T := ⟨lt_trans hb.1 hy.1, hy.2⟩
  have htTail : t ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  have hCont : ContinuousOn Ann (Set.Ioo a T) :=
    h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass ((R : ℝ) + 1) ((N : ℝ) + 1)
      (by positivity) (by positivity)
  have hDGap : IntervalIntegrable D volume x y := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc x y := by
      simpa only [Set.uIcc_of_le hxy.le] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hxClass.1.le.trans hrIcc.1, hrIcc.2.trans hyClass.2.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc x y)] D := by
    filter_upwards [] with r
    exact velocityH3DissipationAt_nonneg u r
  refine ⟨N, w, hRN, rfl, hw, ?_⟩
  by_cases hSide : t ≤ (x + y) / 2
  · have hForward : t + w < y := by
      linarith only [hSide, hQuarter, hxy]
    have hSub : Set.Icc t (t + w) ⊆ Set.Ioo a T := by
      intro r hr
      exact ⟨lt_of_lt_of_le hxClass.1 (ht.1.trans hr.1),
        lt_of_le_of_lt hr.2 (lt_trans hForward hyClass.2)⟩
    have hFloor (r : ℝ) (hr : r ∈ Set.Icc t (t + w)) : H / 4 < Ann r := by
      have hrTail : r ∈ Set.Ioo b T :=
        ⟨lt_of_lt_of_le htTail.1 hr.1,
         lt_of_le_of_lt hr.2 (lt_trans hForward hy.2)⟩
      have hLip := thirdFullPhysical_kineticNaturalAnnularDissipationLipschitz244
        hH3 hClass b hb R N t r htTail hrTail hr.1
      change |Ann t - Ann r| ≤ L * (r - t) at hLip
      have hDifference : Ann t - Ann r ≤ L * (r - t) :=
        (le_abs_self (Ann t - Ann r)).trans hLip
      have hTime : r - t ≤ w := by linarith only [hr.2]
      have hBound : L * (r - t) ≤ H / 8 :=
        (mul_le_mul_of_nonneg_left hTime hL).trans hRate
      linarith only [hPeak, hDifference, hBound, hH]
    have hAnnInt : IntervalIntegrable Ann volume t (t + w) :=
      (hCont.mono hSub).intervalIntegrable_of_Icc (by linarith only [hw])
    have hDWin : IntervalIntegrable D volume t (t + w) := by
      apply hDInt.mono_set
      intro r hr
      have hrIcc : r ∈ Set.Icc t (t + w) := by
        rcases Set.mem_uIcc.mp hr with hForward | hReverse
        · exact hForward
        · exfalso
          have hStrict : t < t + w := by linarith only [hw]
          exact (not_le_of_gt hStrict) (hReverse.1.trans hReverse.2)
      have hrAll : r ∈ Set.Icc a T :=
        ⟨hxClass.1.le.trans (ht.1.trans hrIcc.1),
          hrIcc.2.trans (lt_trans hForward hyClass.2).le⟩
      simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
    have hAnnCost : w * (H / 4) ≤ ∫ r in t..(t + w), Ann r ∂volume := by
      have hCost := h3Path_localPositiveHeight_forces_integratedCost244
        Ann t (t + w) (H / 4) (by linarith only [hw]) hAnnInt
        (fun r hr => (hFloor r hr).le)
      calc
        w * (H / 4) = ((t + w) - t) * (H / 4) := by ring
        _ ≤ _ := hCost
    have hAnnLeD : (∫ r in t..(t + w), Ann r ∂volume) ≤
        ∫ r in t..(t + w), D r ∂volume := by
      apply intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right hw.le) hAnnInt hDWin
      intro r hr
      exact h3Path_actualFiniteAnnulusDissipation_le_fullAt244
        hH3 hClass r (hSub hr) ((R : ℝ) + 1) ((N : ℝ) + 1)
    have hGapCost : (∫ r in t..(t + w), D r ∂volume) ≤
        ∫ r in x..y, D r ∂volume :=
      intervalIntegral.integral_mono_interval
        ht.1 (le_add_of_nonneg_right hw.le) hForward.le hNonneg hDGap
    exact ⟨Or.inl hForward, (hAnnCost.trans hAnnLeD).trans hGapCost⟩
  · have hBeyond : (x + y) / 2 < t := lt_of_not_ge hSide
    have hBackward : x < t - w := by
      linarith only [hBeyond, hQuarter, hxy]
    have hSub : Set.Icc (t - w) t ⊆ Set.Ioo a T := by
      intro r hr
      exact ⟨lt_trans hxClass.1 (lt_of_lt_of_le hBackward hr.1),
        lt_of_le_of_lt hr.2 (lt_of_le_of_lt ht.2 hyClass.2)⟩
    have hFloor (r : ℝ) (hr : r ∈ Set.Icc (t - w) t) : H / 4 < Ann r := by
      have hrTail : r ∈ Set.Ioo b T :=
        ⟨lt_trans hx.1 (lt_of_lt_of_le hBackward hr.1),
         lt_of_le_of_lt hr.2 htTail.2⟩
      have hLip := thirdFullPhysical_kineticNaturalAnnularDissipationLipschitz244
        hH3 hClass b hb R N r t hrTail htTail hr.2
      change |Ann r - Ann t| ≤ L * (t - r) at hLip
      have hDifference : Ann t - Ann r ≤ L * (t - r) := by
        calc
          Ann t - Ann r ≤ |Ann t - Ann r| := le_abs_self _
          _ = |Ann r - Ann t| := abs_sub_comm _ _
          _ ≤ L * (t - r) := hLip
      have hTime : t - r ≤ w := by linarith only [hr.1]
      have hBound : L * (t - r) ≤ H / 8 :=
        (mul_le_mul_of_nonneg_left hTime hL).trans hRate
      linarith only [hPeak, hDifference, hBound, hH]
    have hAnnInt : IntervalIntegrable Ann volume (t - w) t :=
      (hCont.mono hSub).intervalIntegrable_of_Icc (by linarith only [hw])
    have hDWin : IntervalIntegrable D volume (t - w) t := by
      apply hDInt.mono_set
      intro r hr
      have hrIcc : r ∈ Set.Icc (t - w) t := by
        simpa only [Set.uIcc_of_le (by linarith only [hw] : t - w ≤ t)] using hr
      have hrAll : r ∈ Set.Icc a T :=
        ⟨hxClass.1.le.trans (hBackward.le.trans hrIcc.1),
          hrIcc.2.trans (ht.2.trans hyClass.2.le)⟩
      simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
    have hAnnCost : w * (H / 4) ≤ ∫ r in (t - w)..t, Ann r ∂volume := by
      have hCost := h3Path_localPositiveHeight_forces_integratedCost244
        Ann (t - w) t (H / 4) (by linarith only [hw]) hAnnInt
        (fun r hr => (hFloor r hr).le)
      calc
        w * (H / 4) = (t - (t - w)) * (H / 4) := by ring
        _ ≤ _ := hCost
    have hAnnLeD : (∫ r in (t - w)..t, Ann r ∂volume) ≤
        ∫ r in (t - w)..t, D r ∂volume := by
      apply intervalIntegral.integral_mono_on
        (by linarith only [hw] : t - w ≤ t) hAnnInt hDWin
      intro r hr
      exact h3Path_actualFiniteAnnulusDissipation_le_fullAt244
        hH3 hClass r (hSub hr) ((R : ℝ) + 1) ((N : ℝ) + 1)
    have hGapCost : (∫ r in (t - w)..t, D r ∂volume) ≤
        ∫ r in x..y, D r ∂volume :=
      intervalIntegral.integral_mono_interval
        hBackward.le (by linarith only [hw] : t - w ≤ t) ht.2
        hNonneg hDGap
    exact ⟨Or.inr hBackward, (hAnnCost.trans hAnnLeD).trans hGapCost⟩

/-- HARD PHYSICAL RATE/CLOCK GATE: every gamma-free adverse high-radial
signed flux at any point of the original gap forces either clock-times-height
compression or a squared-height kinetic-rate charge on that SAME gap. -/
theorem thirdFullPhysical_signedLowMax_gammaFreeTail_kineticRateOrClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (x y t : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T)
    (hxy : x < y) (ht : t ∈ Set.Icc x y)
    (eta : ℝ) (hEta : 0 < eta)
    (hTail : eta / 2 ≤
      thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) :
    ∃ N : ℕ, R ≤ N ∧
      (let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
           R eta (velocityH3EnergyAt u t)
       let L := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R N
           (velocityH3Energy0At u b)
       let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
       (y - x) * H ≤ 16 * D ∨ H ^ 2 ≤ 32 * (L + 1) * D) := by
  let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  have hxClass : x ∈ Set.Ioo a T := ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hyClass : y ∈ Set.Ioo a T := ⟨lt_trans hb.1 hy.1, hy.2⟩
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hxClass.1 ht.1, lt_of_le_of_lt ht.2 hyClass.2⟩
  obtain ⟨hH, hHigh⟩ :=
    thirdFullPhysical_signedLowMax_gammaFreeTail_linearHighRadialFloor244
      hH3 hClass R t htClass eta hEta hTail
  have hWindow : ThirdFullKineticSignedLowMaxCertifiedAnnularWindow244
      hH3 R H t :=
    thirdFullPhysical_highRadialHeight_to_signedCertifiedWindow244
      hH3 hClass t htClass R H hH hHigh
  obtain ⟨N, w, hRN, hwEq, hw, _hSide, hCost⟩ :=
    thirdFullPhysical_signedLowMax_symmetricKineticInGapCharge244
      hH3 hClass hDInt b hb R H x y t hH hx hy hxy ht hWindow
  refine ⟨N, hRN, ?_⟩
  let L : ℝ := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R N
    (velocityH3Energy0At u b)
  let D : ℝ := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  have hL : 0 ≤ L := thirdFullKinetic_signedLowMax_kineticAnnulusRate_nonneg244 R N _
  have hCost' : min ((y - x) / 4) (H / (8 * (L + 1))) * (H / 4) ≤ D := by
    simpa only [hwEq, thirdFullKineticSignedLowMaxSymmetricGapWidth244,
      L, D] using hCost
  exact thirdFullKinetic_signedLowMax_symmetricCharge_clockOrRate244
    x y H L D hH hL hxy hCost'

/-- Vanishing actual H3 dissipation on the ORIGINAL cofinal kinetic gaps
forces, for EVERY selected gamma-free high-radial carrier, either kinetic gap
clock compression or squared-height compression against the actual finite
annulus rate. The chosen annulus Q can move; there is no Q-uniform rate bound. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tailRateOrClock244
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
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (R : ℕ) (t : ℝ),
        t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        (eta / 2 ≤
          thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
            (velocityH3EnergyAt u t) *
            ‖thirdFullSpectralVelocityHighRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) →
        ∃ Q : ℕ, R ≤ Q ∧
          (let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
                R eta (velocityH3EnergyAt u t)
           let L := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R Q
                (velocityH3Energy0At u b)
           ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * H <
             16 * epsilon) ∨ (H ^ 2 < 32 * (L + 1) * epsilon)) := by
  have hDZero := thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated hWindows
  have hDsmall : ∀ᶠ k : ℕ in atTop,
      (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume) < epsilon :=
    hDZero.eventually (eventually_lt_nhds hEpsilon)
  filter_upwards [hDsmall] with k hk
  intro R t ht hTail
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  have hx : x ∈ Set.Ioo b T := by
    obtain ⟨hTime, hw⟩ := hWindows k
    rcases hw with ⟨_, hdelta, _, hEnd, _, _⟩
    exact ⟨by linarith only [hTime.1, hdelta], hEnd⟩
  have hy : y ∈ Set.Ioo b T := (hWindows (k + 1)).1
  have hxy : x < y := hSeparated k (k + 1) (Nat.lt_succ_self k)
  obtain ⟨Q, hRQ, hAlt⟩ :=
    thirdFullPhysical_signedLowMax_gammaFreeTail_kineticRateOrClock244
      hH3 hClass hDInt b hb R x y t hx hy hxy ht eta hEta hTail
  refine ⟨Q, hRQ, ?_⟩
  let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  let L : ℝ := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R Q
    (velocityH3Energy0At u b)
  let D : ℝ := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  have hL : 0 ≤ L := thirdFullKinetic_signedLowMax_kineticAnnulusRate_nonneg244 R Q _
  have hD : D < epsilon := hk
  change (y - x) * H ≤ 16 * D ∨ H ^ 2 ≤ 32 * (L + 1) * D at hAlt
  change (y - x) * H < 16 * epsilon ∨ H ^ 2 < 32 * (L + 1) * epsilon
  rcases hAlt with hClock | hRate
  · exact Or.inl (lt_of_le_of_lt hClock
      (mul_lt_mul_of_pos_left hD (by norm_num)))
  · have hCoefficient : 0 < 32 * (L + 1) := by
      have hOne : 0 < L + 1 := by linarith only [hL]
      positivity
    exact Or.inr (lt_of_le_of_lt hRate
      (mul_lt_mul_of_pos_left hD hCoefficient))

end
end PrimeTensor.FirstMonomialTriad

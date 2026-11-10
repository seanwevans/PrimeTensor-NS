import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCertifiedEleventhFrequencyCharge
import Mathlib.Tactic

/-!
# Signed sixth flux: certified frequency-time compression on the original gaps

The previous theorem produced an ACTUAL annular H3 dissipation peak at a
physical cutoff Q, an exact symmetric in-gap width w, and a nonzero gap
charge. The cutoff Q cannot be replaced by an arbitrary large integer.

This module identifies the RATE branch of the exact minimum under the
already-used low-relative-density hypothesis. It proves the two-sided
frequency-time concentration constraint, at the SAME physical annulus:

  h <= 8 K(E0) (Q+1)^11 w,       w h <= 4 D,

where h>0 is the capped physical height floor and D is actual full-H3
kinetic-gap dissipation. In particular D(k)->0 makes these widths vanish;
the previously proved eleventh-power charge makes their physical outer
cutoffs escape every fixed B. Neither assertion eliminates concentration.

The cofinal physical result retains the actual annular peak, exact width,
and integrated gap charge, under the original tenth-power residual exclusion.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Low relative gap dissipation excludes the gap-quarter branch of the
EXACT symmetric annular persistence width. The remaining width is the
kinetic annular rate width; no frequency cutoffs have been forgotten. -/
theorem thirdFullKinetic_signedLowMax_lowDensity_forcesRateWidth244
    (R Q : ℕ) (E0 H h x y w D : ℝ)
    (hxy : x < y) (hHeight : h ≤ H)
    (hw : w = thirdFullKineticSignedLowMaxSymmetricGapWidth244
      R Q E0 H x y)
    (hCost : w * (H / 4) ≤ D)
    (hLowDensity : 16 * D < (y - x) * h) :
    w = H / (8 * (thirdFullKineticSignedLowMaxKineticAnnulusRate244
      R Q E0 + 1)) := by
  let L : ℝ := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R Q E0
  have hGap : 0 ≤ y - x := sub_nonneg.mpr hxy.le
  have hLowH : 16 * D < (y - x) * H :=
    lt_of_lt_of_le hLowDensity
      (mul_le_mul_of_nonneg_left hHeight hGap)
  by_cases hLeft : (y - x) / 4 ≤ H / (8 * (L + 1))
  · have hWidth : w = (y - x) / 4 := by
      rw [hw, thirdFullKineticSignedLowMaxSymmetricGapWidth244]
      exact min_eq_left hLeft
    have hClock : (y - x) * H ≤ 16 * D := by
      rw [hWidth] at hCost
      nlinarith only [hCost]
    exact False.elim ((not_lt_of_ge hClock) hLowH)
  · have hRight : H / (8 * (L + 1)) ≤ (y - x) / 4 :=
      (lt_of_not_ge hLeft).le
    rw [hw, thirdFullKineticSignedLowMaxSymmetricGapWidth244,
      min_eq_right hRight]

/-- Genuine annular time-frequency localization. The WIDTH cannot be
smaller than an inverse eleventh-power rate without violating its actual
kinetic Lipschitz modulus; the same width cannot be larger than the true
physical dissipation budget. These are simultaneous inequalities for
ONE certified annulus Q and ONE width w. -/
theorem thirdFullKinetic_signedLowMax_certifiedWidth_twoSided244
    (R Q : ℕ) (E0 H h x y w D : ℝ)
    (hE : 0 ≤ E0) (hH : 0 < H) (hh : 0 < h)
    (hHeight : h ≤ H) (hxy : x < y) (hRQ : R ≤ Q)
    (hwPos : 0 < w)
    (hw : w = thirdFullKineticSignedLowMaxSymmetricGapWidth244
      R Q E0 H x y)
    (hCost : w * (H / 4) ≤ D)
    (hLowDensity : 16 * D < (y - x) * h) :
    h ≤ 8 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
        ((Q : ℝ) + 1) ^ 11 * w ∧
      w * h ≤ 4 * D := by
  let L : ℝ := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R Q E0
  let K : ℝ := thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0
  have hL : 0 ≤ L :=
    thirdFullKinetic_signedLowMax_kineticAnnulusRate_nonneg244 R Q E0
  have hL1 : 0 < L + 1 := by linarith only [hL]
  have hDen : 0 < 8 * (L + 1) := by positivity
  have hwRate : w = H / (8 * (L + 1)) := by
    simpa only [L] using
      (thirdFullKinetic_signedLowMax_lowDensity_forcesRateWidth244
        R Q E0 H h x y w D hxy hHeight hw hCost hLowDensity)
  have hIdentity : H = w * (8 * (L + 1)) := by
    rw [hwRate]
    rw [div_mul_cancel₀ _ hDen.ne']
  have hCap : L + 1 ≤ K * ((Q : ℝ) + 1) ^ 11 := by
    simpa only [L, K] using
      (thirdFullKinetic_signedLowMax_twoAnnularRates_le_eleventh244
        R Q E0 hE hRQ)
  have hScaled : 8 * (L + 1) ≤ 8 * (K * ((Q : ℝ) + 1) ^ 11) :=
    mul_le_mul_of_nonneg_left hCap (by norm_num)
  have hProduct : w * (8 * (L + 1)) ≤
      w * (8 * (K * ((Q : ℝ) + 1) ^ 11)) :=
    mul_le_mul_of_nonneg_left hScaled hwPos.le
  have hCost4 : w * H ≤ 4 * D := by
    nlinarith only [hCost]
  have hHeightScaled : w * h ≤ w * H :=
    mul_le_mul_of_nonneg_left hHeight hwPos.le
  constructor
  · calc
      h ≤ H := hHeight
      _ = w * (8 * (L + 1)) := hIdentity
      _ ≤ w * (8 * (K * ((Q : ℝ) + 1) ^ 11)) := hProduct
      _ = 8 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
          ((Q : ℝ) + 1) ^ 11 * w := by
        dsimp only [K]
        ring
  · exact hHeightScaled.trans hCost4

/-- No choice of moving annuli can prevent their certified widths from
shrinking on disjoint physical gaps with D(k)->0, provided the height
stays above the same positive physical floor h. -/
theorem thirdFullKinetic_signedLowMax_gapDissipation_forcesWidthCollapse244
    (D : ℕ → ℝ) (h : ℝ) (hh : 0 < h)
    (hDZero : Tendsto D atTop (𝓝 (0 : ℝ)))
    (zeta : ℝ) (hzeta : 0 < zeta) :
    ∀ᶠ k : ℕ in atTop, ∀ (w H : ℝ),
      0 ≤ w → h ≤ H → w * (H / 4) ≤ D k → w < zeta := by
  have hTarget : 0 < zeta * h / 4 := by positivity
  have hSmall : ∀ᶠ k : ℕ in atTop,
      D k < zeta * h / 4 :=
    hDZero.eventually (eventually_lt_nhds hTarget)
  filter_upwards [hSmall] with k hk
  intro w H hw hHeight hCost
  have hCost4 : w * H ≤ 4 * D k := by
    nlinarith only [hCost]
  have hLower : w * h ≤ w * H :=
    mul_le_mul_of_nonneg_left hHeight hw
  have hBound : w * h ≤ 4 * D k := hLower.trans hCost4
  have hStrict : 4 * D k < zeta * h := by
    nlinarith only [hk]
  have hDiv : w ≤ (4 * D k) / h :=
    (le_div_iff₀ hh).mpr hBound
  exact hDiv.trans_lt ((div_lt_iff₀ hh).mpr hStrict)

/-- Physical cofinal simultaneous frequency-escape AND time-compression.
The SAME certified annulus Q>B supports the positive physical H3 peak,
its original in-gap charge, and the exact width; on every sufficiently
late qualifying original gap its persistence width is below any prescribed
positive zeta, while the inverse-frequency width floor remains valid.
No assumption about index-weighted dissipation is made. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_certifiedFrequencyTimeCompression244
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
    (J B : ℕ) (E epsilon zeta : ℝ)
    (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) (hzeta : 0 < zeta) :
    ∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      let x := tau (v k) + delta (v k)
      let y := tau (v (k + 1))
      let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
        R eta (velocityH3EnergyAt u t)
      let h := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
      let E0 := velocityH3Energy0At u b
      let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
      t ∈ Set.Icc x y →
      eta < -velocityH3TransportDerivative3At u t →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon x y t →
      16 * D < (y - x) * h →
      ∃ (Q : ℕ) (w : ℝ),
        R ≤ Q ∧ B < Q ∧
        w = thirdFullKineticSignedLowMaxSymmetricGapWidth244
          R Q E0 H x y ∧
        0 < w ∧ w < zeta ∧
        h ≤ 8 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
          ((Q : ℝ) + 1) ^ 11 * w ∧
        w * h ≤ 4 * D ∧
        H / 2 <
          h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) ∧
        w * (H / 4) ≤ D := by
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let E0 : ℝ := velocityH3Energy0At u b
  let D : ℕ → ℝ := fun k =>
    ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
      velocityH3DissipationAt u r ∂volume
  have hh : 0 < h :=
    thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244 eta E hEta hE
  have hDZero : Tendsto D atTop (𝓝 (0 : ℝ)) := by
    simpa only [D] using
      (thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
        hH3 hClass hDInt b hb M tau N delta v
        hLimit hSeparated hWindows)
  have hShrink := thirdFullKinetic_signedLowMax_gapDissipation_forcesWidthCollapse244
    D h hh hDZero zeta hzeta
  have hPhysical := thirdFullPhysical_kineticGaps_signedLowMax_certifiedOuterBeyondFixed244
    hH3 hClass hDInt b hb M tau N delta v
    hLimit hSeparated hWindows eta hEta J B E epsilon hE hEpsilon
  filter_upwards [hPhysical, hShrink] with k hkPhysical hkShrink
  intro R t
  dsimp only
  intro ht hAdverse hNoResidual hLowDensity
  obtain ⟨Q, w, hRQ, hBQ, hwPos, hwEq, hPeak, hCost, _hCharge⟩ :=
    hkPhysical R t ht hAdverse hNoResidual hLowDensity
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  have hCap : velocityH3EnergyAt u t ≤ E := by
    by_contra hn
    have hBadEnergy : E < velocityH3EnergyAt u t := lt_of_not_ge hn
    apply hNoResidual
    unfold ThirdFullKineticSignedLowMaxTenthPowerResidual244
    exact Or.inr (Or.inl (Or.inr (Or.inl hBadEnergy)))
  have hEt0 : 0 ≤ velocityH3EnergyAt u t := by
    have hOne := one_le_velocityH3EnergyAt u t
    linarith only [hOne]
  have hHeight : h ≤ H :=
    thirdFullKinetic_signedLowMax_linearHeight_ge_cappedFloor244
      R eta (velocityH3EnergyAt u t) E hEta hEt0 hCap
  have hH : 0 < H := lt_of_lt_of_le hh hHeight
  have hxy : x < y :=
    hSeparated k (k + 1) (Nat.lt_succ_self k)
  have hE0 : 0 ≤ E0 := velocityH3Energy0At_nonneg u b
  have hTwoSided :
      h ≤ 8 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
        ((Q : ℝ) + 1) ^ 11 * w ∧
      w * h ≤ 4 * D k :=
    thirdFullKinetic_signedLowMax_certifiedWidth_twoSided244
      R Q E0 H h x y w (D k) hE0 hH hh hHeight hxy hRQ
      hwPos hwEq hCost hLowDensity
  have hWidthSmall : w < zeta :=
    hkShrink w H hwPos.le hHeight hCost
  exact ⟨Q, w, hRQ, hBQ, hwEq, hwPos, hWidthSmall,
    hTwoSided.1, hTwoSided.2, hPeak, hCost⟩

end
end PrimeTensor.FirstMonomialTriad

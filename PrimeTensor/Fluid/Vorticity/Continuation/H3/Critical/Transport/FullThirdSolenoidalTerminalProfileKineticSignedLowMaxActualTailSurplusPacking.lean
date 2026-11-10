import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxTenthResidualVacuityAudit
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCertifiedEleventhFrequencyCharge
import Mathlib.Tactic

/-!
# Signed sixth flux: nonvacuous high-radial carrier on actual surplus gaps

The audited tenth-power residual is automatic on any strict gap: its final
branch can choose an arbitrarily small width. Consequently excluding that
residual cannot select actual annular activity.

This module BYPASSES the residual. Instead it tests an actual physical
high-radial Fourier carrier at a strict-time adverse signed-transport sample.
The accepted gamma-free high-tail theorem then constructs a real H3 annular
peak, exact kinetic persistence width and integrated eleventh-power charge.
Those same certified annuli pay a single global H3 dissipation budget, with
frequency occupancy and eventual cutoff escape on the original gaps.

The actual high-tail carrier is a substantial physical condition. Strict
integrated signed surplus alone does NOT imply that carrier in this module.
Neither activity recurrence nor Navier--Stokes continuation is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology Classical
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A genuinely physical event: integrated signed surplus on an original
inter-window gap, a low relative dissipation charge, and an ACTUAL adverse
sample whose physical high-radial carrier is above the signed threshold.
No existential short viscous width, tenth-power residual or annular cutoff
occurs in this predicate. -/
def ThirdFullKineticSignedLowMaxActualTailSurplusActive244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (eta E : ℝ) (tau delta : ℕ → ℝ) (v R : ℕ → ℕ)
    (k : ℕ) : Prop :=
  let x := tau (v k) + delta (v k)
  let y := tau (v (k + 1))
  let h := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  thirdFullKineticGapLowOrderMargin244 u eta x y <
      thirdFullKineticGapSignedSurplus244 u x y ∧
    16 * D < (y - x) * h ∧
    ∃ z : ℝ, z ∈ Set.Icc x y ∧
      eta < -velocityH3TransportDerivative3At u z ∧
      velocityH3EnergyAt u z ≤ E ∧
      eta / 2 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u z) *
        ‖thirdFullSpectralVelocityHighRadialApply244 (R k)
          (h3AuditActualSpectralVelocityTotal hH3 z)‖ ^ 2

/-- The existing exact physical signed-surplus integral supplies the
adverse time. If EVERY such adverse sample is physically high-tail
carrying under the prescribed energy cap, the new meaningful activity
predicate holds. The universal carrier premise is an OPEN PDE gate, not
an inference from the audited tenth-power residual. -/
theorem thirdFullPhysical_signedLowMax_surplus_uniformTail_forcesActivity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x < y) (eta E : ℝ) (hEta : 0 < eta) (R : ℕ)
    (hSurplus : thirdFullKineticGapLowOrderMargin244 u eta x y <
      thirdFullKineticGapSignedSurplus244 u x y)
    (hLow : 16 * (∫ r in x..y, velocityH3DissipationAt u r ∂volume) <
      (y - x) * thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E)
    (hCarrier : ∀ z : ℝ, z ∈ Set.Icc x y →
      eta < -velocityH3TransportDerivative3At u z →
      velocityH3EnergyAt u z ≤ E ∧
      eta / 2 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u z) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 z)‖ ^ 2) :
    ∃ z : ℝ, z ∈ Set.Icc x y ∧
      eta < -velocityH3TransportDerivative3At u z ∧
      velocityH3EnergyAt u z ≤ E ∧
      eta / 2 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u z) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 z)‖ ^ 2 := by
  obtain ⟨z, hz, hAdverse⟩ :=
    thirdFullPhysical_gapSignedSurplus_producesCommonAdverseTime244
      hH3 hClass x y eta hx hy hxy hEta hSurplus
  obtain ⟨hCap, hTail⟩ := hCarrier z hz hAdverse
  exact ⟨z, hz, hAdverse, hCap, hTail⟩

/-- Direct genuine-annulus certification, with NO tenth-power residual
negation. The carrier is an actual Fourier inequality at the SAME physical
time as the peak; the width is the EXACT kinetic-rate persistence width.
The old arbitrary-width existential cannot discharge this theorem. -/
theorem thirdFullPhysical_signedLowMax_actualTail_certifiedNoResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (x y t : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T)
    (hxy : x < y) (ht : t ∈ Set.Icc x y)
    (eta E : ℝ) (hEta : 0 < eta) (hE : 0 ≤ E)
    (hEnergyCap : velocityH3EnergyAt u t ≤ E)
    (hTail : eta / 2 ≤
      thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2)
    (hLowDensity :
      16 * (∫ r in x..y, velocityH3DissipationAt u r ∂volume) <
        (y - x) * thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) :
    let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
      R eta (velocityH3EnergyAt u t)
    let h := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
    let E0 := velocityH3Energy0At u b
    let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
    ∃ (Q : ℕ) (w : ℝ), R ≤ Q ∧ 0 < w ∧
      w = thirdFullKineticSignedLowMaxSymmetricGapWidth244 R Q E0 H x y ∧
      H / 2 <
        h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      w * (H / 4) ≤ D ∧
      h ^ 2 / (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0) ≤
        ((Q : ℝ) + 1) ^ 11 * D := by
  exact thirdFullPhysical_signedLowMax_lowDensity_certifiedEleventh244
    hH3 hClass hDInt b hb R x y t hx hy hxy ht
    eta E hEta hE hEnergyCap hTail hLowDensity

/-- Physical global packing from a NONVACUOUS Fourier carrier gate.
Exactly the active original kinetic gaps are selected; there is no
arbitrary viscous width and no negation of the automatic residual.
The same physical annulus Q and its exact width w appear in the certificate,
inverse-eleventh budget, fixed-frequency occupancy and eventual cutoff escape.
An active gap must exhibit BOTH signed surplus and a real adverse high-tail
carrier. No theorem here asserts that such gaps recur. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_actualTailSurplusGlobalPacking244
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
    (eta E : ℝ) (hEta : 0 < eta) (hE : 0 ≤ E)
    (R : ℕ → ℕ) :
    ∃ (active : ℕ → Prop) (t : ℕ → ℝ) (Q : ℕ → ℕ) (w : ℕ → ℝ),
      (∀ k : ℕ, active k ↔
        ThirdFullKineticSignedLowMaxActualTailSurplusActive244
          hH3 eta E tau delta v R k) ∧
      (∀ k : ℕ, active k →
        t k ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) ∧
        eta < -velocityH3TransportDerivative3At u (t k) ∧
        velocityH3EnergyAt u (t k) ≤ E ∧
        eta / 2 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
          (velocityH3EnergyAt u (t k)) *
          ‖thirdFullSpectralVelocityHighRadialApply244 (R k)
            (h3AuditActualSpectralVelocityTotal hH3 (t k))‖ ^ 2 ∧
        ThirdFullKineticSignedLowMaxGapPackingCertificate244
          hH3 eta b tau delta v R Q t w k ∧
        (thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2 /
          (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
            (velocityH3Energy0At u b)) ≤
          ((Q k : ℝ) + 1) ^ 11 *
            (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
              velocityH3DissipationAt u r ∂volume)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          if active k then
            ((thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2 /
              (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
                (velocityH3Energy0At u b))) / (((Q k : ℝ) + 1) ^ 11)
          else 0) ≤
        ∫ r in a..T, velocityH3DissipationAt u r ∂volume) ∧
      (∀ (B m : ℕ),
        thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244 active Q B m *
          ((thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2 /
            (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
              (velocityH3Energy0At u b))) ≤
          ((B : ℝ) + 1) ^ 11 *
            (∫ r in a..T, velocityH3DissipationAt u r ∂volume)) ∧
      (∀ B : ℕ, ∀ᶠ k : ℕ in atTop, active k → B < Q k) := by
  classical
  let active : ℕ → Prop := fun k =>
    ThirdFullKineticSignedLowMaxActualTailSurplusActive244
      hH3 eta E tau delta v R k
  let x : ℕ → ℝ := fun k => tau (v k) + delta (v k)
  let y : ℕ → ℝ := fun k => tau (v (k + 1))
  let D : ℕ → ℝ := fun k =>
    ∫ r in x k..y k, velocityH3DissipationAt u r ∂volume
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let E0 : ℝ := velocityH3Energy0At u b
  let K : ℝ := thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0
  let c : ℝ := h ^ 2 / (32 * K)
  have hh : 0 < h :=
    thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244 eta E hEta hE
  have hE0 : 0 ≤ E0 := velocityH3Energy0At_nonneg u b
  have hK : 0 < K :=
    thirdFullKinetic_signedLowMax_criticalTwelveCoeff_pos244 E0 hE0
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (pow_pos hh 2) (mul_pos (by norm_num) hK)
  have hxy (k : ℕ) : x k < y k :=
    hSeparated k (k + 1) (Nat.lt_succ_self k)
  have hx (k : ℕ) : x k ∈ Set.Ioo b T := by
    obtain ⟨hTime, hWindow⟩ := hWindows k
    rcases hWindow with ⟨_, hdelta, _, hEnd, _, _⟩
    exact ⟨by dsimp only [x]; linarith only [hTime.1, hdelta], hEnd⟩
  have hy (k : ℕ) : y k ∈ Set.Ioo b T :=
    (hWindows (k + 1)).1
  have hAnyTime (k : ℕ) :
      ∃ z : ℝ, active k →
        z ∈ Set.Icc (x k) (y k) ∧
        eta < -velocityH3TransportDerivative3At u z ∧
        velocityH3EnergyAt u z ≤ E ∧
        eta / 2 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
          (velocityH3EnergyAt u z) *
          ‖thirdFullSpectralVelocityHighRadialApply244 (R k)
            (h3AuditActualSpectralVelocityTotal hH3 z)‖ ^ 2 := by
    by_cases hk : active k
    · have hEvent := hk
      dsimp only [active, ThirdFullKineticSignedLowMaxActualTailSurplusActive244]
        at hEvent
      obtain ⟨_hSurplus, _hLow, z, ht, hAdverse, hCap, hTail⟩ := hEvent
      exact ⟨z, fun _ => ⟨by simpa only [x, y] using ht,
        hAdverse, hCap, hTail⟩⟩
    · exact ⟨0, fun ha => False.elim (hk ha)⟩
  let t : ℕ → ℝ := fun k => Classical.choose (hAnyTime k)
  have hAt (k : ℕ) (hk : active k) :
      t k ∈ Set.Icc (x k) (y k) ∧
      eta < -velocityH3TransportDerivative3At u (t k) ∧
      velocityH3EnergyAt u (t k) ≤ E ∧
      eta / 2 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u (t k)) *
        ‖thirdFullSpectralVelocityHighRadialApply244 (R k)
          (h3AuditActualSpectralVelocityTotal hH3 (t k))‖ ^ 2 :=
    (Classical.choose_spec (hAnyTime k)) hk
  have hLowDensity (k : ℕ) (hk : active k) :
      16 * D k < (y k - x k) * h := by
    have hEvent := hk
    dsimp only [active, ThirdFullKineticSignedLowMaxActualTailSurplusActive244]
      at hEvent
    simpa only [D, x, y, h] using hEvent.2.1
  have hAnyAnnulus (k : ℕ) :
      ∃ (q : ℕ) (ww : ℝ), active k →
        ThirdFullKineticSignedLowMaxNativeSelectedAnnulus244
          hH3 eta b tau delta v R t k q ww ∧
        c ≤ ((q : ℝ) + 1) ^ 11 * D k := by
    by_cases hk : active k
    · obtain ⟨ht, _hAdverse, hCap, hTail⟩ := hAt k hk
      have hLow :
          16 * (∫ r in x k..y k, velocityH3DissipationAt u r ∂volume) <
            (y k - x k) * h := hLowDensity k hk
      obtain ⟨q, ww, hRQ, hwwPos, hwwEq, hPeak, hCost, hCharge⟩ :=
        thirdFullPhysical_signedLowMax_actualTail_certifiedNoResidual244
          hH3 hClass hDInt b hb (R k) (x k) (y k) (t k)
          (hx k) (hy k) (hxy k) ht
          eta E hEta hE hCap hTail
          (by simpa only [h] using hLow)
      have hNative : ThirdFullKineticSignedLowMaxNativeSelectedAnnulus244
          hH3 eta b tau delta v R t k q ww := by
        change (R k ≤ q ∧ 0 < ww ∧
          ww = thirdFullKineticSignedLowMaxSymmetricGapWidth244
            (R k) q E0
            (thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
              (R k) eta (velocityH3EnergyAt u (t k))) (x k) (y k) ∧
          (thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
              (R k) eta (velocityH3EnergyAt u (t k))) / 2 <
            h3PathActualLowRadialDissipation244 ((q : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (t k)) -
            h3PathActualLowRadialDissipation244 (((R k : ℝ) + 1))
              (h3AuditActualSpectralVelocityTotal hH3 (t k)) ∧
          ww * ((thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
            (R k) eta (velocityH3EnergyAt u (t k))) / 4) ≤ D k)
        exact ⟨hRQ, hwwPos, hwwEq, hPeak, hCost⟩
      have hPaid : c ≤ ((q : ℝ) + 1) ^ 11 * D k := by
        simpa only [c, h, K, E0, D, x, y] using hCharge
      exact ⟨q, ww, fun _ => ⟨hNative, hPaid⟩⟩
    · exact ⟨0, 0, fun ha => False.elim (hk ha)⟩
  let Q : ℕ → ℕ := fun k => Classical.choose (hAnyAnnulus k)
  let w : ℕ → ℝ := fun k =>
    Classical.choose (Classical.choose_spec (hAnyAnnulus k))
  have hPicked (k : ℕ) (hk : active k) :
      ThirdFullKineticSignedLowMaxNativeSelectedAnnulus244
        hH3 eta b tau delta v R t k (Q k) (w k) ∧
      c ≤ ((Q k : ℝ) + 1) ^ 11 * D k :=
    (Classical.choose_spec (Classical.choose_spec (hAnyAnnulus k))) hk
  have hCert (k : ℕ) (hk : active k) :
      ThirdFullKineticSignedLowMaxGapPackingCertificate244
        hH3 eta b tau delta v R Q t w k := by
    obtain ⟨hNative, _⟩ := hPicked k hk
    rcases hNative with ⟨hRQ, hPos, hwEq, hPeak, hCost⟩
    exact ⟨(hAt k hk).1, hRQ, hPos, hwEq, hPeak, hCost⟩
  have hCap (k : ℕ) (hk : active k) :
      velocityH3EnergyAt u (t k) ≤ E := (hAt k hk).2.2.1
  have hLow (k : ℕ) (hk : active k) :
      16 * (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume) <
      (tau (v (k + 1)) - (tau (v k) + delta (v k))) *
        thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E := by
    simpa only [D, x, y, h] using hLowDensity k hk
  have hCharge (k : ℕ) (hk : active k) :
      c ≤ ((Q k : ℝ) + 1) ^ 11 * D k := (hPicked k hk).2
  have hDZero : Tendsto D atTop (𝓝 (0 : ℝ)) := by
    simpa only [D, x, y] using
      (thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
        hH3 hClass hDInt b hb M tau N delta v
        hLimit hSeparated hWindows)
  refine ⟨active, t, Q, w, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rfl
  · intro k hk
    have hs := hAt k hk
    refine ⟨?_, hs.2.1, hs.2.2.1, hs.2.2.2, hCert k hk, ?_⟩
    · simpa only [x, y] using hs.1
    · simpa only [c, h, K, E0, D, x, y] using hCharge k hk
  · intro m
    have hPacked :=
      thirdFullPhysical_kineticGaps_signedLowMax_certifiedFinitePacking244
        hH3 hClass hDInt b hb M tau N delta v hSeparated hWindows
        eta E hEta hE active R Q t w hCert hCap hLow m
    -- Compare the goal sum with the actual sum in `hPacked`.  Classical
    -- decidability instances for the same physical activity predicate may
    -- elaborate differently; the equality holds pointwise in both cases.
    refine (le_of_eq ?_).trans hPacked
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases ha : active k
    · simp only [if_pos ha]
    · simp only [if_neg ha]
  · intro B m
    exact thirdFullPhysical_kineticGaps_signedLowMax_certifiedFrequencyOccupancy244
      hH3 hClass hDInt b hb M tau N delta v hSeparated hWindows
      eta E hEta hE active R Q t w hCert hCap hLow B m
  · intro B
    have hPow : 0 < ((B : ℝ) + 1) ^ 11 := by positivity
    have hSmall : ∀ᶠ k : ℕ in atTop,
        D k < c / (((B : ℝ) + 1) ^ 11) :=
      hDZero.eventually (eventually_lt_nhds (div_pos hc hPow))
    filter_upwards [hSmall] with k hkSmall
    intro hk
    by_contra hn
    have hQB : Q k ≤ B := Nat.le_of_not_gt hn
    have hCast : (Q k : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hQB
    have hRad : (Q k : ℝ) + 1 ≤ (B : ℝ) + 1 := by
      linarith only [hCast]
    have hQpow : ((Q k : ℝ) + 1) ^ 11 ≤ ((B : ℝ) + 1) ^ 11 :=
      pow_le_pow_left₀ (by positivity) hRad 11
    have hDnonneg : 0 ≤ D k := by
      dsimp only [D]
      exact intervalIntegral.integral_nonneg (hxy k).le
        (fun r _ => velocityH3DissipationAt_nonneg u r)
    have hCompare := mul_le_mul_of_nonneg_right hQpow hDnonneg
    have hTooSmall : ((B : ℝ) + 1) ^ 11 * D k < c := by
      calc
        ((B : ℝ) + 1) ^ 11 * D k =
            D k * ((B : ℝ) + 1) ^ 11 := by ring
        _ < c := (lt_div_iff₀ hPow).mp hkSmall
    have hPaid := hCharge k hk
    exact (not_lt_of_ge (hPaid.trans hCompare)) hTooSmall

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousContainedPeakCharge
import Mathlib.Tactic

/-!
# Exact overlap envelope for two retained late physical PDE clocks

The primary interval [r,r+eta] has full H3-dissipation floor A. The
secondary interval [s,s+theta] starts at s >= r and has floor H.
Let L = min theta (max 0 (s+theta-(r+eta))) be the length of the
secondary interval OUTSIDE the primary one, and O = theta-L its
intersection length. The exact two-floor lower charge is

   eta*A + L*H + O*max 0 (H-A) <= integral_m^T D_H3.

This single statement handles disjoint, partial-overlap and containment.
It follows from the verified three-way packing plus the contained-peak
three-piece inequality. The two clock charges are never double counted.
The excess payment is conditional on H>A. No uniform-in-frequency
persistence estimate or Navier--Stokes continuation is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The secondary portion to the RIGHT of the primary endpoint. Under
r <= s and theta >= 0, this is between zero and theta. -/
noncomputable def thirdFullLateSecondaryOutsidePrimaryDuration244
    (r s eta theta : ℝ) : ℝ :=
  min theta (max 0 (s + theta - (r + eta)))

/-- Exact two-floor lower envelope paid by one nonnegative time-integral. -/
def ThirdFullLateExactTwoClockOverlapEnvelope244
    (A B r s eta theta H : ℝ) : Prop :=
  let L : ℝ := thirdFullLateSecondaryOutsidePrimaryDuration244 r s eta theta
  eta * A + L * H + (theta - L) * max 0 (H - A) ≤ B

/-- Eliminate the geometric three-way disjunction. On a disjoint pair,
the entire secondary window is outside; on containment it all lies
inside; on partial overlap, the stronger of the two floor estimates
pays for the intersection. -/
theorem thirdFull_scalar_twoClock_exactOverlap_from_packing244
    (A B r s eta theta H : ℝ)
    (hrs : r ≤ s) (htheta : 0 ≤ theta)
    (hPacking :
      max (eta * A)
        (max (min eta (s - r) * A + theta * H)
          (eta * A +
            thirdFullLateSecondaryOutsidePrimaryDuration244 r s eta theta * H)) ≤ B)
    (hContained : s + theta ≤ r + eta →
      eta * A + theta * max 0 (H - A) ≤ B) :
    ThirdFullLateExactTwoClockOverlapEnvelope244 A B r s eta theta H := by
  let L : ℝ := thirdFullLateSecondaryOutsidePrimaryDuration244 r s eta theta
  have hPrefix : min eta (s - r) * A + theta * H ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hPacking)
  have hSuffix : eta * A + L * H ≤ B :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hPacking)
  change eta * A + L * H + (theta - L) * max 0 (H - A) ≤ B
  by_cases hSeparated : r + eta ≤ s
  · have hBig : theta ≤ s + theta - (r + eta) := by
      linarith only [hSeparated]
    have hNonneg : 0 ≤ s + theta - (r + eta) :=
      htheta.trans hBig
    have hL : L = theta := by
      dsimp only [L, thirdFullLateSecondaryOutsidePrimaryDuration244]
      rw [max_eq_right hNonneg, min_eq_left hBig]
    have hPaid : eta * A + theta * H ≤ B := by
      simpa only [hL] using hSuffix
    simpa only [hL, sub_self, zero_mul, add_zero] using hPaid
  · have hOverlap : s ≤ r + eta := (lt_of_not_ge hSeparated).le
    by_cases hInside : s + theta ≤ r + eta
    · have hNonpos : s + theta - (r + eta) ≤ 0 := by
        linarith only [hInside]
      have hL : L = 0 := by
        dsimp only [L, thirdFullLateSecondaryOutsidePrimaryDuration244]
        rw [max_eq_left hNonpos, min_eq_right htheta]
      have hPaid := hContained hInside
      simpa only [hL, zero_mul, add_zero, sub_zero] using hPaid
    · have hCross : r + eta ≤ s + theta := le_of_not_ge hInside
      have hNonneg : 0 ≤ s + theta - (r + eta) := by
        linarith only [hCross]
      have hSmall : s + theta - (r + eta) ≤ theta := by
        linarith only [hOverlap]
      have hL : L = s + theta - (r + eta) := by
        dsimp only [L, thirdFullLateSecondaryOutsidePrimaryDuration244]
        rw [max_eq_right hNonneg, min_eq_right hSmall]
      by_cases hHA : H ≤ A
      · have hZero : max 0 (H - A) = 0 :=
          max_eq_left (sub_nonpos.mpr hHA)
        simpa only [hZero, mul_zero, add_zero] using hSuffix
      · have hAH : A ≤ H := le_of_lt (lt_of_not_ge hHA)
        have hMax : max 0 (H - A) = H - A :=
          max_eq_right (sub_nonneg.mpr hAH)
        have hTravel : s - r ≤ eta := by
          linarith only [hOverlap]
        have hMin : min eta (s - r) = s - r := min_eq_right hTravel
        calc
          eta * A + L * H + (theta - L) * max 0 (H - A) =
              min eta (s - r) * A + theta * H := by
                rw [hMax, hL, hMin]
                ring
          _ ≤ B := hPrefix

/-- A strict excess secondary height bounds the REAL temporal overlap
by the unused terminal action, after paying the primary and exterior
secondary portions. -/
theorem thirdFull_scalar_twoClock_overlapDuration_excessUpperBound244
    (A B r s eta theta H : ℝ)
    (hAH : A < H)
    (hCharge : ThirdFullLateExactTwoClockOverlapEnvelope244
      A B r s eta theta H) :
    theta - thirdFullLateSecondaryOutsidePrimaryDuration244 r s eta theta ≤
      (B - eta * A -
        thirdFullLateSecondaryOutsidePrimaryDuration244 r s eta theta * H) /
        (H - A) := by
  let L : ℝ := thirdFullLateSecondaryOutsidePrimaryDuration244 r s eta theta
  have hPos : 0 < H - A := sub_pos.mpr hAH
  have hMax : max 0 (H - A) = H - A := max_eq_right hPos.le
  change eta * A + L * H + (theta - L) * max 0 (H - A) ≤ B at hCharge
  rw [hMax] at hCharge
  apply (le_div_iff₀ hPos).2
  linarith only [hCharge]

/-- The exact overlap envelope holds for the ACTUAL retained primary
Navier--Stokes PDE clock and the SAME selected constructive secondary
clock, with no new PDE estimates. -/
theorem thirdFullPhysical_retainedPrimary_secondaryClock_exactOverlap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m r eta1 A sState sSource h : ℝ)
    (hm : m ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo m T)
    (heta1 : 0 < eta1) (hend1 : r + eta1 < T)
    (hFloor1 : ∀ x : ℝ, x ∈ Set.Icc r (r + eta1) →
      A < velocityH3DissipationAt u x)
    (hPrimary : eta1 * A ≤
      ∫ x in m..T, velocityH3DissipationAt u x ∂volume)
    (hsState : sState ∈ Set.Icc r (r + (T - r) / 2))
    (hsSource : sSource ∈ Set.Icc r (r + (T - r) / 2))
    (hSecondary : ThirdFullLateSecondaryPDEClock244
      hH3 m sState sSource h) :
    ∃ s eta2 : ℝ,
      (s = sState ∨ s = sSource) ∧ r ≤ s ∧
      0 < eta2 ∧ s + eta2 < T ∧
      ThirdFullLateExactTwoClockOverlapEnvelope244 A
        (∫ x in m..T, velocityH3DissipationAt u x ∂volume)
        r s eta1 eta2 (h / 2) := by
  obtain ⟨s, eta2, hWhich, hrs, heta2, hend2, hPacking, hContained⟩ :=
    thirdFullPhysical_retainedPrimary_secondaryClock_containedPeakPacking244
      hH3 hClass hDInt m r eta1 A sState sSource h
      hm hr heta1 hend1 hFloor1 hPrimary hsState hsSource hSecondary
  have hExact : ThirdFullLateExactTwoClockOverlapEnvelope244 A
      (∫ x in m..T, velocityH3DissipationAt u x ∂volume)
      r s eta1 eta2 (h / 2) := by
    apply thirdFull_scalar_twoClock_exactOverlap_from_packing244
      A (∫ x in m..T, velocityH3DissipationAt u x ∂volume)
      r s eta1 eta2 (h / 2) hrs heta2.le
    · simpa only [thirdFullLateSecondaryOutsidePrimaryDuration244] using hPacking
    · exact hContained
  exact ⟨s, eta2, hWhich, hrs, heta2, hend2, hExact⟩

/-- Keep the preceding full two-sided and contained-peak ledgers, while
attaching the exact unified overlap envelope on the SAME constructive
prescribed-gauge rate branch. No new frequency or time-width premise. -/
def ThirdFullLateRetainedPrimaryExactOverlapCofinalLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ)
    (sSource sState eta1 : ℝ) : Prop :=
  ThirdFullLateRetainedPrimaryContainedPeakCofinalLedger244
      hH3 b m r P V J sSource sState eta1 ∧
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  (T - r) * A ≤ 4 * B ∨ A ^ 2 ≤ 4 * B ∨
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B ∧
      (4 * R * B * E0 ^ 2 < A ^ 2 →
        ∃ s eta2 : ℝ,
          (s = sState ∨ s = sSource) ∧ r ≤ s ∧
          0 < eta2 ∧ s + eta2 < T ∧
          ThirdFullLateExactTwoClockOverlapEnvelope244 A B r s eta1 eta2
            (A / (24 * Real.sqrt (R * B)))))

/-- From the OLD contained-peak and max-packing certification derive
one exact overlap-charge certificate, without selecting a new secondary
clock or introducing any independence claim. -/
theorem thirdFullPhysical_containedPeakLedger_to_exactOverlap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ) (sSource sState eta1 : ℝ)
    (hLedger : ThirdFullLateRetainedPrimaryContainedPeakCofinalLedger244
      hH3 b m r P V J sSource sState eta1) :
    ThirdFullLateRetainedPrimaryExactOverlapCofinalLedger244
      hH3 b m r P V J sSource sState eta1 := by
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  have hOld := hLedger.2
  change (T - r) * A ≤ 4 * B ∨ A ^ 2 ≤ 4 * B ∨
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B ∧
      (4 * R * B * E0 ^ 2 < A ^ 2 →
        ∃ s eta2 : ℝ,
          (s = sState ∨ s = sSource) ∧ r ≤ s ∧
          0 < eta2 ∧ s + eta2 < T ∧
          (let H : ℝ := A / (24 * Real.sqrt (R * B));
            max (eta1 * A)
              (max (min eta1 (s - r) * A + eta2 * H)
                (eta1 * A +
                  (min eta2 (max 0 (s + eta2 - (r + eta1)))) * H)) ≤ B ∧
            (s + eta2 ≤ r + eta1 →
              eta1 * A + eta2 * max 0 (H - A) ≤ B)))) at hOld
  change ThirdFullLateRetainedPrimaryContainedPeakCofinalLedger244
      hH3 b m r P V J sSource sState eta1 ∧
    ((T - r) * A ≤ 4 * B ∨ A ^ 2 ≤ 4 * B ∨
      (A ^ 2 ≤ R *
          (E0 + 3 * velocityH3DissipationAt u sState) *
          (E0 + 3 * velocityH3DissipationAt u sSource) * B ∧
        (4 * R * B * E0 ^ 2 < A ^ 2 →
          ∃ s eta2 : ℝ,
            (s = sState ∨ s = sSource) ∧ r ≤ s ∧
            0 < eta2 ∧ s + eta2 < T ∧
            ThirdFullLateExactTwoClockOverlapEnvelope244 A B r s eta1 eta2
              (A / (24 * Real.sqrt (R * B))))))
  refine ⟨hLedger, ?_⟩
  rcases hOld with hTime | hTail | ⟨hRate, hConditional⟩
  · exact Or.inl hTime
  · exact Or.inr (Or.inl hTail)
  right; right
  refine ⟨hRate, ?_⟩
  intro hGap
  obtain ⟨s, eta2, hWhich, hrs, heta2, hend2, hPacking, hContained⟩ :=
    hConditional hGap
  let H : ℝ := A / (24 * Real.sqrt (R * B))
  have hPacking' :
      max (eta1 * A)
        (max (min eta1 (s - r) * A + eta2 * H)
          (eta1 * A +
            thirdFullLateSecondaryOutsidePrimaryDuration244 r s eta1 eta2 * H)) ≤ B := by
    simpa only [H, thirdFullLateSecondaryOutsidePrimaryDuration244] using hPacking
  have hContained' (hInside : s + eta2 ≤ r + eta1) :
      eta1 * A + eta2 * max 0 (H - A) ≤ B := by
    simpa only [H] using hContained hInside
  have hExact := thirdFull_scalar_twoClock_exactOverlap_from_packing244
    A B r s eta1 eta2 H hrs heta2.le hPacking' hContained'
  exact ⟨s, eta2, hWhich, hrs, heta2, hend2,
    by simpa only [H] using hExact⟩

/-- Same cofinal first-crossing witnesses, now with the ONE exact geometric
terminal-tail envelope on the constructive physical rate branch. The
old two-sided packing and contained peak charge are both retained. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_exactOverlapEnvelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (H : ℕ → ℝ) (hH : ∀ n : ℕ, 1 ≤ H n) :
    ∃ (U : H3PhysicalRealFinVectorL2Hilbert)
      (tau : ℕ → ℝ) (N : ℕ → ℕ) (K C delta : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => tau (v k)) atTop (𝓝 T) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244 hH3
        (fun n : ℕ => (H n) ^ 8) tau N K C delta (v k)) ∧
      (∀ j : ℕ,
        (∑ k ∈ Finset.range j,
          delta (v k) * ((H (v k)) ^ 8 / 4)) ≤
            ∫ s in a..T, velocityH3DissipationAt u s) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / H (v k)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        let t := tau (v k)
        let m := (t + T) / 2
        let Q := (N (v k) : ℝ) + 2
        let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
        let C0 := 3 + h3AuditInitialLerayEnergyCoefficient
        let E0 := 1 + 6 * velocityH3Energy0At u b
        let P := 168 * Q ^ 4 * (‖F‖ * C0) * (T - m)
        let V := (H (v k)) ^ 4
        V < 14 * Q ^ 4 *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
        (∃ r : ℝ, r ∈ Set.Icc t m ∧
          V < 28 * Q ^ 4 *
            (‖F‖ * ((m - t) *
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
        V < 56 * Q ^ 4 * (‖F‖ * C0 * ((T - m) * E0)) ∨
        (∃ (r : ℝ) (J : ℕ) (sSource sState eta1 : ℝ),
          r ∈ Set.Ioo m T ∧ 0 < P ∧
          sSource ∈ Set.Icc r (r + (T - r) / 2) ∧
          sState ∈ Set.Icc r (r + (T - r) / 2) ∧
          eta1 = min ((T - r) / 4)
            ((V / (2 * P)) /
              (2 * (thirdFullLateViscousLowRadialPDERate244 J
                ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
                ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ + 1))) ∧
          0 < eta1 ∧ r + eta1 < T ∧
          (∀ s : ℝ, s ∈ Set.Icc r (r + eta1) →
            V / (2 * P) <
              h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 s) ∧
            V / (2 * P) < velocityH3DissipationAt u s) ∧
          eta1 * (V / (2 * P)) ≤
            ∫ s in m..T, velocityH3DissipationAt u s ∂volume ∧
          ThirdFullLateRetainedPrimaryExactOverlapCofinalLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_containedPeakCofinalLedger244
      hH3 hClass b hb hNoTrace hDInt H hH
  refine ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
    hWindows, hCharges, hEscape, ?_, hViscousTail⟩
  filter_upwards [hOld] with k hkOld
  dsimp only at hkOld ⊢
  let t : ℝ := tau (v k)
  let m : ℝ := (t + T) / 2
  let Q : ℝ := (N (v k) : ℝ) + 2
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let P : ℝ := 168 * Q ^ 4 * (‖F‖ * C0) * (T - m)
  let V : ℝ := (H (v k)) ^ 4
  rcases hkOld with hCarrier | hSource | hClock |
      ⟨r, J, sSource, sState, eta1, hr, hP,
        hsSource, hsState, hEtaEq, heta1, hend1, hFloor, hCharge, hLedger⟩
  · exact Or.inl hCarrier
  · exact Or.inr (Or.inl hSource)
  · exact Or.inr (Or.inr (Or.inl hClock))
  · right; right; right
    have hExact :=
      thirdFullPhysical_containedPeakLedger_to_exactOverlap244
        hH3 b m r P V J sSource sState eta1 hLedger
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hExact⟩

end
end PrimeTensor.FirstMonomialTriad

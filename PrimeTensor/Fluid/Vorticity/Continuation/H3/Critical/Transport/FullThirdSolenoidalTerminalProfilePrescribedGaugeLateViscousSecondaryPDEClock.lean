import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousKineticTwoSliceGate
import Mathlib.Tactic

/-!
# Force a secondary physical PDE clock at an attained late H³ viscous observation

The preceding two-slice kinetic bridge converts the rate arm to

  A² ≤ 96 C₀ (J+2)^5 B (E₀+3D(sState)) (E₀+3D(sSource)),

with B = integral_(m)^T D, E₀ the fixed kinetic anchor, and C₀ the
fixed projected-momentum coefficient. This theorem handles the hard
logical implication without pretending two pointwise values are controlled
by an L¹ tail: if this rate arm exceeds the kinetic-only ceiling at a
threshold h>0, at least ONE of the actual attained physical times must
satisfy h<D(s). At that time the existing finite-band capture and exact
Navier--Stokes variation clock give a fresh interval, with

  eta = min ((T-s)/4) ((h/2)/(2*(Lambda(J2,K2,C2)+1))),
  h/2 < D_low,J2(t) ≤ D(t), eta*(h/2) ≤ integral_(m)^T D.

This new interval may intersect the old one, and its cutoff, maxima and
clock depend on the selected threshold. The same prescribed-gauge minimal
crossing witnesses, frequency escape, Fourier and kinetic alternatives,
and original disjoint viscous-charge bound are retained. No terminal-uniform
persistence width or new summability theorem is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A two-time physical viscous product cannot exceed a threshold-scaled
kinetic-only ceiling unless at least one actual physical dissipation value
exceeds the threshold. -/
theorem thirdFull_scalar_twoSliceRate_forces_actualViscousObservation244
    (A B R E DState DSource h : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hState : 0 ≤ DState) (hSource : 0 ≤ DSource)
    (hRate : A ^ 2 ≤
      R * (E + 3 * DState) * (E + 3 * DSource) * B)
    (hBeyond : R * (E + 3 * h) ^ 2 * B < A ^ 2) :
    h < DState ∨ h < DSource := by
  by_contra hNot
  push_neg at hNot
  have hStateLe : E + 3 * DState ≤ E + 3 * h := by
    linarith only [hNot.1]
  have hSourceLe : E + 3 * DSource ≤ E + 3 * h := by
    linarith only [hNot.2]
  have hStateNonneg : 0 ≤ E + 3 * DState := by
    linarith only [hE, hState]
  have hSourceNonneg : 0 ≤ E + 3 * DSource := by
    linarith only [hE, hSource]
  have hCeilNonneg : 0 ≤ E + 3 * h :=
    hStateNonneg.trans hStateLe
  have hProduct :
      (E + 3 * DState) * (E + 3 * DSource) ≤
        (E + 3 * h) ^ 2 := by
    calc
      _ ≤ (E + 3 * h) * (E + 3 * DSource) :=
        mul_le_mul_of_nonneg_right hStateLe hSourceNonneg
      _ ≤ (E + 3 * h) * (E + 3 * h) :=
        mul_le_mul_of_nonneg_left hSourceLe hCeilNonneg
      _ = (E + 3 * h) ^ 2 := by ring
  have hRB : 0 ≤ R * B := mul_nonneg hR hB
  have hBound :
      R * (E + 3 * DState) * (E + 3 * DSource) * B ≤
        R * (E + 3 * h) ^ 2 * B := by
    calc
      _ = (R * B) * ((E + 3 * DState) * (E + 3 * DSource)) := by ring
      _ ≤ (R * B) * (E + 3 * h) ^ 2 :=
        mul_le_mul_of_nonneg_left hProduct hRB
      _ = R * (E + 3 * h) ^ 2 * B := by ring
  exact (not_lt_of_ge (hRate.trans hBound)) hBeyond

/-- A physical secondary spike recorded at one of the original two attained
late times, together with a NEW finite cutoff and its explicit physical-PDE
persistence clock. The new interval is charged to the same real viscous tail. -/
def ThirdFullLateSecondaryPDEClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (m sState sSource h : ℝ) : Prop :=
  ∃ (s : ℝ), (s = sState ∨ s = sSource) ∧
    ∃ (J2 : ℕ) (zSource zState eta : ℝ),
      zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
      zState ∈ Set.Icc s (s + (T - s) / 2) ∧
      eta = min ((T - s) / 4)
        ((h / 2) / (2 * (thirdFullLateViscousLowRadialPDERate244 J2
          ‖h3AuditActualSpectralVelocityTotal hH3 zState‖
          ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ + 1))) ∧
      0 < eta ∧ s + eta < T ∧
      (∀ q : ℝ, q ∈ Set.Icc s (s + eta) →
        h / 2 < h3PathActualLowRadialDissipation244 ((J2 : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 q) ∧
        h / 2 < velocityH3DissipationAt u q) ∧
      eta * (h / 2) ≤
        ∫ q in m..T, velocityH3DissipationAt u q ∂volume

/-- Select whichever attained maximum has the high viscous observation.
Finite-band capture and the previously formalized EXACT late PDE clock
produce its own certified integrated cost, not a uniform time modulus. -/
theorem thirdFullPhysical_twoSelectedTimes_secondaryPDEClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m sState sSource h : ℝ)
    (hm : m ∈ Set.Ioo a T)
    (hsState : sState ∈ Set.Ioo m T)
    (hsSource : sSource ∈ Set.Ioo m T)
    (hh : 0 < h)
    (hPeak : h < velocityH3DissipationAt u sState ∨
      h < velocityH3DissipationAt u sSource) :
    ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource h := by
  obtain ⟨s, hChoice, hs, hSpike⟩ :
      ∃ (s : ℝ), (s = sState ∨ s = sSource) ∧
        s ∈ Set.Ioo m T ∧ h < velocityH3DissipationAt u s := by
    rcases hPeak with hState | hSource
    · exact ⟨sState, Or.inl rfl, hsState, hState⟩
    · exact ⟨sSource, Or.inr rfl, hsSource, hSource⟩
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hm.1 hs.1, hs.2⟩
  obtain ⟨J2, hCapture⟩ :=
    h3Critical_fullViscousSpike_has_finiteRadialCapture
      hH3 hClass s h hsClass hSpike
  have hCaptureScaled : h < (1 : ℝ) *
      h3PathActualLowRadialDissipation244 ((J2 : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
    simpa only [one_mul] using hCapture
  have hPDE := thirdFullPhysical_lateLowRadialSpike_explicitPDEClock244
    hH3 hClass hDInt m s (1 : ℝ) h J2
    hm hs (by norm_num) hh hCaptureScaled
  unfold ThirdFullLateSecondaryPDEClock244
  refine ⟨s, hChoice, J2, ?_⟩
  simpa only [mul_one] using hPDE

/-- From the late two-slice source-state product, every threshold exceeding
the kinetic-only rate charge forces a NEW physical finite-band time window
at ONE of the two actually attained late maxima. -/
theorem thirdFullPhysical_lateTwoSliceRate_forces_secondaryPDEClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m sState sSource A B R E : ℝ)
    (hm : m ∈ Set.Ioo a T)
    (hsState : sState ∈ Set.Ioo m T)
    (hsSource : sSource ∈ Set.Ioo m T)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hProduct : A ^ 2 ≤
      R * (E + 3 * velocityH3DissipationAt u sState) *
        (E + 3 * velocityH3DissipationAt u sSource) * B)
    (h : ℝ) (hh : 0 < h)
    (hBeyond : R * (E + 3 * h) ^ 2 * B < A ^ 2) :
    ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource h := by
  have hSpike := thirdFull_scalar_twoSliceRate_forces_actualViscousObservation244
    A B R E (velocityH3DissipationAt u sState)
      (velocityH3DissipationAt u sSource) h
    hB hR hE
    (velocityH3DissipationAt_nonneg u sState)
    (velocityH3DissipationAt_nonneg u sSource)
    hProduct hBeyond
  exact thirdFullPhysical_twoSelectedTimes_secondaryPDEClock244
    hH3 hClass hDInt m sState sSource h hm hsState hsSource hh hSpike

/-- Preserve the prescribed-gauge minimal first-crossing witnesses, adding a
secondary physical PDE clock at an actual high-dissipation source/state maximum
when the two-slice rate exceeds a chosen kinetic-only cost threshold. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_lateSecondaryPDEClock244
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
        let B := ∫ s in m..T, velocityH3DissipationAt u s ∂volume
        V < 14 * Q ^ 4 *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
        (∃ r : ℝ, r ∈ Set.Icc t m ∧
          V < 28 * Q ^ 4 *
            (‖F‖ * ((m - t) *
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
        V < 56 * Q ^ 4 * (‖F‖ * C0 * ((T - m) * E0)) ∨
        (∃ (r : ℝ) (J : ℕ) (sSource sState : ℝ),
          r ∈ Set.Ioo m T ∧ 0 < P ∧
          sSource ∈ Set.Icc r (r + (T - r) / 2) ∧
          sState ∈ Set.Icc r (r + (T - r) / 2) ∧
          ((T - r) * (V / (2 * P)) ≤ 4 * B ∨
          (V / (2 * P)) ^ 2 ≤ 4 * B ∨
          ((V / (2 * P)) ^ 2 ≤
            96 * (E0 + 3 * velocityH3DissipationAt u sState) *
              (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) *
              (((J : ℝ) + 2) ^ 5) * B ∧
            (∀ h : ℝ, 0 < h →
              96 * C0 * (((J : ℝ) + 2) ^ 5) * (E0 + 3 * h) ^ 2 * B <
                (V / (2 * P)) ^ 2 →
              ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource h))))) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_lateQuinticProductOrCompression244
      hH3 hClass b hb hNoTrace hDInt H hH
  have hAfter : ∀ᶠ k : ℕ in atTop, b < tau (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  have hNew : ∀ᶠ k : ℕ in atTop,
      let t := tau (v k)
      let m := (t + T) / 2
      let Q := (N (v k) : ℝ) + 2
      let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
      let C0 := 3 + h3AuditInitialLerayEnergyCoefficient
      let E0 := 1 + 6 * velocityH3Energy0At u b
      let P := 168 * Q ^ 4 * (‖F‖ * C0) * (T - m)
      let V := (H (v k)) ^ 4
      let B := ∫ s in m..T, velocityH3DissipationAt u s ∂volume
      V < 14 * Q ^ 4 *
        ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
      (∃ r : ℝ, r ∈ Set.Icc t m ∧
        V < 28 * Q ^ 4 *
          (‖F‖ * ((m - t) *
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
      V < 56 * Q ^ 4 * (‖F‖ * C0 * ((T - m) * E0)) ∨
      (∃ (r : ℝ) (J : ℕ) (sSource sState : ℝ),
        r ∈ Set.Ioo m T ∧ 0 < P ∧
        sSource ∈ Set.Icc r (r + (T - r) / 2) ∧
        sState ∈ Set.Icc r (r + (T - r) / 2) ∧
        ((T - r) * (V / (2 * P)) ≤ 4 * B ∨
          (V / (2 * P)) ^ 2 ≤ 4 * B ∨
          ((V / (2 * P)) ^ 2 ≤
            96 * (E0 + 3 * velocityH3DissipationAt u sState) *
              (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) *
              (((J : ℝ) + 2) ^ 5) * B ∧
            (∀ h : ℝ, 0 < h →
              96 * C0 * (((J : ℝ) + 2) ^ 5) * (E0 + 3 * h) ^ 2 * B <
                (V / (2 * P)) ^ 2 →
              ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource h)))) := by
    filter_upwards [hOld, hAfter] with k hkOld hkAfter
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
    let B : ℝ := ∫ s in m..T, velocityH3DissipationAt u s ∂volume
    rcases hkOld with hCarrier | hSource | hClock |
      ⟨r, J, sSource, sState, hr, hP, hsSource, hsState, hGate⟩
    · exact Or.inl hCarrier
    · exact Or.inr (Or.inl hSource)
    · exact Or.inr (Or.inr (Or.inl hClock))
    · right; right; right
      have hmT : m < T := lt_trans hr.1 hr.2
      have htT : t < T := by
        dsimp only [m] at hmT
        linarith only [hmT]
      have hbm : b < m := by
        dsimp only [m]
        linarith only [hkAfter, htT]
      have hHalfEnd : r + (T - r) / 2 < T := by
        linarith only [hr.2]
      have hSourceTime : sSource ∈ Set.Ioo b T :=
        ⟨lt_trans hbm (lt_of_lt_of_le hr.1 hsSource.1),
          lt_of_le_of_lt hsSource.2 hHalfEnd⟩
      have hStateTime : sState ∈ Set.Ioo b T :=
        ⟨lt_trans hbm (lt_of_lt_of_le hr.1 hsState.1),
          lt_of_le_of_lt hsState.2 hHalfEnd⟩
      have hB : 0 ≤ B := by
        dsimp only [B]
        exact intervalIntegral.integral_nonneg hmT.le
          (fun s _ => velocityH3DissipationAt_nonneg u s)
      let A : ℝ := V / (2 * P)
      let S : ℝ := (((J : ℝ) + 2) ^ 5)
      have hS : 0 ≤ S := by dsimp only [S]; positivity
      have hGateNew :
          (T - r) * A ≤ 4 * B ∨
          A ^ 2 ≤ 4 * B ∨
          A ^ 2 ≤ 96 *
            (E0 + 3 * velocityH3DissipationAt u sState) *
            (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) * S * B := by
        rcases hGate with hTime | hTail | hRate
        · exact Or.inl hTime
        · exact Or.inr (Or.inl hTail)
        · right; right
          have hPhysical :=
            thirdFullPhysical_lateQuinticProduct_twoActualViscousSlices244
              hH3 hClass b hb sSource sState A B S
              hSourceTime hStateTime hB hS
              (by simpa only [A, S] using hRate)
          simpa only [E0, C0] using hPhysical
      have hEnhanced :
          (T - r) * (V / (2 * P)) ≤ 4 * B ∨
          (V / (2 * P)) ^ 2 ≤ 4 * B ∨
          ((V / (2 * P)) ^ 2 ≤
            96 * (E0 + 3 * velocityH3DissipationAt u sState) *
              (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) * S * B ∧
            ∀ h : ℝ, 0 < h →
              96 * C0 * S * (E0 + 3 * h) ^ 2 * B < A ^ 2 →
              ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource h) := by
        rcases hGateNew with hTime | hTail | hRate
        · exact Or.inl hTime
        · exact Or.inr (Or.inl hTail)
        · right; right
          refine ⟨hRate, ?_⟩
          intro h hh hThreshold
          have hmT : m < T := lt_trans hr.1 hr.2
          have htT : t < T := by
            dsimp only [m] at hmT
            linarith only [hmT]
          have htm : t < m := by
            dsimp only [m]
            linarith only [htT]
          have hm : m ∈ Set.Ioo a T :=
            ⟨lt_trans hb.1 (lt_trans hkAfter htm), hmT⟩
          have hHalfEnd : r + (T - r) / 2 < T := by
            linarith only [hr.2]
          have hsStateTail : sState ∈ Set.Ioo m T :=
            ⟨lt_of_lt_of_le hr.1 hsState.1,
              lt_of_le_of_lt hsState.2 hHalfEnd⟩
          have hsSourceTail : sSource ∈ Set.Ioo m T :=
            ⟨lt_of_lt_of_le hr.1 hsSource.1,
              lt_of_le_of_lt hsSource.2 hHalfEnd⟩
          have hB : 0 ≤ B := by
            dsimp only [B]
            exact intervalIntegral.integral_nonneg hmT.le
              (fun s _ => velocityH3DissipationAt_nonneg u s)
          have hC0 : 0 ≤ C0 := by
            dsimp only [C0]
            have hCoeff := h3AuditInitialLerayEnergyCoefficient_nonneg
            linarith only [hCoeff]
          have hE0 : 0 ≤ E0 := by
            dsimp only [E0]
            have hEnergy := velocityH3Energy0At_nonneg u b
            linarith only [hEnergy]
          have hS : 0 ≤ S := by
            dsimp only [S]
            positivity
          let R : ℝ := 96 * C0 * S
          have hR : 0 ≤ R := by
            dsimp only [R]
            positivity
          have hProduct : A ^ 2 ≤
              R * (E0 + 3 * velocityH3DissipationAt u sState) *
                (E0 + 3 * velocityH3DissipationAt u sSource) * B := by
            calc
              A ^ 2 ≤
                  96 * (E0 + 3 * velocityH3DissipationAt u sState) *
                    (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) *
                    S * B := hRate
              _ = R * (E0 + 3 * velocityH3DissipationAt u sState) *
                    (E0 + 3 * velocityH3DissipationAt u sSource) * B := by
                      dsimp only [R]
                      ring
          have hBeyond : R * (E0 + 3 * h) ^ 2 * B < A ^ 2 := by
            simpa only [R, A] using hThreshold
          exact thirdFullPhysical_lateTwoSliceRate_forces_secondaryPDEClock244
            hH3 hClass hDInt m sState sSource A B R E0
            hm hsStateTail hsSourceTail hB hR hE0 hProduct h hh hBeyond
      refine ⟨r, J, sSource, sState, hr, hP, hsSource, hsState, ?_⟩
      simpa only [A, S] using hEnhanced
  exact ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
    hWindows, hCharges, hEscape, hNew, hViscousTail⟩

end
end PrimeTensor.FirstMonomialTriad

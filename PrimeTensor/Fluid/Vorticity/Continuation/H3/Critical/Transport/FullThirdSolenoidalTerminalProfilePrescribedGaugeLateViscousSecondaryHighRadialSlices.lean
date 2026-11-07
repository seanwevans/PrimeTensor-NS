import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousSecondaryPhysicalSlices
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralKineticAnchoredLowDissipationBudget244
import Mathlib.Tactic

/-!
# Localize the attained secondary PDE amplification to actual HIGH-frequency H³ dissipation

The previous cofinal theorem forces a large full H³ dissipation at one of the
SAME selected secondary physical state/source times if the deep-excess clock
remains wide and its squared-tail demand is too large.

On any fixed radial ball σ, the genuine kinetic anchor bounds the full-H³
LOW-radial viscous density by the time-independent quantity

    Lσ = σ² W₃(σ) E₀(b).

The exact spectral partition D = D_low,σ + D_high,σ therefore shows that a
large enough squared-tail demand forces high-radial dissipation at one of the
very same two selected observation times. The radius σ is arbitrary and is
chosen AFTER the existing secondary clock witnesses; it does not change J₂,
zSource, zState, the primary clock, or the disjoint terminal viscous charges.

This is a genuinely frequency-localized physical consequence. It does NOT
provide a positive-length persistence width for D_high or close H³ regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A spike in the true full-H³ dissipation larger than the kinetic low-band
ceiling plus M is necessarily a high-radial spike at that SAME strict time. -/
theorem thirdFullPhysical_secondaryFullSpike_to_highRadial244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (z σ M : ℝ) (hz : z ∈ Set.Ioo b T) (hσ : 0 ≤ σ)
    (hSpike : σ ^ 2 *
      (h3TerminalRadialSobolevWeightSquareCeiling σ *
        velocityH3Energy0At u b) + M < velocityH3DissipationAt u z) :
    M < h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 z) := by
  have hLow := h3Path_actualLowRadialDissipation_le_kineticAnchor244
    hH3 hClass b hb σ hσ z hz
  have hPartition := h3Path_actualRadialDissipation_partition244
    hH3 hClass z ⟨lt_trans hb.1 hz.1, hz.2⟩ σ
  linarith only [hSpike, hLow, hPartition]

/-- The physical two-slice squared-tail gate, together with the anchored
kinetic LOW-frequency bound, forces a HIGH-frequency H³ viscous spike at
one of the same two attained secondary observation times. Neither cutoff
nor observation time is reselected, and no uniform temporal D bound occurs. -/
theorem thirdFullPhysical_secondaryTwoSlice_forcesHighRadial244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (zState zSource A R B S M s σ : ℝ)
    (hzState : zState ∈ Set.Ioo b T)
    (hzSource : zSource ∈ Set.Ioo b T)
    (hR : 0 ≤ R) (hB : 0 ≤ B) (hS : 0 ≤ S) (hσ : 0 ≤ σ)
    (hWide : 192 * B * Real.sqrt (R * B) < (T - s) * A)
    (hDemand : 576 * R * B ^ 2 *
      (96 * (3 + h3AuditInitialLerayEnergyCoefficient) *
        (1 + 6 * velocityH3Energy0At u b + 3 *
          (σ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling σ *
            velocityH3Energy0At u b) + M)) ^ 2 * S + 4) < A ^ 2)
    (hGate : (T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
      A ^ 2 ≤ 576 * R * B ^ 2 *
        (96 * (1 + 6 * velocityH3Energy0At u b +
            3 * velocityH3DissipationAt u zState) *
          ((3 + h3AuditInitialLerayEnergyCoefficient) *
            (1 + 6 * velocityH3Energy0At u b +
              3 * velocityH3DissipationAt u zSource)) * S + 4)) :
    M < h3PathActualHighRadialDissipation244 σ
        (h3AuditActualSpectralVelocityTotal hH3 zState) ∨
      M < h3PathActualHighRadialDissipation244 σ
        (h3AuditActualSpectralVelocityTotal hH3 zSource) := by
  let Lσ : ℝ := σ ^ 2 *
    (h3TerminalRadialSobolevWeightSquareCeiling σ *
      velocityH3Energy0At u b)
  have hFull := thirdFullPhysical_secondaryTwoSlice_forcesDissipationSpike244
    (u := u) b zState zSource A R B S (Lσ + M) T s
    hR hB hS hWide (by simpa only [Lσ] using hDemand) hGate
  rcases hFull with hState | hSource
  · left
    exact thirdFullPhysical_secondaryFullSpike_to_highRadial244
      hH3 hClass b hb zState σ M hzState hσ
      (by simpa only [Lσ] using hState)
  · right
    exact thirdFullPhysical_secondaryFullSpike_to_highRadial244
      hH3 hClass b hb zSource σ M hzSource hσ
      (by simpa only [Lσ] using hSource)

/-- Extend the SAME cofinal residual ledger with a frequency-localized
consequence quantified over arbitrary later-selected radius σ and threshold
M. The secondary PDE clock's J₂, source/state times and overlap ledger are
retained, not reselected to accommodate σ. -/
def ThirdFullLateRetainedPrimarySecondaryHighRadialCofinalLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ)
    (sSource sState eta1 : ℝ) : Prop :=
  ThirdFullLateRetainedPrimarySecondaryTwoSlicePDECofinalLedger244
    hH3 b m r P V J sSource sState eta1 ∧
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  (A ^ 2 ≤ R *
      (E0 + 3 * velocityH3DissipationAt u sState) *
      (E0 + 3 * velocityH3DissipationAt u sSource) * B →
    4 * R * B * E0 ^ 2 < A ^ 2 →
    48 * Real.sqrt (R * B) ≤ 1 →
    ∃ (s eta2 : ℝ) (J2 : ℕ) (zSource zState : ℝ),
      (s = sState ∨ s = sSource) ∧ r ≤ s ∧
      0 < eta2 ∧ s + eta2 < T ∧
      zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
      zState ∈ Set.Icc s (s + (T - s) / 2) ∧
      (∀ (σ M : ℝ), 0 ≤ σ →
        192 * B * Real.sqrt (R * B) < (T - s) * A →
        576 * R * B ^ 2 *
          (96 * C0 *
            (E0 + 3 * (σ ^ 2 *
              (h3TerminalRadialSobolevWeightSquareCeiling σ *
                velocityH3Energy0At u b) + M)) ^ 2 *
              (((J2 : ℝ) + 2) ^ 5) + 4) < A ^ 2 →
        M < h3PathActualHighRadialDissipation244 σ
            (h3AuditActualSpectralVelocityTotal hH3 zState) ∨
        M < h3PathActualHighRadialDissipation244 σ
            (h3AuditActualSpectralVelocityTotal hH3 zSource)))

/-- Upgrade the actually retained secondary physical-two-slice ledger:
frequency localization follows from the exact viscous spectral partition
and its anchored kinetic low-ball estimate, with no additional PDE axiom. -/
theorem thirdFullPhysical_secondaryTwoSliceLedger_to_highRadial244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (m r P V : ℝ) (J : ℕ) (sSource sState eta1 : ℝ)
    (hm : m ∈ Set.Ioo b T) (hr : r ∈ Set.Ioo m T)
    (hOld : ThirdFullLateRetainedPrimarySecondaryTwoSlicePDECofinalLedger244
      hH3 b m r P V J sSource sState eta1) :
    ThirdFullLateRetainedPrimarySecondaryHighRadialCofinalLedger244
      hH3 b m r P V J sSource sState eta1 := by
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  change ThirdFullLateRetainedPrimarySecondaryTwoSlicePDECofinalLedger244
      hH3 b m r P V J sSource sState eta1 ∧
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B →
      4 * R * B * E0 ^ 2 < A ^ 2 →
      48 * Real.sqrt (R * B) ≤ 1 →
      ∃ (s eta2 : ℝ) (J2 : ℕ) (zSource zState : ℝ),
        (s = sState ∨ s = sSource) ∧ r ≤ s ∧
        0 < eta2 ∧ s + eta2 < T ∧
        zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
        zState ∈ Set.Icc s (s + (T - s) / 2) ∧
        (∀ (σ M : ℝ), 0 ≤ σ →
          192 * B * Real.sqrt (R * B) < (T - s) * A →
          576 * R * B ^ 2 *
            (96 * C0 *
              (E0 + 3 * (σ ^ 2 *
                (h3TerminalRadialSobolevWeightSquareCeiling σ *
                  velocityH3Energy0At u b) + M)) ^ 2 *
                (((J2 : ℝ) + 2) ^ 5) + 4) < A ^ 2 →
          M < h3PathActualHighRadialDissipation244 σ
              (h3AuditActualSpectralVelocityTotal hH3 zState) ∨
          M < h3PathActualHighRadialDissipation244 σ
              (h3AuditActualSpectralVelocityTotal hH3 zSource)))
  refine ⟨hOld, ?_⟩
  intro hRate hGap hStrong
  obtain ⟨s, eta2, J2, zSource, zState,
      hChoice, hrs, heta2, hend2, hzSource, hzState, hGate⟩ :=
    hOld.2 hRate hGap hStrong
  have hsT : s < T := by linarith only [heta2, hend2]
  have hHalfEnd : s + (T - s) / 2 < T := by
    linarith only [hsT]
  have hbS : b < s :=
    lt_of_lt_of_le (lt_trans hm.1 hr.1) hrs
  have hzSourceTime : zSource ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le hbS hzSource.1,
      lt_of_le_of_lt hzSource.2 hHalfEnd⟩
  have hzStateTime : zState ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le hbS hzState.1,
      lt_of_le_of_lt hzState.2 hHalfEnd⟩
  have hR : 0 ≤ R := by
    dsimp only [R, C0]
    have hCoeff := h3AuditInitialLerayEnergyCoefficient_nonneg
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact intervalIntegral.integral_nonneg hm.2.le
      (fun x _ => velocityH3DissipationAt_nonneg u x)
  have hS : 0 ≤ (((J2 : ℝ) + 2) ^ 5) := by positivity
  have hGate' :
      (T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
      A ^ 2 ≤ 576 * R * B ^ 2 *
        (96 * (E0 + 3 * velocityH3DissipationAt u zState) *
          (C0 * (E0 + 3 * velocityH3DissipationAt u zSource)) *
          (((J2 : ℝ) + 2) ^ 5) + 4) := by
    simpa only [A, R, B, C0, E0, mul_assoc] using hGate
  refine ⟨s, eta2, J2, zSource, zState,
    hChoice, hrs, heta2, hend2, hzSource, hzState, ?_⟩
  intro σ M hσ hWide hDemand
  exact thirdFullPhysical_secondaryTwoSlice_forcesHighRadial244
    hH3 hClass b hb zState zSource A R B
    (((J2 : ℝ) + 2) ^ 5) M s σ
    hzStateTime hzSourceTime hR hB hS hσ hWide
    (by simpa only [E0, C0] using hDemand) hGate'

/-- The original no-terminal-H³-trace cofinal minimal crossing sequence,
frequency escape and disjoint physical viscous budgets now retain the fixed-
radius HIGH-frequency secondary dissipation obstruction, with no new time
selection and no summability claim for the pointwise secondary spikes. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_secondaryHighRadial244
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
          ThirdFullLateRetainedPrimarySecondaryHighRadialCofinalLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_secondaryTwoSlicePDE244
      hH3 hClass b hb hNoTrace hDInt H hH
  have hAfter : ∀ᶠ k : ℕ in atTop, b < tau (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  refine ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
    hWindows, hCharges, hEscape, ?_, hViscousTail⟩
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
  rcases hkOld with hCarrier | hSource | hClock |
      ⟨r, J, sSource, sState, eta1, hr, hP,
        hsSource, hsState, hEtaEq, heta1, hend1, hFloor, hCharge, hLedger⟩
  · exact Or.inl hCarrier
  · exact Or.inr (Or.inl hSource)
  · exact Or.inr (Or.inr (Or.inl hClock))
  · right; right; right
    have hmT : m < T := lt_trans hr.1 hr.2
    have htT : t < T := by
      dsimp only [m] at hmT
      linarith only [hmT]
    have htm : t < m := by
      dsimp only [m]
      linarith only [htT]
    have hmB : m ∈ Set.Ioo b T :=
      ⟨lt_trans hkAfter htm, hmT⟩
    have hPhysical :=
      thirdFullPhysical_secondaryTwoSliceLedger_to_highRadial244
        hH3 hClass b hb m r P V J sSource sState eta1
        hmB hr hLedger
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hPhysical⟩

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousNormalizedPrimaryPDEGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousKineticTwoSliceGate
import Mathlib.Tactic

/-!
# Actual secondary H³ dissipation observations behind the residual PDE obstruction

The normalized residual clock demands either
    (T-s) A <= 192 B sqrt(R B), or
    A² <= 576 R B² (96 K₂ C₂ (J₂+2)^5 + 4).

The *attained secondary* source and state factors are not independent. The
verified physical Navier--Stokes source bound, the spectral energy comparison,
and the kinetic anchor give, at the SAME secondary observation times,
    K₂ <= E_b + 3 D(zState),
    C₂ <= C_L (E_b + 3 D(zSource)).

This transports squared-tail amplification to two actual pointwise H³
viscous observations. On a noncompressed clock and above a stated finite
cutoff-dependent threshold, one of these two observations must be large.
No uniform cutoff, pointwise dissipation ceiling, or positive-length
persistence interval is inferred from finite integral dissipation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Monotonicity of the *squared-tail* primary barrier; the baseline +4
term is kept, not silently discarded. -/
theorem thirdFull_scalar_secondaryPDEProduct_monotone244
    (A R B P Q : ℝ)
    (hR : 0 ≤ R) (_hB : 0 ≤ B)
    (hPQ : 96 * P ≤ 96 * Q)
    (hRate : A ^ 2 ≤ 576 * R * B ^ 2 * (96 * P + 4)) :
    A ^ 2 ≤ 576 * R * B ^ 2 * (96 * Q + 4) := by
  have hCoeff : 0 ≤ 576 * R * B ^ 2 := by positivity
  have hSum : 96 * P + 4 ≤ 96 * Q + 4 := by
    linarith only [hPQ]
  exact hRate.trans (mul_le_mul_of_nonneg_left hSum hCoeff)

/-- The previously verified *genuine physical two-slice* estimate supplies
an upper bound on the same attained product. The auxiliary square root is
only a way to reuse the existing physical theorem, not a new PDE premise. -/
theorem thirdFullPhysical_secondaryPDEProduct_twoActualSlices244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (zSource zState S : ℝ)
    (hzSource : zSource ∈ Set.Ioo b T)
    (hzState : zState ∈ Set.Ioo b T)
    (hS : 0 ≤ S) :
    96 * ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
        ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ * S ≤
      96 * (1 + 6 * velocityH3Energy0At u b +
          3 * velocityH3DissipationAt u zState) *
        ((3 + h3AuditInitialLerayEnergyCoefficient) *
          (1 + 6 * velocityH3Energy0At u b +
            3 * velocityH3DissipationAt u zSource)) * S := by
  let K : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 zState‖
  let C : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖
  have hSquareNonneg : 0 ≤ 96 * K * C * S := by
    dsimp only [K, C]
    positivity
  have hSquare : (Real.sqrt (96 * K * C * S)) ^ 2 =
      96 * K * C * S := Real.sq_sqrt hSquareNonneg
  have hInput : (Real.sqrt (96 * K * C * S)) ^ 2 ≤
      96 * K * C * S * (1 : ℝ) := by
    rw [hSquare]
    simp
  have hPhysical :=
    thirdFullPhysical_lateQuinticProduct_twoActualViscousSlices244
      hH3 hClass b hb zSource zState
      (Real.sqrt (96 * K * C * S)) 1 S
      hzSource hzState (by norm_num) hS hInput
  simpa only [hSquare, mul_one, K, C] using hPhysical

/-- Replace the secondary finite-frequency rate product by two *actual*
physical H³ dissipations at the witness state/source observation times. -/
theorem thirdFullPhysical_normalizedSecondaryRate_twoActualViscousSlices244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (zSource zState A R B S : ℝ)
    (hzSource : zSource ∈ Set.Ioo b T)
    (hzState : zState ∈ Set.Ioo b T)
    (hR : 0 ≤ R) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hRate : A ^ 2 ≤ 576 * R * B ^ 2 *
      (96 * ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
        ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ * S + 4)) :
    A ^ 2 ≤ 576 * R * B ^ 2 *
      (96 * (1 + 6 * velocityH3Energy0At u b +
          3 * velocityH3DissipationAt u zState) *
        ((3 + h3AuditInitialLerayEnergyCoefficient) *
          (1 + 6 * velocityH3Energy0At u b +
            3 * velocityH3DissipationAt u zSource)) * S + 4) := by
  have hTwo := thirdFullPhysical_secondaryPDEProduct_twoActualSlices244
    hH3 hClass b hb zSource zState S hzSource hzState hS
  have hBound := thirdFull_scalar_secondaryPDEProduct_monotone244
    A R B
    (‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
      ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ * S)
    ((1 + 6 * velocityH3Energy0At u b +
      3 * velocityH3DissipationAt u zState) *
      ((3 + h3AuditInitialLerayEnergyCoefficient) *
        (1 + 6 * velocityH3Energy0At u b +
          3 * velocityH3DissipationAt u zSource)) * S)
    hR hB (by simpa only [mul_assoc] using hTwo)
    (by simpa only [mul_assoc] using hRate)
  simpa only [mul_assoc] using hBound

/-- With a finite cutoff and a fixed dissipation cap, the normalized
squared-tail branch cannot pay a height exceeding the explicit physical
threshold. Therefore a noncompressed clock forces a real secondary
H³ dissipation spike at one of the TWO predetermined observation times. -/
theorem thirdFull_scalar_secondaryTwoSlice_forcesDissipationSpike244
    (A R B E0 C0 S DState DSource M d : ℝ)
    (hR : 0 ≤ R) (_hB : 0 ≤ B)
    (hE0 : 0 ≤ E0) (hC0 : 0 ≤ C0) (hS : 0 ≤ S)
    (hDState : 0 ≤ DState) (hDSource : 0 ≤ DSource)
    (hWide : 192 * B * Real.sqrt (R * B) < d * A)
    (hDemand : 576 * R * B ^ 2 *
      (96 * C0 * (E0 + 3 * M) ^ 2 * S + 4) < A ^ 2)
    (hGate : d * A ≤ 192 * B * Real.sqrt (R * B) ∨
      A ^ 2 ≤ 576 * R * B ^ 2 *
        (96 * (E0 + 3 * DState) * (C0 * (E0 + 3 * DSource)) * S + 4)) :
    M < DState ∨ M < DSource := by
  have hRate : A ^ 2 ≤ 576 * R * B ^ 2 *
      (96 * (E0 + 3 * DState) * (C0 * (E0 + 3 * DSource)) * S + 4) := by
    rcases hGate with hShort | hRate
    · exact False.elim ((not_le_of_gt hWide) hShort)
    · exact hRate
  by_contra hNeither
  have hDs : DState ≤ M := le_of_not_gt (by
    intro hBig
    exact hNeither (Or.inl hBig))
  have hDc : DSource ≤ M := le_of_not_gt (by
    intro hBig
    exact hNeither (Or.inr hBig))
  have hM : 0 ≤ M := le_trans hDState hDs
  have hEM : 0 ≤ E0 + 3 * M := by positivity
  have hESource : 0 ≤ E0 + 3 * DSource := by positivity
  have hDsLe : E0 + 3 * DState ≤ E0 + 3 * M := by
    linarith only [hDs]
  have hDcLe : E0 + 3 * DSource ≤ E0 + 3 * M := by
    linarith only [hDc]
  have hProduct :
      (E0 + 3 * DState) * (E0 + 3 * DSource) ≤
        (E0 + 3 * M) ^ 2 := by
    calc
      (E0 + 3 * DState) * (E0 + 3 * DSource) ≤
          (E0 + 3 * M) * (E0 + 3 * DSource) :=
        mul_le_mul_of_nonneg_right hDsLe hESource
      _ ≤ (E0 + 3 * M) * (E0 + 3 * M) :=
        mul_le_mul_of_nonneg_left hDcLe hEM
      _ = (E0 + 3 * M) ^ 2 := by ring
  have hAmp :
      96 * (E0 + 3 * DState) * (C0 * (E0 + 3 * DSource)) * S ≤
        96 * C0 * (E0 + 3 * M) ^ 2 * S := by
    calc
      _ = (96 * C0 * S) *
          ((E0 + 3 * DState) * (E0 + 3 * DSource)) := by ring
      _ ≤ (96 * C0 * S) * (E0 + 3 * M) ^ 2 :=
        mul_le_mul_of_nonneg_left hProduct (by positivity)
      _ = 96 * C0 * (E0 + 3 * M) ^ 2 * S := by ring
  have hScale : 0 ≤ 576 * R * B ^ 2 := by positivity
  have hSum :
      96 * (E0 + 3 * DState) * (C0 * (E0 + 3 * DSource)) * S + 4 ≤
        96 * C0 * (E0 + 3 * M) ^ 2 * S + 4 := by
    linarith only [hAmp]
  have hUpper : A ^ 2 ≤ 576 * R * B ^ 2 *
      (96 * C0 * (E0 + 3 * M) ^ 2 * S + 4) :=
    hRate.trans (mul_le_mul_of_nonneg_left hSum hScale)
  exact (not_le_of_gt hDemand) hUpper

/-- The threshold-spike fork now uses the exact physical full-H³
dissipation and anchored kinetic energy, rather than abstract scalar
quantities. The cutoff S is still the moving, actually selected S₂. -/
theorem thirdFullPhysical_secondaryTwoSlice_forcesDissipationSpike244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    (b zState zSource A R B S M T s : ℝ)
    (hR : 0 ≤ R) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hWide : 192 * B * Real.sqrt (R * B) < (T - s) * A)
    (hDemand : 576 * R * B ^ 2 *
      (96 * (3 + h3AuditInitialLerayEnergyCoefficient) *
        (1 + 6 * velocityH3Energy0At u b + 3 * M) ^ 2 * S + 4) < A ^ 2)
    (hGate : (T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
      A ^ 2 ≤ 576 * R * B ^ 2 *
        (96 * (1 + 6 * velocityH3Energy0At u b +
            3 * velocityH3DissipationAt u zState) *
          ((3 + h3AuditInitialLerayEnergyCoefficient) *
            (1 + 6 * velocityH3Energy0At u b +
              3 * velocityH3DissipationAt u zSource)) * S + 4)) :
    M < velocityH3DissipationAt u zState ∨
      M < velocityH3DissipationAt u zSource := by
  have hE0 : 0 ≤ 1 + 6 * velocityH3Energy0At u b := by
    have hK := velocityH3Energy0At_nonneg u b
    positivity
  have hC0 : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
    have hCoeff := h3AuditInitialLerayEnergyCoefficient_nonneg
    positivity
  exact thirdFull_scalar_secondaryTwoSlice_forcesDissipationSpike244
    A R B (1 + 6 * velocityH3Energy0At u b)
    (3 + h3AuditInitialLerayEnergyCoefficient) S
    (velocityH3DissipationAt u zState)
    (velocityH3DissipationAt u zSource) M (T - s)
    hR hB hE0 hC0 hS
    (velocityH3DissipationAt_nonneg u zState)
    (velocityH3DissipationAt_nonneg u zSource)
    hWide hDemand hGate

/-- Keep the actual normalized cofinal certificate and attach its physical
two-slice obstruction using EXACTLY the previously selected J₂, zSource,
zState and terminal B. -/
def ThirdFullLateRetainedPrimarySecondaryTwoSlicePDECofinalLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ)
    (sSource sState eta1 : ℝ) : Prop :=
  ThirdFullLateRetainedPrimaryNormalizedPDECofinalLedger244
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
      ((T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
        A ^ 2 ≤ 576 * R * B ^ 2 *
          (96 * (E0 + 3 * velocityH3DissipationAt u zState) *
            (C0 * (E0 + 3 * velocityH3DissipationAt u zSource)) *
            (((J2 : ℝ) + 2) ^ 5) + 4)))

/-- Actual Navier--Stokes two-slice replacement of the normalized
squared-height PDE product, not a postulated uniform rate ceiling. -/
theorem thirdFullPhysical_normalizedLedger_to_secondaryTwoSlicePDE244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (m r P V : ℝ) (J : ℕ) (sSource sState eta1 : ℝ)
    (hm : m ∈ Set.Ioo b T) (hr : r ∈ Set.Ioo m T)
    (hOld : ThirdFullLateRetainedPrimaryNormalizedPDECofinalLedger244
      hH3 b m r P V J sSource sState eta1) :
    ThirdFullLateRetainedPrimarySecondaryTwoSlicePDECofinalLedger244
      hH3 b m r P V J sSource sState eta1 := by
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  change ThirdFullLateRetainedPrimaryNormalizedPDECofinalLedger244
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
        ((T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
          A ^ 2 ≤ 576 * R * B ^ 2 *
            (96 * (E0 + 3 * velocityH3DissipationAt u zState) *
              (C0 * (E0 + 3 * velocityH3DissipationAt u zSource)) *
              (((J2 : ℝ) + 2) ^ 5) + 4)))
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
  have hConverted :
      (T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
      A ^ 2 ≤ 576 * R * B ^ 2 *
        (96 * (E0 + 3 * velocityH3DissipationAt u zState) *
          (C0 * (E0 + 3 * velocityH3DissipationAt u zSource)) *
          (((J2 : ℝ) + 2) ^ 5) + 4) := by
    have hGate' :
        (T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
        A ^ 2 ≤ 576 * R * B ^ 2 *
          (96 * ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
            ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
            (((J2 : ℝ) + 2) ^ 5) + 4) := by
      simpa only [A, R, B, C0, mul_assoc] using hGate
    rcases hGate' with hShort | hPhysicalRate
    · exact Or.inl hShort
    · right
      have hResolved :=
        thirdFullPhysical_normalizedSecondaryRate_twoActualViscousSlices244
          hH3 hClass b hb zSource zState A R B
          (((J2 : ℝ) + 2) ^ 5)
          hzSourceTime hzStateTime hR hB hS hPhysicalRate
      simpa only [E0, C0] using hResolved
  refine ⟨s, eta2, J2, zSource, zState,
    hChoice, hrs, heta2, hend2, hzSource, hzState, ?_⟩
  simpa only [A, R, B, E0, C0, mul_assoc] using hConverted


/-- Cofinal no-terminal-H³-trace witnesses keep their original disjoint
viscous charges, frequency escape and first physical clock. The activated
secondary rate branch is now paid by D_H3 at the two *actual attained*
secondary PDE observation times; these times are not replaced. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_secondaryTwoSlicePDE244
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
          ThirdFullLateRetainedPrimarySecondaryTwoSlicePDECofinalLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_normalizedPrimaryPDE244
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
      thirdFullPhysical_normalizedLedger_to_secondaryTwoSlicePDE244
        hH3 hClass b hb m r P V J sSource sState eta1
        hmB hr hLedger
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hPhysical⟩

end
end PrimeTensor.FirstMonomialTriad

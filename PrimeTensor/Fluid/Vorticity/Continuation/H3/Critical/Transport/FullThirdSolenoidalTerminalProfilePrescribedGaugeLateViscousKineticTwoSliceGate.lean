import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousQuinticPhysicalBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationPointwise
import Mathlib.Tactic

/-!
# Resolve late prescribed-gauge quintic source-state amplification into physical H³ dissipation

The existing strict-time kinetic anchor bounds the *actual* H³ spectral-state
norm via its physical energy, and also bounds the projected momentum source.
Thus the quintic rate product K*C on the same late half-terminal interval is
paid by two physical viscous observations:

  K <= E_b + 3 D_H3(sState),
  C <= (3 + C_L) * (E_b + 3 D_H3(sSource)),
  E_b = 1 + 6 E_0(b).

Consequently the previously unresolved late rate branch becomes

  A^2 <= 96 (3+C_L) (E_b+3D(sState)) (E_b+3D(sSource))
          (J+2)^5 B,

where A=H(vk)^4/(2P), B=integral_(mk)^T D_H3 and J is the actual captured
finite Fourier cutoff. These are true Navier--Stokes times, not postulated
suprema. The old time-compression and pure-tail alternatives, the minimal
prescribed-gauge first-crossing witnesses and their disjoint viscous charges,
remain unchanged. Finite integrability by itself does not bound D at these
two selected times; this is a two-slice physical obstruction, not regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The quintic PDE-rate factor is monotone in each nonnegative observed
physical factor, even when the remaining viscous tail is very small. -/
theorem thirdFull_scalar_quinticProduct_twoSliceMonotonicity244
    (A B S K C EK EC : ℝ)
    (hB : 0 ≤ B) (hS : 0 ≤ S) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hEK : K ≤ EK) (hEC : C ≤ EC)
    (hRate : A ^ 2 ≤ 96 * K * C * S * B) :
    A ^ 2 ≤ 96 * EK * EC * S * B := by
  have hEKNonneg : 0 ≤ EK := le_trans hK hEK
  have hProduct : K * C ≤ EK * EC := by
    calc
      K * C ≤ EK * C := mul_le_mul_of_nonneg_right hEK hC
      _ ≤ EK * EC := mul_le_mul_of_nonneg_left hEC hEKNonneg
  have hFactor : 0 ≤ 96 * S * B := by positivity
  calc
    A ^ 2 ≤ 96 * K * C * S * B := hRate
    _ = (96 * S * B) * (K * C) := by ring
    _ ≤ (96 * S * B) * (EK * EC) :=
      mul_le_mul_of_nonneg_left hProduct hFactor
    _ = 96 * EK * EC * S * B := by ring

/-- Both *attained* late-time maxima are charged to the same physical
kinetic anchor and to actual full H³ dissipation at their respective times.
The spectral-state estimate uses the normalized H³ energy's unit floor,
not a terminal-uniform H³ bound or an independent Sobolev assumption. -/
theorem thirdFullPhysical_lateQuinticProduct_twoActualViscousSlices244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (sSource sState A B S : ℝ)
    (hsSource : sSource ∈ Set.Ioo b T)
    (hsState : sState ∈ Set.Ioo b T)
    (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hProduct : A ^ 2 ≤
      96 * ‖h3AuditActualSpectralVelocityTotal hH3 sState‖ *
        ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ * S * B) :
    A ^ 2 ≤ 96 *
      (1 + 6 * velocityH3Energy0At u b +
        3 * velocityH3DissipationAt u sState) *
      ((3 + h3AuditInitialLerayEnergyCoefficient) *
        (1 + 6 * velocityH3Energy0At u b +
          3 * velocityH3DissipationAt u sSource)) * S * B := by
  let K : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
  let C : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖
  let EK : ℝ := 1 + 6 * velocityH3Energy0At u b +
    3 * velocityH3DissipationAt u sState
  let EC : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient) *
    (1 + 6 * velocityH3Energy0At u b +
      3 * velocityH3DissipationAt u sSource)
  have hsStateAbs : sState ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hsState.1),
      hsState.2⟩
  have hSpectralEnergy : K ^ 2 ≤ velocityH3EnergyAt u sState := by
    simpa only [K] using
      (h3Audit_initialActualSpectralState_norm_sq_le_energy
        hH3 sState hsStateAbs)
  have hEnergyOne : 1 ≤ velocityH3EnergyAt u sState :=
    one_le_velocityH3EnergyAt u sState
  have hSpectralLinear : K ≤ velocityH3EnergyAt u sState := by
    nlinarith only [hSpectralEnergy, hEnergyOne, sq_nonneg (K - 1)]
  have hEnergyAnchor : velocityH3EnergyAt u sState ≤ EK := by
    simpa only [EK] using
      (h3Critical_energy_le_kinetic_anchor_add_dissipation
        hH3 hClass hb hsState)
  have hKBound : K ≤ EK := hSpectralLinear.trans hEnergyAnchor
  have hCBound : C ≤ EC := by
    simpa only [C, EC] using
      (h3Critical_projected_source_le_kinetic_anchor_add_dissipation
        hH3 hClass hb hsSource)
  have hResolved :=
    thirdFull_scalar_quinticProduct_twoSliceMonotonicity244
      A B S K C EK EC hB hS (norm_nonneg _) (norm_nonneg _)
      hKBound hCBound (by simpa only [K, C] using hProduct)
  simpa only [EK, EC] using hResolved

/-- Same prescribed-gauge minimal annulus witnesses, now with the actual
late *physical* H³ dissipation at both state-maximizing and source-maximizing
times replacing the unresolved product of the attained state/source norms.
No pointwise ceiling on full H³ dissipation is assumed. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_lateTwoViscousSlices244
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
          (V / (2 * P)) ^ 2 ≤
            96 * (E0 + 3 * velocityH3DissipationAt u sState) *
              (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) *
              (((J : ℝ) + 2) ^ 5) * B))) ∧
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
          (V / (2 * P)) ^ 2 ≤
            96 * (E0 + 3 * velocityH3DissipationAt u sState) *
              (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) *
              (((J : ℝ) + 2) ^ 5) * B)) := by
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
      refine ⟨r, J, sSource, sState, hr, hP, hsSource, hsState, ?_⟩
      simpa only [A, S] using hGateNew
  exact ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
    hWindows, hCharges, hEscape, hNew, hViscousTail⟩

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousRateBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousAnnularQuinticRate
import Mathlib.Tactic

/-!
# Physical source-state fifth-power barrier on prescribed-gauge late viscosity

The previously verified actual PDE-clock dichotomy leaves a low-radial
variation coefficient Lambda. The physical Fourier gradient polynomial
bound gives

  Lambda(J,K,C) <= 24 K C (J+2)^5,

where K and C are attained physical spectral-state and projected-source
norm maxima on the same late compact physical interval. If A is the
normalized prescribed-gauge fourth-power spike and B is the actual
remaining full H3 dissipation integral, then the fast-rate arm

  A^2 <= 2 (Lambda+1) B

is sharpened to the necessary alternative

  A^2 <= 4 B OR A^2 <= 96 K C (J+2)^5 B.

Combined with the preexisting terminal time-compression arm, this leaves
three genuinely physical mechanisms on the late branch. No upper bound
on the moving capture cutoff J, K, or C is asserted. The original
minimal crossing witnesses and finite disjoint viscous charges are
unchanged; this is not a Navier--Stokes continuation proof.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The actual low-radial projected-PDE dissipation variation coefficient
is no worse than a fifth power of the selected finite Fourier radius,
times the attained physical state and source maxima. -/
theorem thirdFull_lateLowRadialPDERate_le_quinticPhysicalProduct244
    (J : ℕ) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    thirdFullLateViscousLowRadialPDERate244 J K C ≤
      24 * K * C * (((J : ℝ) + 2) ^ 5) := by
  have hJ : (1 : ℝ) ≤ (J : ℝ) + 1 := by
    have hj : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
    linarith only [hj]
  have hRoot := h3Critical_annularPDE_sqrtWeight_le_cubicCutoff
    ((J : ℝ) + 1) hJ
  have hFactor : 0 ≤ 6 * (((J : ℝ) + 2) ^ 2) * K * C := by
    positivity
  calc
    thirdFullLateViscousLowRadialPDERate244 J K C =
        (6 * (((J : ℝ) + 2) ^ 2) * K * C) *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling
            ((J : ℝ) + 1)) := by
              dsimp only [thirdFullLateViscousLowRadialPDERate244]
              ring
    _ ≤ (6 * (((J : ℝ) + 2) ^ 2) * K * C) *
          (4 * (((J : ℝ) + 1) + 1) ^ 3) :=
            mul_le_mul_of_nonneg_left hRoot hFactor
    _ = 24 * K * C * (((J : ℝ) + 2) ^ 5) := by ring

/-- Split the physical PDE-rate cost into a vanishing pure-tail arm or a
nonzero actual source-state-frequency payment. No sign is required for the
spike height or rate, apart from nonnegativity of the terminal cost B. -/
theorem thirdFull_scalar_lateRate_quinticProductOrTail244
    (A B Lambda K C S : ℝ) (hB : 0 ≤ B)
    (hRate : A ^ 2 ≤ 2 * (Lambda + 1) * B)
    (hBound : Lambda ≤ 24 * K * C * S) :
    A ^ 2 ≤ 4 * B ∨ A ^ 2 ≤ 96 * K * C * S * B := by
  have hRateBound :
      2 * (Lambda + 1) * B ≤
        2 * (24 * K * C * S + 1) * B := by
    apply mul_le_mul_of_nonneg_right _ hB
    linarith only [hBound]
  have hUpper : A ^ 2 ≤ 48 * K * C * S * B + 2 * B := by
    calc
      A ^ 2 ≤ 2 * (Lambda + 1) * B := hRate
      _ ≤ 2 * (24 * K * C * S + 1) * B := hRateBound
      _ = 48 * K * C * S * B + 2 * B := by ring
  by_cases hSmall : A ^ 2 ≤ 4 * B
  · exact Or.inl hSmall
  · right
    have hLarge : 4 * B < A ^ 2 := lt_of_not_ge hSmall
    nlinarith only [hUpper, hLarge]

/-- The prescribed-gauge first-crossing witnesses now carry a FOUR-way
physical rate gate. On the late-viscous branch the exact clock eta has been
eliminated: the actual remaining time times the normalized fourth-power
amplitude must be small, OR the square of that amplitude is paid by the
actual finite-band PDE variation coefficient times terminal H^3 dissipation.
Neither rate nor state/source maxima are substituted by an artificial bound. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_lateQuinticProductOrCompression244
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
            96 * ‖h3AuditActualSpectralVelocityTotal hH3 sState‖ *
              ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ *
                (((J : ℝ) + 2) ^ 5) * B))) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_lateRateOrCompression244
      hH3 hClass b hb hNoTrace hDInt H hH
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
            96 * ‖h3AuditActualSpectralVelocityTotal hH3 sState‖ *
              ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ *
                (((J : ℝ) + 2) ^ 5) * B)) := by
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
    let B : ℝ := ∫ s in m..T, velocityH3DissipationAt u s ∂volume
    rcases hkOld with hCarrier | hSource | hClock |
      ⟨r, J, sSource, sState, hr, hP, hsSource, hsState, hGate⟩
    · exact Or.inl hCarrier
    · exact Or.inr (Or.inl hSource)
    · exact Or.inr (Or.inr (Or.inl hClock))
    · right; right; right
      have hB : 0 ≤ B := by
        dsimp only [B]
        exact intervalIntegral.integral_nonneg
          (lt_trans hr.1 hr.2).le
          (fun s _ => velocityH3DissipationAt_nonneg u s)
      let KP : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
      let CP : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖
      let Lambda : ℝ := thirdFullLateViscousLowRadialPDERate244 J KP CP
      let S : ℝ := (((J : ℝ) + 2) ^ 5)
      have hPoly : Lambda ≤ 24 * KP * CP * S := by
        dsimp only [Lambda, KP, CP, S]
        exact thirdFull_lateLowRadialPDERate_le_quinticPhysicalProduct244
          J _ _ (norm_nonneg _) (norm_nonneg _)
      have hPhys :
          (T - r) * (V / (2 * P)) ≤ 4 * B ∨
          (V / (2 * P)) ^ 2 ≤ 4 * B ∨
          (V / (2 * P)) ^ 2 ≤ 96 * KP * CP * S * B := by
        rcases hGate with hShort | hFast
        · exact Or.inl hShort
        · right
          exact thirdFull_scalar_lateRate_quinticProductOrTail244
            (V / (2 * P)) B Lambda KP CP S hB hFast hPoly
      refine ⟨r, J, sSource, sState, hr, hP, hsSource, hsState, ?_⟩
      simpa only [KP, CP, S] using hPhys
  exact ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
    hWindows, hCharges, hEscape, hNew, hViscousTail⟩

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeHalfTailLocalization
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationTerminalTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Physical dissipation controls the delayed source action on selected H³ windows

The previously established three-channel obstruction retained an absolute
projected-source tail on the delayed half of each terminal interval.  That
tail is not an independent unknown: the genuine projected Navier--Stokes
momentum source satisfies the proved pointwise kinetic-plus-H³-dissipation
majorant. Integrating on the delayed half makes the physical payments explicit:

  source_tail(m,T) <= (3 + C_L) *
    ((1 + 6 E₀(b)) * (T-m) + 3 * integral_m^T D_H³).

Consequently the selected prescribed-gauge first-crossing windows carry one
of FOUR quartic charges: fixed terminal Fourier carrier, attained source
maximum on the early half, kinetic-clock length, or actual terminal viscous
charge. The terminal viscous integral tends to zero, since the assumed full
H³ dissipation is integrable. Its product with the escaping outer-frequency
fourth power is *not* shown to vanish; no false continuation is inferred.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A delayed quartic source payment splits into a kinetic-time cost or a
true viscous-action cost. The factor 56 is twice the existing 28. -/
theorem thirdFull_quartic_delayedSource_kineticOrViscous244
    (R Q S E D : ℝ) (hQ : 0 ≤ Q)
    (hSource : R < 28 * Q ^ 4 * S)
    (hBound : S ≤ E + D) :
    R < 56 * Q ^ 4 * E ∨ R < 56 * Q ^ 4 * D := by
  have hCoef : 0 ≤ 28 * Q ^ 4 := by positivity
  have hUpper : R < 28 * Q ^ 4 * (E + D) :=
    hSource.trans_le (mul_le_mul_of_nonneg_left hBound hCoef)
  have hAdd : R < 28 * Q ^ 4 * E + 28 * Q ^ 4 * D := by
    convert hUpper using 1 <;> ring
  by_cases hEarly : R < 56 * Q ^ 4 * E
  · exact Or.inl hEarly
  · right
    have hEarlyLe : 56 * Q ^ 4 * E ≤ R := le_of_not_gt hEarly
    nlinarith only [hAdd, hEarlyLe]

/-- The actual projected physical momentum-source L¹ action on the delayed
terminal interval is charged to the fixed kinetic anchor and the actual
full H³ viscous dissipation. The terminal endpoint is treated by the
interval integral comparison on Ioo, with no assertion about G(T). -/
theorem thirdFullPhysical_delayedSource_le_kineticClock_add_viscosity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hG : IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
      volume b T)
    (m : ℝ) (hm : m ∈ Set.Ioo b T) :
    (∫ r in m..T, ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) ≤
      (3 + h3AuditInitialLerayEnergyCoefficient) *
        ((1 + 6 * velocityH3Energy0At u b) * (T - m) +
          3 * (∫ r in m..T, velocityH3DissipationAt u r ∂volume)) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let D : ℝ → ℝ := velocityH3DissipationAt u
  let C : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let K : ℝ := 1 + 6 * velocityH3Energy0At u b
  have hDtail : IntervalIntegrable D volume m T := by
    apply hDInt.mono_set
    intro r hr
    have hr' : r ∈ Set.Icc m T := by
      simpa only [Set.uIcc_of_le hm.2.le] using hr
    have hr'' : r ∈ Set.Icc a T :=
      ⟨le_trans hb.1.le (le_trans hm.1.le hr'.1), hr'.2⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hr''
  have hGtail : IntervalIntegrable G volume m T := by
    apply hG.mono_set
    intro r hr
    have hr' : r ∈ Set.Icc m T := by
      simpa only [Set.uIcc_of_le hm.2.le] using hr
    have hr'' : r ∈ Set.Icc b T :=
      ⟨le_trans hm.1.le hr'.1, hr'.2⟩
    simpa only [Set.uIcc_of_le hb.2.le] using hr''
  have hConst : IntervalIntegrable (fun _ : ℝ => K) volume m T :=
    intervalIntegrable_const
  have hScaled : IntervalIntegrable (fun r : ℝ => 3 * D r)
      volume m T := hDtail.const_mul 3
  have hMajor : IntervalIntegrable
      (fun r : ℝ => C * (K + 3 * D r)) volume m T :=
    (hConst.add hScaled).const_mul C
  have hCompare :
      (∫ r in m..T, ‖G r‖ ∂volume) ≤
        ∫ r in m..T, C * (K + 3 * D r) ∂volume := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      hm.2.le hGtail.norm hMajor
    intro r hr
    have hrTime : r ∈ Set.Ioo b T :=
      ⟨lt_trans hm.1 hr.1, hr.2⟩
    exact h3Critical_projected_source_le_kinetic_anchor_add_dissipation
      hH3 hClass hb hrTime
  have hInner :
      (∫ r in m..T, K + 3 * D r ∂volume) =
        (T - m) * K + 3 * (∫ r in m..T, D r ∂volume) := by
    calc
      _ = (∫ _r in m..T, K ∂volume) +
            (∫ r in m..T, 3 * D r ∂volume) :=
              intervalIntegral.integral_add hConst hScaled
      _ = (T - m) * K + 3 * (∫ r in m..T, D r ∂volume) := by
          simp
  have hEvaluated :
      (∫ r in m..T, C * (K + 3 * D r) ∂volume) =
        C * (K * (T - m) + 3 * (∫ r in m..T, D r ∂volume)) := by
    rw [intervalIntegral.integral_const_mul, hInner]
    ring
  change (∫ r in m..T, ‖G r‖ ∂volume) ≤
    C * (K * (T - m) + 3 * (∫ r in m..T, D r ∂volume))
  calc
    (∫ r in m..T, ‖G r‖ ∂volume) ≤
        (∫ r in m..T, C * (K + 3 * D r) ∂volume) := hCompare
    _ = C * (K * (T - m) +
        3 * (∫ r in m..T, D r ∂volume)) := hEvaluated

/-- A scalar interval-integrable quantity has vanishing terminal subinterval
action along *any* cofinal increasing lower endpoints. This is applied to
the actual viscous dissipation, not to a positive-frequency surrogate. -/
theorem thirdFull_scalarTerminalTail_integral_tendsto_zero244
    (D : ℝ → ℝ) (a T : ℝ) (haT : a < T)
    (hD : IntervalIntegrable D volume a T)
    (m : ℕ → ℝ) (hm : Tendsto m atTop (𝓝 T))
    (hInside : ∀ᶠ k : ℕ in atTop, a ≤ m k ∧ m k ≤ T) :
    Tendsto (fun k : ℕ => ∫ r in m k..T, D r ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  let P : ℝ → ℝ := fun s => ∫ r in a..s, D r ∂volume
  have hCont : ContinuousOn P (Set.Icc a T) := by
    simpa only [P, Set.uIcc_of_le haT.le] using
      (intervalIntegral.continuousOn_primitive_interval' hD left_mem_uIcc)
  have hWithin : Tendsto P (𝓝[Set.Icc a T] T) (𝓝 (P T)) :=
    hCont T ⟨haT.le, le_rfl⟩
  have hInsideIcc : ∀ᶠ k : ℕ in atTop, m k ∈ Set.Icc a T := by
    filter_upwards [hInside] with k hk
    exact ⟨hk.1, hk.2⟩
  have hMWithin : Tendsto m atTop (𝓝[Set.Icc a T] T) :=
    tendsto_nhdsWithin_iff.mpr ⟨hm, hInsideIcc⟩
  have hP : Tendsto (fun k : ℕ => P (m k)) atTop (𝓝 (P T)) :=
    hWithin.comp hMWithin
  have hConstant : Tendsto (fun _ : ℕ => P T) atTop (𝓝 (P T)) :=
    tendsto_const_nhds
  have hDifference : Tendsto (fun k : ℕ => P T - P (m k))
      atTop (𝓝 (0 : ℝ)) := by
    have hSub := hConstant.sub hP
    simpa only [sub_self] using hSub
  have hIdentity :
      (fun k : ℕ => ∫ r in m k..T, D r ∂volume) =ᶠ[atTop]
        (fun k : ℕ => P T - P (m k)) := by
    filter_upwards [hInside] with k hk
    have hLeft : IntervalIntegrable D volume a (m k) := by
      apply hD.mono_set
      intro r hr
      have hr' : r ∈ Set.Icc a (m k) := by
        simpa only [Set.uIcc_of_le hk.1] using hr
      have hr'' : r ∈ Set.Icc a T :=
        ⟨hr'.1, hr'.2.trans hk.2⟩
      simpa only [Set.uIcc_of_le haT.le] using hr''
    have hRight : IntervalIntegrable D volume (m k) T := by
      apply hD.mono_set
      intro r hr
      have hr' : r ∈ Set.Icc (m k) T := by
        simpa only [Set.uIcc_of_le hk.2] using hr
      have hr'' : r ∈ Set.Icc a T :=
        ⟨hk.1.trans hr'.1, hr'.2⟩
      simpa only [Set.uIcc_of_le haT.le] using hr''
    have hAdd := intervalIntegral.integral_add_adjacent_intervals hLeft hRight
    change (∫ r in m k..T, D r ∂volume) =
      (∫ r in a..T, D r ∂volume) -
        (∫ r in a..m k, D r ∂volume)
    linarith only [hAdd]
  exact hDifference.congr' hIdentity.symm

/-- On the SAME prescribed-gauge minimal physical windows, the previously
unresolved delayed source arm must pay either a shrinking kinetic-time cost
or a genuine terminal H³ viscous integral. Together with the terminal Fourier
carrier and early attained source envelope, this is a FOUR-way alternative.
The terminal viscous tail vanishes, although the outer-frequency fourth
power multiplying it is not uniformly controlled. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_fourPhysicalChannels244
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
      (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244 hH3
        (fun n : ℕ => (H n) ^ 8) τ N K C δ (v k)) ∧
      (∀ j : ℕ,
        (∑ k ∈ Finset.range j,
          δ (v k) * ((H (v k)) ^ 8 / 4)) ≤
            ∫ r in a..T, velocityH3DissipationAt u r) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / H (v k)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        let t := τ (v k)
        let m := (t + T) / 2
        let Q := (N (v k) : ℝ) + 2
        let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
        let C₀ := 3 + h3AuditInitialLerayEnergyCoefficient
        let E₀ := 1 + 6 * velocityH3Energy0At u b
        (H (v k)) ^ 4 < 14 * Q ^ 4 *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
        (H (v k)) ^ 4 < 28 * Q ^ 4 *
          (‖F‖ * ((m - t) *
            h3PathActualProjectedSourceWindowEnvelope244 hH3 t m)) ∨
        (H (v k)) ^ 4 < 56 * Q ^ 4 *
          (‖F‖ * C₀ * ((T - m) * E₀)) ∨
        (H (v k)) ^ 4 < 168 * Q ^ 4 *
          (‖F‖ * C₀ *
            (∫ r in m..T, velocityH3DissipationAt u r ∂volume))) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in ((τ (v k) + T) / 2)..T,
          velocityH3DissipationAt u r ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hThree⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_halfTailThreeChannel244
      hH3 hClass b hb hNoTrace hDInt H hH
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let C₀ : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E₀ : ℝ := 1 + 6 * velocityH3Energy0At u b
  have hG : IntervalIntegrable G volume b T :=
    h3Critical_projected_source_integrable_of_finite_dissipation
      hH3 hClass hDInt b hb
  have hAfter : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  have hBefore (k : ℕ) : τ (v k) < T := by
    rcases (hWindows k).1.1 with
      ⟨_, _, _, hδ, _, hEnd, _, _, _, _, _, _, _⟩
    linarith only [hδ, hEnd]
  have hFour : ∀ᶠ k : ℕ in atTop,
      let t := τ (v k)
      let m := (t + T) / 2
      let Q := (N (v k) : ℝ) + 2
      let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
      let C₀ := 3 + h3AuditInitialLerayEnergyCoefficient
      let E₀ := 1 + 6 * velocityH3Energy0At u b
      (H (v k)) ^ 4 < 14 * Q ^ 4 *
        ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
      (H (v k)) ^ 4 < 28 * Q ^ 4 *
        (‖F‖ * ((m - t) *
          h3PathActualProjectedSourceWindowEnvelope244 hH3 t m)) ∨
      (H (v k)) ^ 4 < 56 * Q ^ 4 *
        (‖F‖ * C₀ * ((T - m) * E₀)) ∨
      (H (v k)) ^ 4 < 168 * Q ^ 4 *
        (‖F‖ * C₀ *
          (∫ r in m..T, velocityH3DissipationAt u r ∂volume)) := by
    filter_upwards [hThree, hAfter] with k hkThree hkAfter
    dsimp only at hkThree ⊢
    let t : ℝ := τ (v k)
    let m : ℝ := (t + T) / 2
    let Q : ℝ := (N (v k) : ℝ) + 2
    have hm : m ∈ Set.Ioo b T := by
      dsimp only [m, t]
      constructor <;> linarith only [hkAfter, hBefore k]
    rcases hkThree with hCarrier | hEarly | hDelayed
    · exact Or.inl hCarrier
    · exact Or.inr (Or.inl hEarly)
    · right; right
      have hSource :
          (∫ r in m..T, ‖G r‖ ∂volume) ≤
            C₀ * (E₀ * (T - m) +
              3 * (∫ r in m..T, velocityH3DissipationAt u r ∂volume)) :=
        thirdFullPhysical_delayedSource_le_kineticClock_add_viscosity244
          hH3 hClass hDInt b hb hG m hm
      have hSplit :
          ‖F‖ * (∫ r in m..T, ‖G r‖ ∂volume) ≤
            (‖F‖ * C₀ * ((T - m) * E₀)) +
              (‖F‖ * C₀ *
                (3 * (∫ r in m..T, velocityH3DissipationAt u r ∂volume))) := by
        calc
          _ ≤ ‖F‖ * (C₀ * (E₀ * (T - m) +
                3 * (∫ r in m..T, velocityH3DissipationAt u r ∂volume))) :=
              mul_le_mul_of_nonneg_left hSource (norm_nonneg F)
          _ = _ := by ring
      have hDelayed' : (H (v k)) ^ 4 <
          28 * Q ^ 4 *
            (‖F‖ * (∫ r in m..T, ‖G r‖ ∂volume)) := by
        simpa only [F, G, Q, t, m] using hDelayed
      rcases thirdFull_quartic_delayedSource_kineticOrViscous244
          ((H (v k)) ^ 4) Q
          (‖F‖ * (∫ r in m..T, ‖G r‖ ∂volume))
          (‖F‖ * C₀ * ((T - m) * E₀))
          (‖F‖ * C₀ *
            (3 * (∫ r in m..T, velocityH3DissipationAt u r ∂volume)))
          (by dsimp only [Q]; positivity) hDelayed' hSplit with hKin | hVisc
      · left
        convert hKin using 1 <;> ring
      · right
        convert hVisc using 1 <;> ring
  have hMid : Tendsto (fun k : ℕ => (τ (v k) + T) / 2)
      atTop (𝓝 T) := by
    have hHalf := (hLimit.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (T : ℝ)) atTop (𝓝 T))).div_const 2
    convert hHalf using 1 <;> ring
  have hRange : ∀ᶠ k : ℕ in atTop,
      a ≤ (τ (v k) + T) / 2 ∧ (τ (v k) + T) / 2 ≤ T := by
    filter_upwards [hAfter] with k hk
    constructor <;> linarith only [hb.1, hk, hBefore k]
  have hViscousTail : Tendsto (fun k : ℕ =>
      ∫ r in ((τ (v k) + T) / 2)..T,
        velocityH3DissipationAt u r ∂volume)
      atTop (𝓝 (0 : ℝ)) :=
    thirdFull_scalarTerminalTail_integral_tendsto_zero244
      (velocityH3DissipationAt u) a T hClass.terminal_start.2
      hDInt (fun k => (τ (v k) + T) / 2) hMid hRange
  exact ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
    hWindows, hCharges, hEscape, hFour, hViscousTail⟩

end
end PrimeTensor.FirstMonomialTriad

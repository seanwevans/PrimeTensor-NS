import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeViscousPeakTransfer
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousFiniteBandPersistence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Finite-band persistence of the actual prescribed-gauge late viscous spikes

The previous prescribed-gauge dichotomy extracts a genuine late physical
H³-dissipation spike at r ∈ ((t+T)/2,T). Full H³ dissipation is an unbounded
Fourier multiplier and its continuity does NOT follow from H³ continuity.

The existing finite-radial capture theorem instead places any strict spike
above an explicitly selected finite low-radial cutoff. That finite-frequency
quantity is continuous in time, so a positive right-hand persistence interval
exists. We attach this persistence interval to the exact same gauge-dependent
minimal crossing witnesses; it is a new interval, not asserted to be disjoint
from other late-peak windows or to coincide with the anchored PDE window.

If V = H(vk)^4 and P = 168 Q_k^4 ||F|| C_0 (T-m_k), the late branch gives
V < P D_H³(r). In particular P > 0. There is a cutoff J and η > 0 with

    V < P D_low,J(s) ≤ P D_H³(s)    (r ≤ s ≤ r+η),
    η * (V / P) ≤ ∫_(m_k)^T D_H³(s) ds.

The latter terminal integral tends to zero. This is a quantitative
necessary persistence-width compression law, NOT a frequency-independent
positive persistence width or a regularity proof. The open mechanism is to
control η from below using the actual physical PDE rate at the late spike.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A positive, coefficient-weighted *actual* late H³ viscous spike is
captured by a finite radial cutoff and has a nonzero persistence interval.
The real-valued integrated floor of that new window is paid by the SAME
terminal H³ dissipation tail that produced the pointwise spike. -/
theorem thirdFullPhysical_positiveLateViscousSpike_finiteBandTailCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m r P V : ℝ) (hm : m ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo m T)
    (hV : 0 < V)
    (hPeak : V < P * velocityH3DissipationAt u r) :
    0 < P ∧ ∃ (J : ℕ) (η : ℝ),
      0 < η ∧ r + η < T ∧
      (∀ s : ℝ, s ∈ Set.Icc r (r + η) →
        V < P * h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) ∧
        V < P * velocityH3DissipationAt u s) ∧
      η * (V / P) ≤
        ∫ s in m..T, velocityH3DissipationAt u s ∂volume := by
  let D : ℝ → ℝ := velocityH3DissipationAt u
  have hP : 0 < P := by
    by_contra hNot
    have hNonpos : P ≤ 0 := le_of_not_gt hNot
    have hDNonneg : 0 ≤ D r := velocityH3DissipationAt_nonneg u r
    have hProd : P * D r ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hNonpos hDNonneg
    have hActual : V < P * D r := hPeak
    linarith only [hV, hActual, hProd]
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hm.1 hr.1, hr.2⟩
  have hHeight : V / P < D r := by
    apply (div_lt_iff₀ hP).2
    simpa only [mul_comm] using hPeak
  obtain ⟨J, η, hη, hηEnd, hFloor, _hExtendedCost⟩ :=
    h3Critical_fullViscousSpike_has_finiteBandIntegratedRightWindow
      hH3 hClass r (V / P) hrClass hHeight
  have hDtail : IntervalIntegrable D volume m T := by
    apply hDInt.mono_set
    intro x hx
    have hx' : x ∈ Set.Icc m T := by
      simpa only [Set.uIcc_of_le hm.2.le] using hx
    have hx'' : x ∈ Set.Icc a T :=
      ⟨hm.1.le.trans hx'.1, hx'.2⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hx''
  have hDwindow : IntervalIntegrable D volume r (r + η) := by
    apply hDInt.mono_set
    intro x hx
    have hx' : x ∈ Set.Icc r (r + η) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right hη.le)] using hx
    have hx'' : x ∈ Set.Icc a T :=
      ⟨hrClass.1.le.trans hx'.1, hx'.2.trans hηEnd.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hx''
  have hWindowCharge : η * (V / P) ≤
      ∫ s in r..(r + η), D s ∂volume := by
    have hIntegral :
        (∫ _s in r..(r + η), V / P ∂volume) ≤
          ∫ s in r..(r + η), D s ∂volume := by
      apply intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right hη.le)
        intervalIntegrable_const hDwindow
      intro s hs
      exact (hFloor s hs).2.le
    calc
      η * (V / P) = ∫ _s in r..(r + η), V / P ∂volume := by
        simp [mul_comm] <;> ring
      _ ≤ ∫ s in r..(r + η), D s ∂volume := hIntegral
  have hNonnegative :
      0 ≤ᵐ[volume.restrict (Set.Ioc m T)] D := by
    filter_upwards [] with x
    exact velocityH3DissipationAt_nonneg u x
  have hTailCharge :
      (∫ s in r..(r + η), D s ∂volume) ≤
        ∫ s in m..T, D s ∂volume :=
    intervalIntegral.integral_mono_interval
      hr.1.le (le_add_of_nonneg_right hη.le) hηEnd.le hNonnegative hDtail
  refine ⟨hP, J, η, hη, hηEnd, ?_, hWindowCharge.trans hTailCharge⟩
  intro s hs
  have hLow : V / P <
      h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) := (hFloor s hs).1
  have hFull : V / P < D s := (hFloor s hs).2
  constructor
  · have h := (div_lt_iff₀ hP).1 hLow
    simpa only [mul_comm] using h
  · have h := (div_lt_iff₀ hP).1 hFull
    simpa only [mul_comm] using h

/-- Same prescribed-gauge minimal first-crossing family, now including a
finite-band right-hand persistence and a terminal *real* viscous charge for
every late-spike alternative. The new windows need not be pairwise disjoint.
This does not supply a uniform lower bound for their lengths η. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_lateFiniteBandCharge244
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
        let P := 168 * Q ^ 4 * (‖F‖ * C₀) * (T - m)
        (H (v k)) ^ 4 < 14 * Q ^ 4 *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
        (∃ r : ℝ, r ∈ Set.Icc t m ∧
          (H (v k)) ^ 4 < 28 * Q ^ 4 *
            (‖F‖ * ((m - t) *
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
        (H (v k)) ^ 4 < 56 * Q ^ 4 *
          (‖F‖ * C₀ * ((T - m) * E₀)) ∨
        (∃ (r : ℝ) (J : ℕ) (η : ℝ),
          r ∈ Set.Ioo m T ∧ 0 < η ∧ r + η < T ∧ 0 < P ∧
          (∀ s : ℝ, s ∈ Set.Icc r (r + η) →
            (H (v k)) ^ 4 < P *
              h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 s) ∧
            (H (v k)) ^ 4 < P * velocityH3DissipationAt u s) ∧
          η * ((H (v k)) ^ 4 / P) ≤
            ∫ s in m..T, velocityH3DissipationAt u s ∂volume)) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in ((τ (v k) + T) / 2)..T,
          velocityH3DissipationAt u r ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hPeaks, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_actualLateViscousPeak244
      hH3 hClass b hb hNoTrace hDInt H hH
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let C₀ : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  have hAfter : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  have hFinal : ∀ᶠ k : ℕ in atTop,
      let t := τ (v k)
      let m := (t + T) / 2
      let Q := (N (v k) : ℝ) + 2
      let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
      let C₀ := 3 + h3AuditInitialLerayEnergyCoefficient
      let E₀ := 1 + 6 * velocityH3Energy0At u b
      let P := 168 * Q ^ 4 * (‖F‖ * C₀) * (T - m)
      (H (v k)) ^ 4 < 14 * Q ^ 4 *
        ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
      (∃ r : ℝ, r ∈ Set.Icc t m ∧
        (H (v k)) ^ 4 < 28 * Q ^ 4 *
          (‖F‖ * ((m - t) *
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
      (H (v k)) ^ 4 < 56 * Q ^ 4 *
        (‖F‖ * C₀ * ((T - m) * E₀)) ∨
      (∃ (r : ℝ) (J : ℕ) (η : ℝ),
        r ∈ Set.Ioo m T ∧ 0 < η ∧ r + η < T ∧ 0 < P ∧
        (∀ s : ℝ, s ∈ Set.Icc r (r + η) →
          (H (v k)) ^ 4 < P *
            h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) ∧
          (H (v k)) ^ 4 < P * velocityH3DissipationAt u s) ∧
        η * ((H (v k)) ^ 4 / P) ≤
          ∫ s in m..T, velocityH3DissipationAt u s ∂volume) := by
    filter_upwards [hPeaks, hAfter] with k hkPeak hkAfter
    dsimp only at hkPeak ⊢
    let t : ℝ := τ (v k)
    let m : ℝ := (t + T) / 2
    let Q : ℝ := (N (v k) : ℝ) + 2
    let P : ℝ := 168 * Q ^ 4 * (‖F‖ * C₀) * (T - m)
    rcases hkPeak with hCarrier | hSource | hClock | ⟨r, hr, hViscous⟩
    · exact Or.inl hCarrier
    · exact Or.inr (Or.inl hSource)
    · exact Or.inr (Or.inr (Or.inl hClock))
    · right; right; right
      have hEnd : t < T := by
        rcases (hWindows k).1.1 with
          ⟨_, _, _, hδ, _, hEnd, _, _, _, _, _, _, _⟩
        dsimp only [t]
        linarith only [hδ, hEnd]
      have hm : m ∈ Set.Ioo a T := by
        dsimp only [m, t]
        constructor <;> linarith only [hb.1, hkAfter, hEnd]
      have hHeight : 0 < (H (v k)) ^ 4 :=
        pow_pos (lt_of_lt_of_le zero_lt_one (hH (v k))) 4
      have hLate : (H (v k)) ^ 4 <
          P * velocityH3DissipationAt u r := by
        dsimp only [P]
        convert hViscous using 1 <;> ring
      obtain ⟨hP, J, η, hη, hηEnd, hFloor, hCost⟩ :=
        thirdFullPhysical_positiveLateViscousSpike_finiteBandTailCharge244
          hH3 hClass hDInt m r P ((H (v k)) ^ 4)
          hm hr hHeight hLate
      exact ⟨r, J, η, hr, hη, hηEnd, hP, hFloor, hCost⟩
  exact ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
    hWindows, hCharges, hEscape, hFinal, hViscousTail⟩

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedComponentResidualEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralKineticAnchoredLowDissipationBudget244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralLowRadialTemporalContinuity244
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# Fixed-radius high-frequency H³ dissipation obstruction

For each fixed nonnegative Fourier radius, actual low-radial H³ dissipation
is continuous in positive physical time and uniformly bounded by a kinetic
anchor on a terminal tail; consequently it is time-integrable on that tail.
The exact radial partition then localizes the previously proved full H³
nonintegrability to high frequencies for every fixed radius. Cofinal high-
frequency H³ spikes follow without any temporal continuity of full H³
viscous dissipation or a positive terminal kinetic-mass assumption.

This result concerns H³ DISSIPATION, not the low-pass MOMENTUM SOURCE.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped Topology Interval

noncomputable section
set_option maxHeartbeats 800000

/-- Every fixed-radius low-frequency H³ dissipation is time-integrable on
any strict terminal tail, directly from the kinetic anchor. -/
theorem h3Critical_fixedRadial_lowDissipation_intervalIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    IntervalIntegrable
      (fun t : ℝ => h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t)) volume b T := by
  let L : ℝ → ℝ := fun t => h3PathActualLowRadialDissipation244 ρ
    (h3AuditActualSpectralVelocityTotal hH3 t)
  let C : ℝ := ρ ^ 2 *
    (h3TerminalRadialSobolevWeightSquareCeiling ρ * velocityH3Energy0At u b)
  have hSub : Set.Ioo b T ⊆ Set.Ioo a T := by
    intro t ht
    exact ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hCont : ContinuousOn L (Set.Ioo b T) :=
    (h3Path_actualLowRadialDissipation_continuousOn_positiveTime244
      hH3 hClass ρ hρ).mono hSub
  have hMeas : AEStronglyMeasurable L
      ((volume : Measure ℝ).restrict (Set.Ioo b T)) :=
    hCont.aestronglyMeasurable measurableSet_Ioo
  have hConst : IntervalIntegrable (fun _ : ℝ => max C 0) volume b T :=
    continuousOn_const.intervalIntegrable_of_Icc hb.2.le
  have hMajor : IntegrableOn (fun _ : ℝ => max C 0)
      (Set.Ioo b T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).1 hConst
  have hDom : ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioo b T)),
      ‖L t‖ ≤ max C 0 :=
    ae_restrict_of_forall_mem measurableSet_Ioo (by
      intro t ht
      have hLow : 0 ≤ L t := by
        dsimp only [L, h3PathActualLowRadialDissipation244]
        apply integral_nonneg
        intro ξ
        exact h3TerminalSpectralDissipationSingleDensity_nonneg _ ξ
      have hCeil : L t ≤ C :=
        h3Path_actualLowRadialDissipation_le_kineticAnchor244
          hH3 hClass b hb ρ hρ t ht
      rw [Real.norm_eq_abs, abs_of_nonneg hLow]
      exact hCeil.trans (le_max_left C 0))
  have hInt : IntegrableOn L (Set.Ioo b T) volume :=
    Integrable.mono' hMajor hMeas hDom
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).2 hInt

/-- High-frequency time integrability together with the automatic
low-frequency L¹ budget would make full H³ dissipation integrable. -/
theorem h3Critical_fullDissipation_integrable_of_fixedRadial_highIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHigh : IntervalIntegrable
      (fun t : ℝ => h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t)) volume b T) :
    IntervalIntegrable (velocityH3DissipationAt u) volume b T := by
  have hLow := h3Critical_fixedRadial_lowDissipation_intervalIntegrable
    hH3 hClass b hb ρ hρ
  have hSum : IntervalIntegrable
      (fun t : ℝ =>
        h3PathActualLowRadialDissipation244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 t) +
        h3PathActualHighRadialDissipation244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 t)) volume b T :=
    hLow.add hHigh
  have hSumOn : IntegrableOn
      (fun t : ℝ =>
        h3PathActualLowRadialDissipation244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 t) +
        h3PathActualHighRadialDissipation244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 t))
      (Set.Ioo b T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).1 hSum
  have hFullOn : IntegrableOn (velocityH3DissipationAt u)
      (Set.Ioo b T) volume := by
    apply IntegrableOn.congr_fun hSumOn (fun t ht => ?_) measurableSet_Ioo
    exact h3Path_actualRadialDissipation_partition244
      hH3 hClass t ⟨lt_trans hb.1 ht.1, ht.2⟩ ρ
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).2 hFullOn

/-- The high-frequency H³ dissipation beyond EVERY fixed cutoff is
non-L¹ on EVERY strict terminal tail when the physical L² trace fails. -/
theorem h3Critical_noL2Trace_highRadialDissipation_nonintegrable_everyFixedRadius
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∀ (b : ℝ), b ∈ Set.Ioo a T → ∀ (ρ : ℝ), 0 ≤ ρ →
      ¬ IntervalIntegrable
        (fun t : ℝ => h3PathActualHighRadialDissipation244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 t)) volume b T := by
  intro b hb ρ hρ hHigh
  exact (h3Critical_noL2Trace_forces_full_dissipation_nonintegrable_on_every_tail
    hH3 hClass hNoTrace b hb)
      (h3Critical_fullDissipation_integrable_of_fixedRadial_highIntegrable
        hH3 hClass b hb ρ hρ hHigh)

/-- Fixed-radius high-frequency H³ dissipation has arbitrarily large
spikes cofinally, even though its temporal continuity is not known. -/
theorem h3Critical_noL2Trace_highRadialDissipation_spikes_everyFixedRadius
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∀ (b : ℝ), b ∈ Set.Ioo a T → ∀ (ρ : ℝ), 0 ≤ ρ → ∀ M : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        M < h3PathActualHighRadialDissipation244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 t) := by
  intro b hb ρ hρ M
  let C : ℝ := ρ ^ 2 *
    (h3TerminalRadialSobolevWeightSquareCeiling ρ * velocityH3Energy0At u b)
  obtain ⟨t, ht, hSpike⟩ :=
    h3Critical_noL2Trace_fullDissipation_cofinally_unbounded
      hH3 hClass hNoTrace b hb (C + M)
  refine ⟨t, ht, ?_⟩
  have hLow := h3Path_actualLowRadialDissipation_le_kineticAnchor244
    hH3 hClass b hb ρ hρ t ht
  have hPartition := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ⟨lt_trans hb.1 ht.1, ht.2⟩ ρ
  dsimp only [C] at hSpike
  linarith only [hSpike, hLow, hPartition]

end
end PrimeTensor.Bridge.Euclidean

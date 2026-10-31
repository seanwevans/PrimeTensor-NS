import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationTerminalTrace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# Terminal nonintegrability obstruction from failure of the physical L² trace

The prior result proved that finite full H³ dissipation yields a strong
physical L² terminal trace.  This module sharpens the hypothesis to ANY
strict terminal subinterval. It separates the analytic mechanism:

* Actual projected source L¹ on (b,T) implies physical L² trace using
  the unconditional positive-time Hilbert FTC.
* Under the preterminal H³ energy class, full H³ dissipation L¹ on (b,T)
  implies actual projected source L¹ on the SAME interval.
* Hence failure of the physical trace forces BOTH integrabilities to fail
  on EVERY terminal subinterval, without assuming either integrability.

This is a conditional necessary obstruction, not an unconditional
regularity or smooth-continuation theorem.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped Topology Interval

noncomputable section
set_option maxHeartbeats 800000

/-- An L¹ actual physical projected momentum source on any terminal interval
forces a strong L² endpoint velocity. No H³ energy class is required. -/
theorem h3Critical_physicalL2_trace_of_integrable_projected_source_on_tail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : b ∈ Set.Ioo (0 : ℝ) T)
    (hG : IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
      volume b T) :
    ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hPrimitive :=
    h3Critical_integrable_primitive_terminal_limit G b T hb.2 hG
  have hNear : ∀ᶠ t : ℝ in (𝓝[<] T), t ∈ Set.Ioo b T := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hb.2)] with t htT hbt
    exact ⟨hbt, htT⟩
  have hFTC : (h3AuditInitialOldPhysicalHilbertTotal hH3) =ᶠ[𝓝[<] T]
      (fun t => h3AuditInitialOldPhysicalHilbertTotal hH3 b +
        ∫ s in b..t, G s) := by
    filter_upwards [hNear] with t ht
    exact h3Path_physicalHilbertEvolution_betweenPositiveTimes244
      hH3 b t hb ⟨lt_trans hb.1 ht.1, ht.2⟩
  refine ⟨h3AuditInitialOldPhysicalHilbertTotal hH3 b +
    ∫ s in b..T, G s, ?_⟩
  have hLimit : Tendsto
      (fun t => h3AuditInitialOldPhysicalHilbertTotal hH3 b +
        ∫ s in b..t, G s)
      (𝓝[<] T)
      (𝓝 (h3AuditInitialOldPhysicalHilbertTotal hH3 b +
        ∫ s in b..T, G s)) :=
    tendsto_const_nhds.add hPrimitive
  exact hLimit.congr' hFTC.symm

/-- Failure of a strong physical L² trace forces the *actual* projected
momentum source to be non-L¹ on every positive terminal interval. -/
theorem h3Critical_noL2Trace_forces_projected_source_nonintegrable_on_every_tail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      ¬ IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
        volume b T := by
  intro b hb hG
  exact hNoTrace
    (h3Critical_physicalL2_trace_of_integrable_projected_source_on_tail
      hH3 b hb hG)

/-- The pointwise affine full-dissipation majorant yields Bochner source
integrability from dissipation integrability on the SAME strict terminal tail.
The old theorem assumed dissipation integrability on the whole `(a,T)`;
this one uses only `(b,T)`. -/
theorem h3Critical_projected_source_integrable_of_tail_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume b T) :
    IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
      volume b T := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let C : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  have hConst : IntervalIntegrable
      (fun _ : ℝ => 1 + 6 * velocityH3Energy0At u b)
      volume b T :=
    continuousOn_const.intervalIntegrable_of_Icc hb.2.le
  have hScaled : IntervalIntegrable
      (fun s : ℝ => 3 * velocityH3DissipationAt u s)
      volume b T := hDInt.const_mul 3
  have hInner : IntervalIntegrable
      (fun s : ℝ => (1 + 6 * velocityH3Energy0At u b) +
        3 * velocityH3DissipationAt u s) volume b T :=
    hConst.add hScaled
  have hMajor : IntegrableOn
      (fun s : ℝ => C * (1 + 6 * velocityH3Energy0At u b +
        3 * velocityH3DissipationAt u s))
      (Set.Ioo b T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).1
      (hInner.const_mul C)
  have hSub : Set.Ioo b T ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1) hs.1, hs.2⟩
  have hCont : ContinuousOn G (Set.Ioo b T) := by
    have hFull := h3Audit_initialActualProjectedRHS_continuousOn_positiveTime hH3
    change ContinuousOn
      (fun s : ℝ => h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s) (Set.Ioo b T)
    exact hFull.mono hSub
  have hMeas : AEStronglyMeasurable G
      ((volume : Measure ℝ).restrict (Set.Ioo b T)) :=
    hCont.aestronglyMeasurable measurableSet_Ioo
  have hDom : ∀ᵐ s : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioo b T)),
      ‖G s‖ ≤ C * (1 + 6 * velocityH3Energy0At u b +
        3 * velocityH3DissipationAt u s) :=
    ae_restrict_of_forall_mem measurableSet_Ioo (by
      intro s hs
      exact h3Critical_projected_source_le_kinetic_anchor_add_dissipation
        hH3 hClass hb hs)
  have hG : IntegrableOn G (Set.Ioo b T) volume :=
    Integrable.mono' hMajor hMeas hDom
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).2 hG

/-- If the physical L² trace fails, full H³ dissipation is not time
integrable on ANY strict terminal subinterval. This does not assume full
H³ dissipation integrability, even temporarily in the theorem statement. -/
theorem h3Critical_noL2Trace_forces_full_dissipation_nonintegrable_on_every_tail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ¬ IntervalIntegrable (velocityH3DissipationAt u) volume b T := by
  intro b hb hDInt
  have hb0 : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  have hNoSource :=
    h3Critical_noL2Trace_forces_projected_source_nonintegrable_on_every_tail
      hH3 hNoTrace b hb0
  exact hNoSource
    (h3Critical_projected_source_integrable_of_tail_dissipation
      hH3 hClass b hb hDInt)

end
end PrimeTensor.Bridge.Euclidean

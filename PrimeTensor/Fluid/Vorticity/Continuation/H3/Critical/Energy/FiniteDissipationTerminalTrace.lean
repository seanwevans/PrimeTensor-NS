import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationPointwise
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalHilbertGlobalFTC
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopUnconditionalHilbertFTCKinetic244
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Full H³ dissipation produces an actual physical L² terminal trace

This proof uses only the verified pointwise source/dissipation bound and the
previously formalized, unconditional positive-time Hilbert-space momentum FTC.
No source ceiling, frequency cutoff cap, terminal-clock condition, or higher
radial moment majorant is assumed.

The terminal assertion remains conditional on interval-integrability of the
full fourth-spatial-derivative H³ viscous dissipation. It does NOT assert a
smooth H³ continuation or unconditional Navier--Stokes regularity.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped Topology Interval

noncomputable section
set_option maxHeartbeats 800000

/-- The existing pointwise source bound is an actual Bochner L¹ bound on
any terminal subtail if the full H³ dissipation is interval-integrable. -/
theorem h3Critical_projected_source_integrable_of_finite_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
      volume b T := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let C : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  have hTailD : IntervalIntegrable (velocityH3DissipationAt u) volume b T := by
    apply hDInt.mono_set
    intro s hs
    have hs' : s ∈ Set.Icc b T := by
      simpa only [Set.uIcc_of_le hb.2.le] using hs
    have hs'' : s ∈ Set.Icc a T :=
      ⟨le_trans hb.1.le hs'.1, hs'.2⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hs''
  have hConst : IntervalIntegrable
      (fun _ : ℝ => 1 + 6 * velocityH3Energy0At u b)
      volume b T :=
    continuousOn_const.intervalIntegrable_of_Icc hb.2.le
  have hScaled : IntervalIntegrable
      (fun s : ℝ => 3 * velocityH3DissipationAt u s)
      volume b T := hTailD.const_mul 3
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

/-- An interval-integrable Bochner source has a left terminal primitive
limit, including its actual endpoint Bochner integral. -/
theorem h3Critical_integrable_primitive_terminal_limit
    (G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b T : ℝ) (hbT : b < T)
    (hG : IntervalIntegrable G volume b T) :
    Tendsto (fun t : ℝ => ∫ s in b..t, G s) (𝓝[<] T)
      (𝓝 (∫ s in b..T, G s)) := by
  have hCont : ContinuousOn (fun t : ℝ => ∫ s in b..t, G s)
      (Set.Icc b T) := by
    simpa only [Set.uIcc_of_le hbT.le] using
      (intervalIntegral.continuousOn_primitive_interval'
        hG left_mem_uIcc)
  have hWithin : Tendsto (fun t : ℝ => ∫ s in b..t, G s)
      (𝓝[Set.Icc b T] T) (𝓝 (∫ s in b..T, G s)) :=
    hCont T ⟨hbT.le, le_rfl⟩
  have hNear : ∀ᶠ t : ℝ in (𝓝[<] T), t ∈ Set.Icc b T := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hbT)] with t htT hbt
    exact ⟨hbt.le, htT.le⟩
  have hSmaller : (𝓝[<] T) ≤ 𝓝[Set.Icc b T] T := by
    change (𝓝[<] T) ≤ 𝓝 T ⊓ 𝓟 (Set.Icc b T)
    exact le_inf nhdsWithin_le_nhds (le_principal_iff.mpr hNear)
  exact hWithin.mono_left hSmaller

/-- The finite-dissipation source is integrable through terminal time;
therefore the positive-time physical Hilbert FTC produces a strong L² trace.
Neither positive terminal kinetic mass nor a terminal H³ ceiling is needed. -/
theorem h3Critical_physicalL2_terminal_trace_of_finite_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) := by
  let b : ℝ := (a + T) / 2
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    constructor <;> linarith only [hClass.terminal_start.2]
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hG : IntervalIntegrable G volume b T :=
    h3Critical_projected_source_integrable_of_finite_dissipation
      hH3 hClass hDInt b hb
  have hPrimitive :=
    h3Critical_integrable_primitive_terminal_limit G b T hb.2 hG
  have hb0 : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  have hNear : ∀ᶠ t : ℝ in (𝓝[<] T), t ∈ Set.Ioo b T := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hb.2)] with t htT hbt
    exact ⟨hbt, htT⟩
  have hFTC : (h3AuditInitialOldPhysicalHilbertTotal hH3) =ᶠ[𝓝[<] T]
      (fun t => h3AuditInitialOldPhysicalHilbertTotal hH3 b +
        ∫ s in b..t, G s) := by
    filter_upwards [hNear] with t ht
    exact h3Path_physicalHilbertEvolution_betweenPositiveTimes244
      hH3 b t hb0 ⟨lt_trans hb0.1 ht.1, ht.2⟩
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

/-- The no-strong-L²-trace arm is impossible in the finite-full-dissipation
regime, without invoking the positive kinetic mass assumption. -/
theorem h3Critical_noL2Trace_incompatible_with_finite_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) : False :=
  hNoTrace (h3Critical_physicalL2_terminal_trace_of_finite_dissipation
    hH3 hClass hDInt)

end
end PrimeTensor.Bridge.Euclidean

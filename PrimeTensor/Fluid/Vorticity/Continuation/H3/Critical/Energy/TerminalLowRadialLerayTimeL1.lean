import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalLowRadialLerayPhysicalL2Bound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialActualPhysicalSourceMeasurability
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# Actual low-frequency physical Leray forcing is Bochner-L¹ in terminal time

The existing pointwise kinetic source estimate and finite-band L² theorem
control the norm of every physical low-pass nonlinear forcing component.
The remaining analytic issue is STRONG TIME MEASURABILITY of a sharp Fourier
cutoff. Here the sharp indicator is built as a genuine norm-one continuous
linear operator on the unweighted complex Fourier L² Hilbert space.

The actual Fourier Leray source is already jointly continuous in its H³
spectral inputs, and the actual spectral velocity is continuous in positive
time. Composition with the sharp cutoff and the already-established physical
inverse-Fourier decoder gives positive-time continuity of the ACTUAL low-band
physical nonlinear forcing. Its kinetic ceiling implies Bochner-L¹ on every
strict terminal tail.

This closes the nonlinear Leray part ONLY. The sharp-cutoff Laplacian and
identification of the combined cutoff with the physical projected source
are separate obligations, not tacit premises.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1600000

noncomputable local instance axisFintypeH3LowRadialLerayTimeL1
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3LowRadialLerayTimeL1 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Sharp cutoff on unweighted Fourier L² -/

/-- Sharp cutoff as a genuine Fourier L² state. -/
noncomputable def h3CriticalFourierSharpLowCutoffApply
    (ρ : ℝ) (F : H3FourierComplexL2) : H3FourierComplexL2 :=
  ((MeasureTheory.Lp.memLp F).indicator
      (measurableSet_h3TerminalRadialFrequencyBelow ρ)).toLp
    ((h3TerminalRadialFrequencyBelow ρ).indicator F)

/-- Precise almost-everywhere Fourier multiplier representative. -/
theorem h3Critical_fourierSharpLowCutoffApply_ae
    (ρ : ℝ) (F : H3FourierComplexL2) :
    (h3CriticalFourierSharpLowCutoffApply ρ F : H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
        (h3TerminalRadialFrequencyBelow ρ).indicator F := by
  -- Avoid unfolding the nested Fourier/WithLp representative during
  -- elaboration: isolate the indicator and its MemLp witness first.
  let S : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow ρ
  let f : H3FourierPoint3 → ℂ := F
  have hf : MemLp (S.indicator f) 2
      (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp F).indicator
      (measurableSet_h3TerminalRadialFrequencyBelow ρ)
  have hRep :
      ((hf.toLp (S.indicator f) : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)] S.indicator f :=
    MeasureTheory.MemLp.coeFn_toLp hf
  change ((hf.toLp (S.indicator f) : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)] S.indicator f
  exact hRep

/-- Sharp cutoff is nonexpansive in the Fourier L² norm. -/
theorem h3Critical_fourierSharpLowCutoffApply_norm_le
    (ρ : ℝ) (F : H3FourierComplexL2) :
    ‖h3CriticalFourierSharpLowCutoffApply ρ F‖ ≤ ‖F‖ := by
  unfold h3CriticalFourierSharpLowCutoffApply
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_def]
  exact ENNReal.toReal_mono (MeasureTheory.Lp.eLpNorm_ne_top F)
    (MeasureTheory.eLpNorm_indicator_le
      (s := h3TerminalRadialFrequencyBelow ρ)
      (f := (F : H3FourierPoint3 → ℂ)))

/-- Sharp cutoff is additive at the L² quotient level. -/
theorem h3Critical_fourierSharpLowCutoffApply_add
    (ρ : ℝ) (F G : H3FourierComplexL2) :
    h3CriticalFourierSharpLowCutoffApply ρ (F + G) =
      h3CriticalFourierSharpLowCutoffApply ρ F +
        h3CriticalFourierSharpLowCutoffApply ρ G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3Critical_fourierSharpLowCutoffApply_ae ρ (F + G),
    h3Critical_fourierSharpLowCutoffApply_ae ρ F,
    h3Critical_fourierSharpLowCutoffApply_ae ρ G,
    MeasureTheory.Lp.coeFn_add F G,
    MeasureTheory.Lp.coeFn_add
      (h3CriticalFourierSharpLowCutoffApply ρ F)
      (h3CriticalFourierSharpLowCutoffApply ρ G)
  ] with ξ hFG hF hG hIn hOut
  rw [hFG, hOut]
  by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ρ
  · simp only [Set.indicator_of_mem hξ, hIn, Pi.add_apply, hF, hG]
  · simp only [Set.indicator_of_notMem hξ, hF, hG, Pi.add_apply, add_zero]

/-- Sharp cutoff commutes with complex scaling. -/
theorem h3Critical_fourierSharpLowCutoffApply_smul
    (ρ : ℝ) (c : ℂ) (F : H3FourierComplexL2) :
    h3CriticalFourierSharpLowCutoffApply ρ (c • F) =
      c • h3CriticalFourierSharpLowCutoffApply ρ F := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3Critical_fourierSharpLowCutoffApply_ae ρ (c • F),
    h3Critical_fourierSharpLowCutoffApply_ae ρ F,
    MeasureTheory.Lp.coeFn_smul c F,
    MeasureTheory.Lp.coeFn_smul c
      (h3CriticalFourierSharpLowCutoffApply ρ F)
  ] with ξ hCF hF hIn hOut
  rw [hCF, hOut]
  -- `hOut` leaves a pointwise scalar action on a function; expose its
  -- argument before rewriting the cutoff representative `hF`.
  simp only [Pi.smul_apply]
  rw [hF]
  by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ρ
  · simp only [Set.indicator_of_mem hξ, hIn, Pi.smul_apply]
  · simp only [Set.indicator_of_notMem hξ, smul_zero]

/-- Norm-one complex-linear sharp Fourier cutoff on native L². -/
noncomputable def h3CriticalFourierSharpLowCutoffCLM
    (ρ : ℝ) : H3FourierComplexL2 →L[ℂ] H3FourierComplexL2 :=
  (show H3FourierComplexL2 →ₗ[ℂ] H3FourierComplexL2 from
    { toFun := h3CriticalFourierSharpLowCutoffApply ρ
      map_add' := h3Critical_fourierSharpLowCutoffApply_add ρ
      map_smul' := h3Critical_fourierSharpLowCutoffApply_smul ρ }).mkContinuous
        1 (fun F => by
          simpa using h3Critical_fourierSharpLowCutoffApply_norm_le ρ F)

/-- The previously constructed actual Fourier cutoff is this universal CLM
applied to the genuine nonlinear Fourier source, with no new representatives. -/
theorem h3Critical_lowRadialLerayFourierL2_eq_sharpCutoffCLM
    (ρ : ℝ) (U : H3SpectralVelocityState) (i : Fin 3) :
    h3CriticalLowRadialLerayFourierL2 ρ U i =
      h3CriticalFourierSharpLowCutoffCLM ρ
        (h3RawFinLerayOuterProductDivergenceFourierL2 U U i) := by
  change h3CriticalLowRadialLerayFourierL2 ρ U i =
    h3CriticalFourierSharpLowCutoffApply ρ
      (h3RawFinLerayOuterProductDivergenceFourierL2 U U i)
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3Critical_lowRadialLerayFourierL2_ae ρ U i,
    h3Critical_fourierSharpLowCutoffApply_ae ρ
      (h3RawFinLerayOuterProductDivergenceFourierL2 U U i),
    MeasureTheory.MemLp.coeFn_toLp
      (h3RawFinLerayOuterProductDivergence_memLp2 U U i)
  ] with ξ hA hB hForcing
  rw [hA, hB]
  by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ρ
  · simp only [Set.indicator_of_mem hξ]
    exact hForcing.symm
  · simp only [Set.indicator_of_notMem hξ]

/-! ## Continuity and actual terminal time Bochner integrability -/

/-- The nonlinear cutoff's physical scalar L² decoder varies continuously
with the true H³ spectral velocity input at every fixed radius. -/
theorem h3Critical_lowRadialLerayPhysicalL2_continuous
    (ρ : ℝ) (i : Fin 3) :
    Continuous (fun U : H3SpectralVelocityState =>
      h3CriticalLowRadialLerayPhysicalL2 ρ U i) := by
  have hDiagonal : Continuous
      (fun U : H3SpectralVelocityState => (U, U)) :=
    Continuous.prodMk continuous_id continuous_id
  have hRaw : Continuous (fun U : H3SpectralVelocityState =>
      h3RawFinLerayOuterProductDivergenceFourierL2 U U i) := by
    have hComp :=
      (continuous_h3RawFinLerayOuterProductDivergenceFourierL2 i).comp
        hDiagonal
    change Continuous (fun U : H3SpectralVelocityState =>
      h3RawFinLerayOuterProductDivergenceFourierL2 U U i) at hComp
    exact hComp
  have hCut : Continuous (fun U : H3SpectralVelocityState =>
      h3CriticalLowRadialLerayFourierL2 ρ U i) := by
    have hComp :=
      (h3CriticalFourierSharpLowCutoffCLM ρ).continuous.comp hRaw
    have hEq :
        (fun U : H3SpectralVelocityState =>
          h3CriticalLowRadialLerayFourierL2 ρ U i) =
        (fun U : H3SpectralVelocityState =>
          h3CriticalFourierSharpLowCutoffCLM ρ
            (h3RawFinLerayOuterProductDivergenceFourierL2 U U i)) := by
      funext U
      exact h3Critical_lowRadialLerayFourierL2_eq_sharpCutoffCLM ρ U i
    rw [hEq]
    exact hComp
  have hDecode : Continuous h3Path_physicalRawFourierDecoder244 := by
    unfold h3Path_physicalRawFourierDecoder244
    exact continuous_h3FromFourierRealL2.comp
      (continuous_h3RealPartFourierL2.comp
        ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ).symm.continuous))
  exact hDecode.comp hCut

/-- For every fixed Fourier radius and coordinate the actual kinetic low-pass
physical nonlinear source has a continuous positive-time trajectory. -/
theorem h3Critical_actual_lowRadialLerayPhysicalL2_continuousOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (i : Fin 3) :
    ContinuousOn (fun t : ℝ =>
      h3CriticalLowRadialLerayPhysicalL2 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) i)
      (Set.Ioo b T) := by
  have hSub : Set.Ioo b T ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 ht.1), ht.2⟩
  exact (h3Critical_lowRadialLerayPhysicalL2_continuous ρ i).comp_continuousOn
    ((h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hSub)

/-- The ACTUAL low-frequency real physical Leray source is Bochner-L¹ on
EVERY strict terminal tail, with no auxiliary measurability assumption. -/
theorem h3Critical_actual_lowRadialLerayPhysicalL2_intervalIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (i : Fin 3) :
    IntervalIntegrable (fun t : ℝ =>
      h3CriticalLowRadialLerayPhysicalL2 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) i)
      volume b T := by
  let B : ℝ → H3ScalarL2 := fun t =>
    h3CriticalLowRadialLerayPhysicalL2 ρ
      (h3AuditActualSpectralVelocityTotal hH3 t) i
  let C : ℝ := (volume : Measure H3FourierPoint3).real
    (h3TerminalRadialFrequencyBelow ρ) *
      (18 * (ρ * velocityH3Energy0At u b)) ^ 2
  have hBCont : ContinuousOn B (Set.Ioo b T) :=
    h3Critical_actual_lowRadialLerayPhysicalL2_continuousOn
      hH3 hClass b hb ρ i
  have hMeas : AEStronglyMeasurable B
      ((volume : Measure ℝ).restrict (Set.Ioo b T)) :=
    hBCont.aestronglyMeasurable measurableSet_Ioo
  have hCNonneg : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (measureReal_nonneg) (sq_nonneg _)
  have hKNonneg : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
  have hCeil : ∀ t : ℝ, t ∈ Set.Ioo b T →
      ‖B t‖ ≤ Real.sqrt C := by
    intro t ht
    have hSq : ‖B t‖ ^ 2 ≤ C :=
      h3Critical_actual_lowRadial_lerayPhysicalL2_sq_le_kineticAnchor
        hH3 hClass b hb ρ hρ t ht i
    have hRoot : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hCNonneg
    nlinarith only [hSq, hRoot, hKNonneg, norm_nonneg (B t)]
  have hConst : IntervalIntegrable
      (fun _ : ℝ => Real.sqrt C) volume b T := intervalIntegrable_const
  have hMajor : IntegrableOn (fun _ : ℝ => Real.sqrt C)
      (Set.Ioo b T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).1 hConst
  have hDom : ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioo b T)),
      ‖B t‖ ≤ Real.sqrt C :=
    ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => hCeil t ht)
  have hInt : IntegrableOn B (Set.Ioo b T) volume :=
    Integrable.mono' hMajor hMeas hDom
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).2 hInt

end
end PrimeTensor.Bridge.Euclidean

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalLowRadialLerayTimeL1
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Diffusion.Continuity
import Mathlib.Tactic

/-!
# Actual kinetic low-frequency Laplacian is Bochner-L¹ on terminal tails

The preceding nonlinear Leray argument constructs a continuous norm-one sharp
cutoff operator on Fourier L² and establishes physical Bochner-L¹ for the
actual low-band nonlinear forcing. The missing linear diffusion component can
be bounded by the *raw Fourier kinetic norm*, rather than by full H³ energy.

On the ball `2π‖ξ‖ < ρ`, the physical Laplacian multiplier has magnitude
`q(ξ) = (2π)²‖ξ‖² < ρ²`. Therefore

  ‖1_{Sρ} Δ̂u_j(t)‖₂ ≤ ρ² ‖û_j(t)‖₂ ≤ ρ² √E₀(b)

for all `b < t < T` and every component. The real inverse-Fourier decoder
preserves this upper bound. Its trajectory is continuous in positive time,
so it is Bochner-L¹ on every strict terminal tail.

This does not yet identify the cutoff of the *combined* projected physical
source. That commutation/identification is a separate remaining obligation.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1600000

noncomputable local instance axisFintypeH3LowRadialLaplacianTimeL1
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3LowRadialLaplacianTimeL1 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The actual raw Fourier Laplacian on a fixed gradient ball has L² norm
at most radius-squared times the raw Fourier velocity L² norm. -/
theorem h3Critical_lowRadialLaplacianFourierL2_norm_le_raw
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : H3SpectralScalarState) :
    ‖h3CriticalFourierSharpLowCutoffCLM ρ
      (h3SpectralScalarLaplacianRawFourierL2 G)‖ ≤
      ρ ^ 2 * ‖h3SpectralScalarRawFourierL2 G‖ := by
  change ‖h3CriticalFourierSharpLowCutoffApply ρ
      (h3SpectralScalarLaplacianRawFourierL2 G)‖ ≤ _
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    h3Critical_fourierSharpLowCutoffApply_ae ρ
      (h3SpectralScalarLaplacianRawFourierL2 G),
    h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw G
  ] with ξ hCut hLap
  rw [hCut]
  by_cases hS : ξ ∈ h3TerminalRadialFrequencyBelow ρ
  · rw [Set.indicator_of_mem hS, hLap]
    have hRad : h3FourierGradientMagnitude ξ < ρ := by
      change h3FourierGradientMagnitude ξ < ρ at hS
      exact hS
    have hSq : h3FourierGradientSquare ξ ≤ ρ ^ 2 := by
      calc
        h3FourierGradientSquare ξ = (h3FourierGradientMagnitude ξ) ^ 2 :=
          (h3FourierGradientMagnitude_sq ξ).symm
        _ ≤ ρ ^ 2 :=
          pow_le_pow_left₀ (h3FourierGradientMagnitude_nonneg ξ) hRad.le 2
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (h3FourierGradientSquare_nonneg ξ)]
    exact mul_le_mul_of_nonneg_right hSq (norm_nonneg _)
  · rw [Set.indicator_of_notMem hS, norm_zero]
    exact mul_nonneg (sq_nonneg _) (norm_nonneg _)

/-- Real physical L² reconstruction of the genuinely truncated Fourier
Laplacian of a weighted H³ scalar velocity coordinate. -/
noncomputable def h3CriticalLowRadialLaplacianPhysicalL2
    (ρ : ℝ) (G : H3SpectralScalarState) : H3ScalarL2 :=
  h3Path_physicalRawFourierDecoder244
    (h3CriticalFourierSharpLowCutoffCLM ρ
      (h3SpectralScalarLaplacianRawFourierL2 G))

/-- Physical decoder inherits the kinetic-scale low-frequency Fourier
Laplacian bound. -/
theorem h3Critical_lowRadialLaplacianPhysicalL2_norm_le_raw
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : H3SpectralScalarState) :
    ‖h3CriticalLowRadialLaplacianPhysicalL2 ρ G‖ ≤
      ρ ^ 2 * ‖h3SpectralScalarRawFourierL2 G‖ := by
  calc
    ‖h3CriticalLowRadialLaplacianPhysicalL2 ρ G‖ ≤
        ‖h3CriticalFourierSharpLowCutoffCLM ρ
          (h3SpectralScalarLaplacianRawFourierL2 G)‖ :=
      h3Path_physicalRawFourierDecoder_norm_le244 _
    _ ≤ ρ ^ 2 * ‖h3SpectralScalarRawFourierL2 G‖ :=
      h3Critical_lowRadialLaplacianFourierL2_norm_le_raw ρ hρ G

/-- The actual raw velocity Fourier L² coordinate is bounded by the
physical kinetic energy at every earlier strict anchor. -/
theorem h3Critical_actual_rawVelocityFourierL2_norm_le_kineticAnchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (i : Fin 3) :
    ‖h3SpectralScalarRawFourierL2
      ((h3AuditActualSpectralVelocityTotal hH3 t) i)‖ ≤
      Real.sqrt (velocityH3Energy0At u b) := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 htClass.1, htClass.2⟩
  rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
  exact h3Path_rawVelocityFourierL2_le_sqrtKineticAnchor244
    hH3 hClass hb htClass ht.1.le i

/-- The genuine low-frequency physical Laplacian has a uniform
kinetic-anchor ceiling, with no terminal H³ bound. -/
theorem h3Critical_actual_lowRadialLaplacianPhysicalL2_norm_le_kineticAnchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (i : Fin 3) :
    ‖h3CriticalLowRadialLaplacianPhysicalL2 ρ
      ((h3AuditActualSpectralVelocityTotal hH3 t) i)‖ ≤
        ρ ^ 2 * Real.sqrt (velocityH3Energy0At u b) := by
  calc
    ‖h3CriticalLowRadialLaplacianPhysicalL2 ρ
        ((h3AuditActualSpectralVelocityTotal hH3 t) i)‖ ≤
      ρ ^ 2 * ‖h3SpectralScalarRawFourierL2
        ((h3AuditActualSpectralVelocityTotal hH3 t) i)‖ :=
      h3Critical_lowRadialLaplacianPhysicalL2_norm_le_raw ρ hρ _
    _ ≤ ρ ^ 2 * Real.sqrt (velocityH3Energy0At u b) :=
      mul_le_mul_of_nonneg_left
        (h3Critical_actual_rawVelocityFourierL2_norm_le_kineticAnchor
          hH3 hClass b hb t ht i) (sq_nonneg ρ)

/-- Fixed-radius physical low-pass Laplacian is strongly continuous in
its weighted spectral H³ scalar input. -/
theorem h3Critical_lowRadialLaplacianPhysicalL2_continuous
    (ρ : ℝ) :
    Continuous (h3CriticalLowRadialLaplacianPhysicalL2 ρ) := by
  have hLap : Continuous h3SpectralScalarLaplacianRawFourierL2 :=
    continuous_h3SpectralScalarLaplacianRawFourierL2
  have hCut : Continuous (fun G : H3SpectralScalarState =>
      h3CriticalFourierSharpLowCutoffCLM ρ
        (h3SpectralScalarLaplacianRawFourierL2 G)) :=
    (h3CriticalFourierSharpLowCutoffCLM ρ).continuous.comp hLap
  have hDecode : Continuous h3Path_physicalRawFourierDecoder244 := by
    unfold h3Path_physicalRawFourierDecoder244
    exact continuous_h3FromFourierRealL2.comp
      (continuous_h3RealPartFourierL2.comp
        ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ).symm.continuous))
  exact hDecode.comp hCut

/-- The actual physical low-pass Laplacian component varies continuously
on every strict positive-time terminal tail. -/
theorem h3Critical_actual_lowRadialLaplacianPhysicalL2_continuousOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (i : Fin 3) :
    ContinuousOn (fun t : ℝ =>
      h3CriticalLowRadialLaplacianPhysicalL2 ρ
        ((h3AuditActualSpectralVelocityTotal hH3 t) i))
      (Set.Ioo b T) := by
  have hSub : Set.Ioo b T ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 ht.1), ht.2⟩
  have hU : ContinuousOn (h3AuditActualSpectralVelocityTotal hH3)
      (Set.Ioo b T) :=
    (h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hSub
  have hCoord : Continuous
      (fun U : H3SpectralVelocityState => U i) := continuous_apply i
  exact (h3Critical_lowRadialLaplacianPhysicalL2_continuous ρ).comp_continuousOn
    (hCoord.comp_continuousOn hU)

/-- Every actual physical low-frequency Laplacian coordinate is
Bochner-L¹ on every strict terminal tail. -/
theorem h3Critical_actual_lowRadialLaplacianPhysicalL2_intervalIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (i : Fin 3) :
    IntervalIntegrable (fun t : ℝ =>
      h3CriticalLowRadialLaplacianPhysicalL2 ρ
        ((h3AuditActualSpectralVelocityTotal hH3 t) i))
      volume b T := by
  let B : ℝ → H3ScalarL2 := fun t =>
    h3CriticalLowRadialLaplacianPhysicalL2 ρ
      ((h3AuditActualSpectralVelocityTotal hH3 t) i)
  let C : ℝ := ρ ^ 2 * Real.sqrt (velocityH3Energy0At u b)
  have hBCont : ContinuousOn B (Set.Ioo b T) :=
    h3Critical_actual_lowRadialLaplacianPhysicalL2_continuousOn
      hH3 hClass b hb ρ i
  have hMeas : AEStronglyMeasurable B
      ((volume : Measure ℝ).restrict (Set.Ioo b T)) :=
    hBCont.aestronglyMeasurable measurableSet_Ioo
  have hCeil : ∀ t : ℝ, t ∈ Set.Ioo b T → ‖B t‖ ≤ C := by
    intro t ht
    exact h3Critical_actual_lowRadialLaplacianPhysicalL2_norm_le_kineticAnchor
      hH3 hClass b hb ρ hρ t ht i
  have hConst : IntervalIntegrable (fun _ : ℝ => C) volume b T :=
    intervalIntegrable_const
  have hMajor : IntegrableOn (fun _ : ℝ => C)
      (Set.Ioo b T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).1 hConst
  have hDom : ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioo b T)),
      ‖B t‖ ≤ C :=
    ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => hCeil t ht)
  have hInt : IntegrableOn B (Set.Ioo b T) volume :=
    Integrable.mono' hMajor hMeas hDom
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).2 hInt


/-- The combined kinetic low-band projected Fourier RHS decodes to exactly
the difference of the separately reconstructed low-pass Laplacian and Leray
terms. This is an identity of reconstructed objects, not yet an identification
with a separate physical-space Fourier projection operator. -/
theorem h3Critical_lowRadialProjectedPhysicalL2_eq_decode
    (ρ : ℝ) (U : H3SpectralVelocityState) (i : Fin 3) :
    h3CriticalLowRadialLaplacianPhysicalL2 ρ (U i) -
        h3CriticalLowRadialLerayPhysicalL2 ρ U i =
      h3Path_physicalRawFourierDecoder244
        (h3CriticalFourierSharpLowCutoffCLM ρ
          (h3SpectralScalarLaplacianRawFourierL2 (U i) -
            h3RawFinLerayOuterProductDivergenceFourierL2 U U i)) := by
  let D : H3FourierComplexL2 :=
    h3CriticalFourierSharpLowCutoffCLM ρ
      (h3SpectralScalarLaplacianRawFourierL2 (U i))
  let N : H3FourierComplexL2 :=
    h3CriticalFourierSharpLowCutoffCLM ρ
      (h3RawFinLerayOuterProductDivergenceFourierL2 U U i)
  have hLeray : h3CriticalLowRadialLerayFourierL2 ρ U i = N :=
    h3Critical_lowRadialLerayFourierL2_eq_sharpCutoffCLM ρ U i
  change h3Path_physicalRawFourierDecoder244 D -
    h3Path_physicalRawFourierDecoder244
      (h3CriticalLowRadialLerayFourierL2 ρ U i) = _
  rw [hLeray]
  rw [← h3Path_physicalRawFourierDecoder_sub244 D N]
  rw [map_sub]

/-- Actual low-frequency reconstructed projected momentum RHS is Bochner-L¹
on every strict terminal tail; this combines the two genuine components. -/
theorem h3Critical_actual_lowRadialProjectedPhysicalL2_intervalIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (i : Fin 3) :
    IntervalIntegrable (fun t : ℝ =>
      h3CriticalLowRadialLaplacianPhysicalL2 ρ
          ((h3AuditActualSpectralVelocityTotal hH3 t) i) -
        h3CriticalLowRadialLerayPhysicalL2 ρ
          (h3AuditActualSpectralVelocityTotal hH3 t) i)
      volume b T := by
  exact
    (h3Critical_actual_lowRadialLaplacianPhysicalL2_intervalIntegrable
      hH3 hClass b hb ρ hρ i).sub
    (h3Critical_actual_lowRadialLerayPhysicalL2_intervalIntegrable
      hH3 hClass b hb ρ hρ i)

end
end PrimeTensor.Bridge.Euclidean

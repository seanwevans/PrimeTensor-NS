import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralAbsoluteHighSubcutoffEscape244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralCubicDissipationIntegratedWindows244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialActualPhysicalSourceMeasurability
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# Automatic positive-time continuity of bounded-frequency H³ dissipation

The actual weighted spectral velocity is strongly continuous at all strictly
positive times (the existing initial-actual-spectral-velocity theorem). A
bounded Fourier multiplier, unlike the full unbounded H³ dissipation symbol,
is continuous on weighted spectral L². We construct its exact Hilbert realization:

  M_ρ(G)(ξ) = 1_{|D(ξ)|<ρ} |D(ξ)| G(ξ).

The actual low-frequency dissipation is the sum of squared L² norms of M_ρ
on the three velocity components, so it is continuous in time automatically.

This discharges the LOW-dissipation continuity premise from the previous
cubic integrated window theorem. Full H³ dissipation continuity remains
explicit: it does not follow from H³ spectral continuity without additional
fourth-order control. No uniform width or terminal integrated blowup follows.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3LowRadialTemporal244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3LowRadialTemporal244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Bounded radial gradient multiplier; its jump at the ball boundary is
measurable, which is all an L² multiplier requires. -/
noncomputable def h3PathLowRadialGradientMultiplier244
    (ρ : ℝ) (ξ : H3FourierPoint3) : ℝ := by
  classical
  exact if ξ ∈ h3TerminalRadialFrequencyBelow ρ then
    h3FourierGradientMagnitude ξ else 0

/-- The cutoff Fourier multiplier has a uniform, nonnegative bound. -/
theorem h3Path_lowRadialGradientMultiplier_mem_Icc244
    (ρ : ℝ) (hρ : 0 ≤ ρ) (ξ : H3FourierPoint3) :
    h3PathLowRadialGradientMultiplier244 ρ ξ ∈ Set.Icc (0 : ℝ) (ρ + 1) := by
  classical
  by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ρ
  · have hq : h3FourierGradientMagnitude ξ < ρ := by
      simpa only [h3TerminalRadialFrequencyBelow, Set.mem_ofPred_eq] using hξ
    simp only [h3PathLowRadialGradientMultiplier244, if_pos hξ]
    exact ⟨h3FourierGradientMagnitude_nonneg ξ, by linarith⟩
  · simp only [h3PathLowRadialGradientMultiplier244, if_neg hξ]
    exact ⟨le_refl (0 : ℝ), by linarith⟩

/-- A sharp radial cutoff is measurable even though not continuous in ξ. -/
theorem h3Path_lowRadialGradientMultiplier_measurable244
    (ρ : ℝ) : Measurable (h3PathLowRadialGradientMultiplier244 ρ) := by
  have hq : Continuous h3FourierGradientMagnitude := by
    unfold h3FourierGradientMagnitude
    fun_prop
  unfold h3PathLowRadialGradientMultiplier244
  classical
  exact Measurable.ite
    (measurableSet_h3TerminalRadialFrequencyBelow ρ)
    hq.measurable measurable_const

/-- The cutoff-gradient product belongs to the native Fourier L² space. -/
theorem h3Path_lowRadialGradientMultiplier_memLp244
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : H3SpectralScalarState) :
    MemLp (fun ξ : H3FourierPoint3 =>
      (h3PathLowRadialGradientMultiplier244 ρ ξ : ℂ) * G ξ)
      2 (volume : Measure H3FourierPoint3) := by
  refine (MeasureTheory.Lp.memLp G).of_le_mul (c := ρ + 1) ?_ ?_
  · exact
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable
        (h3Path_lowRadialGradientMultiplier_measurable244 ρ).aestronglyMeasurable).mul
        (MeasureTheory.Lp.aestronglyMeasurable G))
  · filter_upwards with ξ
    have hm := h3Path_lowRadialGradientMultiplier_mem_Icc244 ρ hρ ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hm.1]
    exact mul_le_mul_of_nonneg_right hm.2 (norm_nonneg (G ξ))

noncomputable def h3PathLowRadialGradientMultiplierApply244
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : H3SpectralScalarState) :
    H3FourierComplexL2 :=
  (h3Path_lowRadialGradientMultiplier_memLp244 ρ hρ G).toLp
    (fun ξ : H3FourierPoint3 =>
      (h3PathLowRadialGradientMultiplier244 ρ ξ : ℂ) * G ξ)

/-- The multiplier's genuine L² representative. -/
theorem h3Path_lowRadialGradientMultiplierApply_ae244
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : H3SpectralScalarState) :
    (h3PathLowRadialGradientMultiplierApply244 ρ hρ G :
      H3FourierPoint3 → ℂ) =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (h3PathLowRadialGradientMultiplier244 ρ ξ : ℂ) * G ξ) := by
  exact MeasureTheory.MemLp.coeFn_toLp
    (h3Path_lowRadialGradientMultiplier_memLp244 ρ hρ G)

/-- Uniform L² operator bound for the sharp radial-gradient cutoff. -/
theorem h3Path_lowRadialGradientMultiplierApply_norm_le244
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : H3SpectralScalarState) :
    ‖h3PathLowRadialGradientMultiplierApply244 ρ hρ G‖ ≤
      (ρ + 1) * ‖G‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [h3Path_lowRadialGradientMultiplierApply_ae244 ρ hρ G]
    with ξ hξ
  rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (h3Path_lowRadialGradientMultiplier_mem_Icc244 ρ hρ ξ).1]
  exact mul_le_mul_of_nonneg_right
    (h3Path_lowRadialGradientMultiplier_mem_Icc244 ρ hρ ξ).2 (norm_nonneg _)

/-- The bounded radial Fourier multiplier is additive. -/
theorem h3Path_lowRadialGradientMultiplierApply_add244
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G H : H3SpectralScalarState) :
    h3PathLowRadialGradientMultiplierApply244 ρ hρ (G + H) =
      h3PathLowRadialGradientMultiplierApply244 ρ hρ G +
        h3PathLowRadialGradientMultiplierApply244 ρ hρ H := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3Path_lowRadialGradientMultiplierApply_ae244 ρ hρ (G + H),
    h3Path_lowRadialGradientMultiplierApply_ae244 ρ hρ G,
    h3Path_lowRadialGradientMultiplierApply_ae244 ρ hρ H,
    MeasureTheory.Lp.coeFn_add G H,
    MeasureTheory.Lp.coeFn_add
      (h3PathLowRadialGradientMultiplierApply244 ρ hρ G)
      (h3PathLowRadialGradientMultiplierApply244 ρ hρ H)
  ] with ξ hGH hG hH hIn hOut
  rw [hGH, hOut]
  simp only [Pi.add_apply, hG, hH, hIn, mul_add]

/-- Complex homogeneity of the sharp Fourier multiplier. -/
theorem h3Path_lowRadialGradientMultiplierApply_smul244
    (ρ : ℝ) (hρ : 0 ≤ ρ) (c : ℂ) (G : H3SpectralScalarState) :
    h3PathLowRadialGradientMultiplierApply244 ρ hρ (c • G) =
      c • h3PathLowRadialGradientMultiplierApply244 ρ hρ G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3Path_lowRadialGradientMultiplierApply_ae244 ρ hρ (c • G),
    h3Path_lowRadialGradientMultiplierApply_ae244 ρ hρ G,
    MeasureTheory.Lp.coeFn_smul c G,
    MeasureTheory.Lp.coeFn_smul c
      (h3PathLowRadialGradientMultiplierApply244 ρ hρ G)
  ] with ξ hCG hG hIn hOut
  rw [hCG, hOut]
  simp only [Pi.smul_apply, smul_eq_mul, hG, hIn]
  ring

/-- A genuine continuous linear Fourier multiplier on native weighted L². -/
noncomputable def h3PathLowRadialGradientMultiplierCLM244
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    H3SpectralScalarState →L[ℂ] H3FourierComplexL2 :=
  (show H3SpectralScalarState →ₗ[ℂ] H3FourierComplexL2 from
    { toFun := h3PathLowRadialGradientMultiplierApply244 ρ hρ
      map_add' := h3Path_lowRadialGradientMultiplierApply_add244 ρ hρ
      map_smul' := h3Path_lowRadialGradientMultiplierApply_smul244 ρ hρ }).mkContinuous
        (ρ + 1) (fun G =>
          h3Path_lowRadialGradientMultiplierApply_norm_le244 ρ hρ G)

@[simp] theorem h3Path_lowRadialGradientMultiplierCLM_apply244
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : H3SpectralScalarState) :
    h3PathLowRadialGradientMultiplierCLM244 ρ hρ G =
      h3PathLowRadialGradientMultiplierApply244 ρ hρ G := rfl

/-- One coordinate's low-frequency physical dissipation is exactly the
squared norm of the contractive Fourier-cutoff operator. -/
theorem h3Path_lowRadialGradientMultiplier_norm_sq_eq_integral244
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : H3SpectralScalarState) :
    ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ G‖ ^ 2 =
      ∫ ξ in h3TerminalRadialFrequencyBelow ρ,
        h3FourierGradientSquare ξ * ‖G ξ‖ ^ 2 ∂volume := by
  rw [h3Path_lowRadialGradientMultiplierCLM_apply244,
    h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
  rw [← integral_indicator (measurableSet_h3TerminalRadialFrequencyBelow ρ)]
  apply integral_congr_ae
  filter_upwards [h3Path_lowRadialGradientMultiplierApply_ae244 ρ hρ G]
    with ξ hξ
  rw [hξ]
  by_cases hξS : ξ ∈ h3TerminalRadialFrequencyBelow ρ
  · rw [Set.indicator_of_mem hξS]
    simp only [h3PathLowRadialGradientMultiplier244, if_pos hξS]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (h3FourierGradientMagnitude_nonneg ξ), mul_pow,
      h3FourierGradientMagnitude_sq]
  · rw [Set.indicator_of_notMem hξS]
    simp [h3PathLowRadialGradientMultiplier244, hξS]

/-- Integrability of the bounded-radial coordinate dissipation density needs
only weighted spectral L², not a globally integrable H⁴ dissipation. -/
theorem h3Path_lowRadialGradientCoordinate_integrableOn244
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : H3SpectralScalarState) :
    IntegrableOn (fun ξ : H3FourierPoint3 =>
      h3FourierGradientSquare ξ * ‖G ξ‖ ^ 2)
      (h3TerminalRadialFrequencyBelow ρ) volume := by
  let S : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow ρ
  have hMajor : Integrable
      (fun ξ : H3FourierPoint3 => ρ ^ 2 * ‖G ξ‖ ^ 2)
      (volume.restrict S) :=
    (((MeasureTheory.Lp.memLp G).norm.integrable_sq).const_mul
      (ρ ^ 2)).mono_measure Measure.restrict_le_self
  have hq : Continuous h3FourierGradientSquare := by
    unfold h3FourierGradientSquare
    fun_prop
  have hMeas : AEStronglyMeasurable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ * ‖G ξ‖ ^ 2)
      (volume.restrict S) :=
    (hq.aestronglyMeasurable.mul
      ((MeasureTheory.Lp.aestronglyMeasurable G).norm.pow 2)).mono_measure
        Measure.restrict_le_self
  apply Integrable.mono' hMajor hMeas
  rw [ae_restrict_iff' (measurableSet_h3TerminalRadialFrequencyBelow ρ)]
  filter_upwards with ξ hξ
  have hBound : h3FourierGradientSquare ξ ≤ ρ ^ 2 := by
    rw [← h3FourierGradientMagnitude_sq]
    have hξ' : h3FourierGradientMagnitude ξ < ρ := by
      simpa only [S, h3TerminalRadialFrequencyBelow,
        Set.mem_ofPred_eq] using hξ
    exact pow_le_pow_left₀ (h3FourierGradientMagnitude_nonneg ξ) hξ'.le 2
  have hProductNonneg :
      0 ≤ h3FourierGradientSquare ξ * ‖G ξ‖ ^ 2 :=
    mul_nonneg (h3FourierGradientSquare_nonneg ξ) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hProductNonneg]
  exact mul_le_mul_of_nonneg_right hBound (sq_nonneg _)

/-- Exact three-component Hilbert realization of *actual* low-radial H³
dissipation. The equality holds for every weighted spectral L² state. -/
theorem h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : H3SpectralVelocityState) :
    h3PathActualLowRadialDissipation244 ρ G =
      ∑ j : Fin 3,
        ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ (G j)‖ ^ 2 := by
  let S : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow ρ
  let A : Fin 3 → H3FourierPoint3 → ℝ := fun j ξ =>
    h3FourierGradientSquare ξ * ‖G j ξ‖ ^ 2
  have hInt (j : Fin 3) : Integrable (A j) (volume.restrict S) := by
    dsimp only [A, S]
    exact h3Path_lowRadialGradientCoordinate_integrableOn244 ρ hρ (G j)
  calc
    h3PathActualLowRadialDissipation244 ρ G =
        ∫ ξ in S, (A 0 ξ + A 1 ξ) + A 2 ξ ∂volume := by
          unfold h3PathActualLowRadialDissipation244
          apply integral_congr_ae
          filter_upwards with ξ
          dsimp only [S, A]
          unfold h3TerminalSpectralDissipationSingleDensity
          ring
    _ = (∫ ξ in S, A 0 ξ ∂volume) +
          (∫ ξ in S, A 1 ξ ∂volume) +
          (∫ ξ in S, A 2 ξ ∂volume) := by
          have h01 := integral_add (hInt 0) (hInt 1)
          have h012 := integral_add ((hInt 0).add (hInt 1)) (hInt 2)
          simp only [Pi.add_apply] at h01 h012
          rw [h012, h01]
    _ = ∑ j : Fin 3,
        ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ (G j)‖ ^ 2 := by
          simp only [Fin.sum_univ_three]
          rw [h3Path_lowRadialGradientMultiplier_norm_sq_eq_integral244 ρ hρ (G 0),
            h3Path_lowRadialGradientMultiplier_norm_sq_eq_integral244 ρ hρ (G 1),
            h3Path_lowRadialGradientMultiplier_norm_sq_eq_integral244 ρ hρ (G 2)]

/-- The low-radial H³ dissipation quadratic is continuous on the native
weighted H³ Hilbert state, for every fixed nonnegative radius. -/
theorem h3Path_actualLowRadialDissipation_continuous244
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Continuous (h3PathActualLowRadialDissipation244 ρ) := by
  have hQ : Continuous (fun G : H3SpectralVelocityState =>
      ∑ j : Fin 3,
        ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ (G j)‖ ^ 2) := by
    apply continuous_finsetSum Finset.univ
    intro j _
    exact (continuous_norm.comp
      ((h3PathLowRadialGradientMultiplierCLM244 ρ hρ).continuous.comp
        (continuous_apply j))).pow 2
  convert hQ using 1
  funext G
  exact h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 ρ hρ G

/-- The previously conditional low-frequency continuity requirement follows
from the already-closed strong positive-time actual spectral state continuity. -/
theorem h3Path_actualLowRadialDissipation_continuousOn_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ContinuousOn (fun t : ℝ =>
      h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t)) (Set.Ioo a T) := by
  have hSub : Set.Ioo a T ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  exact (h3Path_actualLowRadialDissipation_continuous244 ρ hρ).comp_continuousOn
    ((h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hSub)

/-- Cubic high-radial integral windows now require only TOTAL dissipation
continuity. Bounded-frequency continuity has been discharged from the path. -/
theorem h3Path_noL2Trace_forces_cubicIntegralWindows_of_totalContinuous244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDCont : ContinuousOn (velocityH3DissipationAt u) (Set.Ioo a T)) :
    ∃ (τ δ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, 0 < δ n ∧ τ n + δ n < T) ∧
      (∀ n : ℕ, ∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ n : ℕ, δ n * (((n : ℝ) + 1) ^ 3 / 2) ≤
        (∫ s in τ n..(τ n + δ n),
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s))) := by
  exact h3Path_noL2Trace_forces_cubicHighDissipationIntegralWindows244
    hH3 hClass hMass hNoTrace hDCont
    (fun n => h3Path_actualLowRadialDissipation_continuousOn_positiveTime244
      hH3 hClass ((n : ℝ) + 1) (by positivity))

end
end PrimeTensor.FirstMonomialTriad

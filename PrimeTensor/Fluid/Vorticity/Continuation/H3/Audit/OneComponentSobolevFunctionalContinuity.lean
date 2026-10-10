import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentHomogeneousSobolev
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Raw.L2.Shift

/-!
# Continuity of the homogeneous three-halves Fourier energy functional

The previous audit proved the frequencywise domination

  sqrt(q^3) * |W3^(-1) G|^2 <= |G|^2.

The coefficient `sqrt (sqrt(q^3)) / W3` is consequently bounded by one.
This file turns that coefficient into a contractive complex-linear Fourier L2
multiplier. The exact homogeneous three-halves energy is the squared norm of
that multiplier; hence it is a continuous function of the weighted H3 state.

Consequently temporal measurability of the *actual* homogeneous density
follows from a measurable canonical weighted-spectral state path, a better
specified interface than assuming measurability of the scalar density itself.

Crucially, neither pathwise convergence at T nor continuity of the *total*
H3 energy automatically establishes measurability of each component's spectral
state path. That separate preterminal-time PDE obligation is NOT assumed closed.
No published one-component continuation theorem is used in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

noncomputable local instance axisFintypeH3AuditSobolevFunctionalContinuity
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

-- The `Lp` Hilbert state has a norm topology but no default measurable-space
-- instance. Use precisely its Borel sigma-algebra for the state-time bridge.
noncomputable local instance h3AuditSpectralScalarBorelMeasurable :
    MeasurableSpace H3SpectralScalarState :=
  borel H3SpectralScalarState

local instance h3AuditSpectralScalarBorelSpace :
    BorelSpace H3SpectralScalarState where
  measurable_eq := rfl

/-- The nonnegative bounded multiplier whose output L2 norm is the homogeneous
three-halves Fourier seminorm. Here q=(2 pi)^2 |xi|^2 and W3 is the native H3
weight. -/
noncomputable def h3AuditThreeHalvesFourierMultiplier
    (ξ : H3FourierPoint3) : ℝ :=
  Real.sqrt (Real.sqrt (h3FourierGradientSquare ξ ^ 3)) *
    h3SobolevFrequencyWeightInv ξ

/-- The multiplier is nonnegative and no larger than one. -/
theorem h3Audit_threeHalvesMultiplier_mem_Icc
    (ξ : H3FourierPoint3) :
    h3AuditThreeHalvesFourierMultiplier ξ ∈ Set.Icc (0 : ℝ) 1 := by
  let W : ℝ := h3SobolevFrequencyWeight ξ
  let s : ℝ := Real.sqrt (h3FourierGradientSquare ξ ^ 3)
  have hW : 0 < W := h3SobolevFrequencyWeight_pos ξ
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hSmall : s ≤ W ^ 2 :=
    h3Audit_sqrt_gradientCube_le_sobolevWeightSquare ξ
  have hSqrt : Real.sqrt s ≤ W := by
    have h := Real.sqrt_le_sqrt hSmall
    simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hW] using h
  have hInv : 0 ≤ W⁻¹ := inv_nonneg.mpr hW.le
  have hMul : Real.sqrt s * W⁻¹ ≤ W * W⁻¹ :=
    mul_le_mul_of_nonneg_right hSqrt hInv
  have hCancel : W * W⁻¹ = (1 : ℝ) := mul_inv_cancel₀ (ne_of_gt hW)
  change 0 ≤ Real.sqrt s * W⁻¹ ∧ Real.sqrt s * W⁻¹ ≤ 1
  constructor
  · exact mul_nonneg (Real.sqrt_nonneg _) hInv
  · simpa only [hCancel] using hMul

/-- The frequency multiplier is continuous, hence measurable. -/
theorem continuous_h3AuditThreeHalvesFourierMultiplier :
    Continuous h3AuditThreeHalvesFourierMultiplier := by
  have hq : Continuous h3FourierGradientSquare := by
    unfold h3FourierGradientSquare
    fun_prop
  unfold h3AuditThreeHalvesFourierMultiplier
  exact
    (Real.continuous_sqrt.comp
      (Real.continuous_sqrt.comp (hq.pow 3))).mul
      continuous_h3SobolevFrequencyWeightInv

/-- Apply the bounded multiplier to a weighted H3 scalar Fourier state. -/
theorem h3Audit_threeHalvesMultiplier_memLp2
    (G : H3SpectralScalarState) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        (h3AuditThreeHalvesFourierMultiplier ξ : ℂ) * G ξ)
      2 (volume : Measure H3FourierPoint3) := by
  refine (MeasureTheory.Lp.memLp G).of_le_mul (c := 1) ?_ ?_
  · exact
      ((Complex.continuous_ofReal.comp
        continuous_h3AuditThreeHalvesFourierMultiplier).aestronglyMeasurable).mul
        (MeasureTheory.Lp.aestronglyMeasurable G)
  · filter_upwards with ξ
    have hC := h3Audit_threeHalvesMultiplier_mem_Icc ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hC.1]
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hC.2 (norm_nonneg (G ξ)))

noncomputable def h3AuditThreeHalvesMultiplierApply
    (G : H3SpectralScalarState) : H3FourierComplexL2 :=
  (h3Audit_threeHalvesMultiplier_memLp2 G).toLp
    (fun ξ : H3FourierPoint3 =>
      (h3AuditThreeHalvesFourierMultiplier ξ : ℂ) * G ξ)

/-- Almost-everywhere representative of the bounded Fourier multiplier. -/
theorem h3Audit_threeHalvesMultiplierApply_ae
    (G : H3SpectralScalarState) :
    (h3AuditThreeHalvesMultiplierApply G : H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (h3AuditThreeHalvesFourierMultiplier ξ : ℂ) * G ξ) := by
  exact MeasureTheory.MemLp.coeFn_toLp
    (h3Audit_threeHalvesMultiplier_memLp2 G)

/-- The new fractional multiplier is an L2 contraction. -/
theorem h3Audit_norm_threeHalvesMultiplierApply_le
    (G : H3SpectralScalarState) :
    ‖h3AuditThreeHalvesMultiplierApply G‖ ≤ ‖G‖ := by
  have hNorm :
      ‖h3AuditThreeHalvesMultiplierApply G‖ ≤ 1 * ‖G‖ := by
    apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [h3Audit_threeHalvesMultiplierApply_ae G]
      with ξ hξ
    rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (h3Audit_threeHalvesMultiplier_mem_Icc ξ).1]
    exact mul_le_mul_of_nonneg_right
      (h3Audit_threeHalvesMultiplier_mem_Icc ξ).2 (norm_nonneg _)
  simpa only [one_mul] using hNorm

/-- Additivity of the bounded Fourier multiplier. -/
theorem h3Audit_threeHalvesMultiplierApply_add
    (G H : H3SpectralScalarState) :
    h3AuditThreeHalvesMultiplierApply (G + H) =
      h3AuditThreeHalvesMultiplierApply G +
        h3AuditThreeHalvesMultiplierApply H := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3Audit_threeHalvesMultiplierApply_ae (G + H),
    h3Audit_threeHalvesMultiplierApply_ae G,
    h3Audit_threeHalvesMultiplierApply_ae H,
    MeasureTheory.Lp.coeFn_add G H,
    MeasureTheory.Lp.coeFn_add
      (h3AuditThreeHalvesMultiplierApply G)
      (h3AuditThreeHalvesMultiplierApply H)
  ] with ξ hGH hG hH hIn hOut
  rw [hGH, hOut]
  simp only [Pi.add_apply, hG, hH, hIn, mul_add]

/-- Complex-linearity of the bounded Fourier multiplier. -/
theorem h3Audit_threeHalvesMultiplierApply_smul
    (c : ℂ) (G : H3SpectralScalarState) :
    h3AuditThreeHalvesMultiplierApply (c • G) =
      c • h3AuditThreeHalvesMultiplierApply G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3Audit_threeHalvesMultiplierApply_ae (c • G),
    h3Audit_threeHalvesMultiplierApply_ae G,
    MeasureTheory.Lp.coeFn_smul c G,
    MeasureTheory.Lp.coeFn_smul c (h3AuditThreeHalvesMultiplierApply G)
  ] with ξ hCG hG hIn hOut
  rw [hCG, hOut]
  simp only [Pi.smul_apply, smul_eq_mul, hG, hIn]
  ring

/-- The genuine homogeneous three-halves multiplier is a continuous linear
operator on the exact native Fourier L2 Hilbert state. -/
noncomputable def h3AuditThreeHalvesMultiplierCLM :
    H3SpectralScalarState →L[ℂ] H3FourierComplexL2 :=
  (show H3SpectralScalarState →ₗ[ℂ] H3FourierComplexL2 from
    { toFun := h3AuditThreeHalvesMultiplierApply
      map_add' := h3Audit_threeHalvesMultiplierApply_add
      map_smul' := h3Audit_threeHalvesMultiplierApply_smul }).mkContinuous
      1 (fun G => by
        change ‖h3AuditThreeHalvesMultiplierApply G‖ ≤ 1 * ‖G‖
        simpa only [one_mul] using
          h3Audit_norm_threeHalvesMultiplierApply_le G)

@[simp]
theorem h3Audit_threeHalvesMultiplierCLM_apply
    (G : H3SpectralScalarState) :
    h3AuditThreeHalvesMultiplierCLM G =
      h3AuditThreeHalvesMultiplierApply G := rfl

/-- Native scalar homogeneous three-halves mass is EXACTLY the square norm of
our continuous linear Fourier multiplier. -/
theorem h3Audit_homogeneousThreeHalvesMass_eq_multiplierNormSq
    (G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
      h3AuditHomogeneousThreeHalvesFourierSquareDensity G ξ) =
    ‖h3AuditThreeHalvesMultiplierCLM G‖ ^ 2 := by
  rw [h3Audit_threeHalvesMultiplierCLM_apply,
    h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [h3Audit_threeHalvesMultiplierApply_ae G]
    with ξ hξ
  rw [hξ]
  let s : ℝ := Real.sqrt (h3FourierGradientSquare ξ ^ 3)
  let W : ℝ := h3SobolevFrequencyWeight ξ
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hW : 0 < W := h3SobolevFrequencyWeight_pos ξ
  have hRoot : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs
  have hCoeff : 0 ≤ h3AuditThreeHalvesFourierMultiplier ξ :=
    (h3Audit_threeHalvesMultiplier_mem_Icc ξ).1
  have hRaw :
      ‖h3SpectralScalarRawFourier G ξ‖ = W⁻¹ * ‖G ξ‖ := by
    unfold h3SpectralScalarRawFourier h3SobolevFrequencyWeightInvComplex
      h3SobolevFrequencyWeightInv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hW.le)]
  unfold h3AuditHomogeneousThreeHalvesFourierSquareDensity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hCoeff, hRaw]
  change s * (W⁻¹ * ‖G ξ‖) ^ 2 =
      (Real.sqrt s * W⁻¹ * ‖G ξ‖) ^ 2
  calc
    s * (W⁻¹ * ‖G ξ‖) ^ 2
        = (Real.sqrt s) ^ 2 * (W⁻¹ * ‖G ξ‖) ^ 2 := by
            rw [hRoot]
    _ = (Real.sqrt s * W⁻¹ * ‖G ξ‖) ^ 2 := by ring

/-- Therefore the exact homogeneous three-halves square energy is continuous
as a function of the weighted spectral H3 state. -/
theorem continuous_h3Audit_homogeneousThreeHalvesMass :
    Continuous (fun G : H3SpectralScalarState =>
      ∫ ξ : H3FourierPoint3,
        h3AuditHomogeneousThreeHalvesFourierSquareDensity G ξ) := by
  have hCont : Continuous (fun G : H3SpectralScalarState =>
      ‖h3AuditThreeHalvesMultiplierCLM G‖ ^ 2) :=
    (continuous_norm.comp h3AuditThreeHalvesMultiplierCLM.continuous).pow 2
  convert hCont using 1
  funext G
  exact h3Audit_homogeneousThreeHalvesMass_eq_multiplierNormSq G

/-- Canonical strict-time spectral component, extended by zero outside the
preterminal time interval. This makes its time measurability an ordinary
measurable-map statement without dependent proof arguments. -/
noncomputable def h3AuditComplementSpectralStateTotal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) : H3SpectralScalarState :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    h3TerminalComplementSpectralStateAt hH3 p t ht
  else 0

/-- The Fourier homogeneous time density is measurable whenever the actual
weighted H3 spectral-state path is measurable. Unlike the previous checkpoint,
NO measurability hypothesis on the scalar density is retained. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_measurable_of_state
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (hState : Measurable (h3AuditComplementSpectralStateTotal hH3 p)) :
    Measurable (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p) := by
  let F : H3SpectralScalarState → ℝ := fun G =>
    ∫ ξ : H3FourierPoint3,
      h3AuditHomogeneousThreeHalvesFourierSquareDensity G ξ
  have hF : Continuous F :=
    continuous_h3Audit_homogeneousThreeHalvesMass
  have hComp : Measurable (fun t : ℝ =>
      F (h3AuditComplementSpectralStateTotal hH3 p t)) :=
    hF.measurable.comp hState
  have hZero : F 0 = 0 := by
    dsimp only [F]
    rw [h3Audit_homogeneousThreeHalvesMass_eq_multiplierNormSq]
    change ‖h3AuditThreeHalvesMultiplierCLM (0 : H3SpectralScalarState)‖ ^ 2 = 0
    rw [map_zero]
    norm_num
  have hEq :
      h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p =
        (fun t : ℝ => F (h3AuditComplementSpectralStateTotal hH3 p t)) := by
    funext t
    by_cases ht : t ∈ Set.Ioo (0 : ℝ) T
    · simp only [h3AuditHomogeneousThreeHalvesVelocityTimeDensity,
        dif_pos ht, h3AuditComplementSpectralStateTotal, F]
    · simp only [h3AuditHomogeneousThreeHalvesVelocityTimeDensity,
        dif_neg ht, h3AuditComplementSpectralStateTotal, F]
      exact hZero.symm
  rw [hEq]
  exact hComp

/-- Both transverse homogeneous densities are now integrable on a common
terminal interval assuming only measurable canonical H3 spectral paths.
Temporal measurability of the densities is supplied by the preceding theorem. -/
theorem h3Audit_onePhysicalEndpoint_twoHomogeneousThreeHalves_integrable_of_stateMeasurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hPos : Measurable (h3AuditComplementSpectralStateTotal hH3
      (h3TerminalActualVorticityPositiveComplementPair i)))
    (hNeg : Measurable (h3AuditComplementSpectralStateTotal hH3
      (h3TerminalActualVorticityNegativeComplementPair i))) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      IntegrableOn
        (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3
          (h3TerminalActualVorticityPositiveComplementPair i)) (Set.Ioo c T) ∧
      IntegrableOn
        (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3
          (h3TerminalActualVorticityNegativeComplementPair i)) (Set.Ioo c T) := by
  exact
    h3Audit_onePhysicalEndpoint_twoHomogeneousThreeHalves_integrable_of_timeMeasurable
      hH3 hClass i hPhysical
      (h3Audit_homogeneousThreeHalvesTimeDensity_measurable_of_state
        hH3 _ hPos)
      (h3Audit_homogeneousThreeHalvesTimeDensity_measurable_of_state
        hH3 _ hNeg)

end
end Euclidean
end Bridge
end PrimeTensor

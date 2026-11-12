import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularYoungResidualTemporalContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSpectralDecodeDensity244
import Mathlib.Tactic

/-!
# Exact cubic-weighted annular Young residual on actual preterminal H³ paths

The preceding source proved strong Fourier-L² continuity of the true Leray
anti-heat residual, but only unweighted annular integrals. On a fixed
bounded-frequency ball, sqrt(q³) is a bounded Fourier multiplier of norm at
most sigma³. Construct the actual quotient-L² multiplier (not a pointwise
surrogate), establish its exact annular norm-square identity and then
identify the full nonlinear Young-gap plus radial-width functional.

For fixed finite rho <= sigma, continuity follows from the strongly continuous
actual weighted-H³ Fourier path, without an extra nonlinear-cost continuity
assumption. This is local in strictly positive time; no cutoff-uniform modulus,
terminal H³ continuation, or global regularity is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularYoungWidthTemporal244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularYoungWidthTemporal244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The exact homogeneous 3/2-order multiplier, truncated above at sigma.
Its SQUARE is q³ on the ball; it is zero off the ball. -/
noncomputable def thirdFullKineticFiniteCubicRootSymbol244
    (sigma : ℝ) (ξ : H3FourierPoint3) : ℝ := by
  classical
  exact if ξ ∈ h3TerminalRadialFrequencyBelow sigma then
    Real.sqrt (h3FourierGradientSquare ξ ^ 3)
  else 0

/-- Fixed finite bandwidth, not an H⁶ assumption, bounds the cubic-root
multiplier by sigma³. -/
theorem thirdFullKinetic_finiteCubicRootSymbol_mem_Icc244
    (sigma : ℝ) (hSigma : 0 ≤ sigma) (ξ : H3FourierPoint3) :
    thirdFullKineticFiniteCubicRootSymbol244 sigma ξ ∈
      Set.Icc (0 : ℝ) (sigma ^ 3) := by
  classical
  by_cases hIn : ξ ∈ h3TerminalRadialFrequencyBelow sigma
  · have hFreq : h3FourierGradientMagnitude ξ ≤ sigma := by
      change h3FourierGradientMagnitude ξ < sigma at hIn
      exact hIn.le
    have hQ : h3FourierGradientSquare ξ ≤ sigma ^ 2 := by
      rw [← h3FourierGradientMagnitude_sq]
      exact pow_le_pow_left₀ (h3FourierGradientMagnitude_nonneg ξ) hFreq 2
    have hQ3 : h3FourierGradientSquare ξ ^ 3 ≤ (sigma ^ 2) ^ 3 :=
      pow_le_pow_left₀ (h3FourierGradientSquare_nonneg ξ) hQ 3
    have hRoot : Real.sqrt ((sigma ^ 2) ^ 3) = sigma ^ 3 := by
      rw [show (sigma ^ 2) ^ 3 = (sigma ^ 3) ^ 2 from by ring]
      exact Real.sqrt_sq (pow_nonneg hSigma 3)
    rw [thirdFullKineticFiniteCubicRootSymbol244, if_pos hIn]
    exact ⟨Real.sqrt_nonneg _, by
      simpa only [hRoot] using Real.sqrt_le_sqrt hQ3⟩
  · rw [thirdFullKineticFiniteCubicRootSymbol244, if_neg hIn]
    exact ⟨le_refl _, pow_nonneg hSigma 3⟩

/-- The fixed-band scalar multiplier is measurable even though its
radial cutoff is sharp. -/
theorem thirdFullKinetic_finiteCubicRootSymbol_measurable244
    (sigma : ℝ) :
    Measurable (thirdFullKineticFiniteCubicRootSymbol244 sigma) := by
  classical
  have hQ : Measurable h3FourierGradientSquare := by
    unfold h3FourierGradientSquare
    measurability
  -- `Measurable.pow` expects a measurable exponent in this Mathlib version.
  -- For the fixed natural power, use two applications of multiplication.
  have hQ3 : Measurable (fun ξ : H3FourierPoint3 =>
      h3FourierGradientSquare ξ ^ 3) := by
    have hProd := hQ.mul (hQ.mul hQ)
    change Measurable (fun ξ : H3FourierPoint3 =>
      h3FourierGradientSquare ξ *
        (h3FourierGradientSquare ξ * h3FourierGradientSquare ξ)) at hProd
    have hEq :
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ *
            (h3FourierGradientSquare ξ * h3FourierGradientSquare ξ)) =
        (fun ξ : H3FourierPoint3 => h3FourierGradientSquare ξ ^ 3) := by
      funext ξ
      ring
    rw [hEq] at hProd
    exact hProd
  have hRoot : Measurable (fun ξ : H3FourierPoint3 =>
      Real.sqrt (h3FourierGradientSquare ξ ^ 3)) := by
    exact Real.continuous_sqrt.measurable.comp hQ3
  unfold thirdFullKineticFiniteCubicRootSymbol244
  exact Measurable.ite
    (measurableSet_h3TerminalRadialFrequencyBelow sigma)
    hRoot measurable_const

/-- Membership in Fourier L² of the actual finite-band q^(3/2) multiplier. -/
theorem thirdFullKinetic_finiteCubicRootMultiplier_memLp244
    (sigma : ℝ) (hSigma : 0 ≤ sigma) (F : H3FourierComplexL2) :
    MemLp (fun ξ : H3FourierPoint3 =>
      (thirdFullKineticFiniteCubicRootSymbol244 sigma ξ : ℂ) * F ξ)
      2 (volume : Measure H3FourierPoint3) := by
  have hMajor : MemLp
      (fun ξ : H3FourierPoint3 => ((sigma ^ 3 : ℝ) : ℂ) * F ξ)
      2 (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp F).const_mul _
  have hMeas : AEStronglyMeasurable
      (fun ξ : H3FourierPoint3 =>
        (thirdFullKineticFiniteCubicRootSymbol244 sigma ξ : ℂ) * F ξ)
      (volume : Measure H3FourierPoint3) :=
    ((Complex.continuous_ofReal.measurable.comp
       (thirdFullKinetic_finiteCubicRootSymbol_measurable244 sigma)).aestronglyMeasurable).mul
      (MeasureTheory.Lp.aestronglyMeasurable F)
  refine hMajor.of_le hMeas ?_
  filter_upwards with ξ
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (thirdFullKinetic_finiteCubicRootSymbol_mem_Icc244
      sigma hSigma ξ).1, abs_of_nonneg (pow_nonneg hSigma 3)]
  exact mul_le_mul_of_nonneg_right
    (thirdFullKinetic_finiteCubicRootSymbol_mem_Icc244 sigma hSigma ξ).2
    (norm_nonneg _)

/-- Genuine bounded multiplier on the *unweighted* complex Fourier L² state. -/
noncomputable def thirdFullKineticFiniteCubicRootMultiplierApply244
    (sigma : ℝ) (hSigma : 0 ≤ sigma) (F : H3FourierComplexL2) :
    H3FourierComplexL2 :=
  (thirdFullKinetic_finiteCubicRootMultiplier_memLp244 sigma hSigma F).toLp
    (fun ξ : H3FourierPoint3 =>
      (thirdFullKineticFiniteCubicRootSymbol244 sigma ξ : ℂ) * F ξ)

/-- This L² class has exactly the advertised Fourier multiplier a.e. -/
theorem thirdFullKinetic_finiteCubicRootMultiplier_ae244
    (sigma : ℝ) (hSigma : 0 ≤ sigma) (F : H3FourierComplexL2) :
    (thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma F :
      H3FourierPoint3 → ℂ) =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ => (thirdFullKineticFiniteCubicRootSymbol244 sigma ξ : ℂ) * F ξ) := by
  exact MeasureTheory.MemLp.coeFn_toLp
    (thirdFullKinetic_finiteCubicRootMultiplier_memLp244 sigma hSigma F)

/-- Exact frequency cost of the native Fourier L² multiplier. -/
theorem thirdFullKinetic_finiteCubicRootMultiplier_norm_le244
    (sigma : ℝ) (hSigma : 0 ≤ sigma) (F : H3FourierComplexL2) :
    ‖thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma F‖ ≤
      sigma ^ 3 * ‖F‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [thirdFullKinetic_finiteCubicRootMultiplier_ae244
    sigma hSigma F] with ξ hξ
  rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (thirdFullKinetic_finiteCubicRootSymbol_mem_Icc244
      sigma hSigma ξ).1]
  exact mul_le_mul_of_nonneg_right
    (thirdFullKinetic_finiteCubicRootSymbol_mem_Icc244 sigma hSigma ξ).2
    (norm_nonneg _)

/-- The genuine L² multiplier is additive. -/
theorem thirdFullKinetic_finiteCubicRootMultiplier_add244
    (sigma : ℝ) (hSigma : 0 ≤ sigma)
    (F G : H3FourierComplexL2) :
    thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma (F + G) =
      thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma F +
      thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    thirdFullKinetic_finiteCubicRootMultiplier_ae244 sigma hSigma (F + G),
    thirdFullKinetic_finiteCubicRootMultiplier_ae244 sigma hSigma F,
    thirdFullKinetic_finiteCubicRootMultiplier_ae244 sigma hSigma G,
    MeasureTheory.Lp.coeFn_add F G,
    MeasureTheory.Lp.coeFn_add
      (thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma F)
      (thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma G)
  ] with ξ hFG hF hG hIn hOut
  rw [hFG, hOut]
  simp only [Pi.add_apply, hF, hG, hIn, mul_add]

/-- Complex linearity of the actual bounded multiplier. -/
theorem thirdFullKinetic_finiteCubicRootMultiplier_smul244
    (sigma : ℝ) (hSigma : 0 ≤ sigma)
    (c : ℂ) (F : H3FourierComplexL2) :
    thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma (c • F) =
      c • thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma F := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    thirdFullKinetic_finiteCubicRootMultiplier_ae244 sigma hSigma (c • F),
    thirdFullKinetic_finiteCubicRootMultiplier_ae244 sigma hSigma F,
    MeasureTheory.Lp.coeFn_smul c F,
    MeasureTheory.Lp.coeFn_smul c
      (thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma F)
  ] with ξ hCF hF hIn hOut
  rw [hCF, hOut]
  simp only [Pi.smul_apply, smul_eq_mul, hF, hIn]
  ring

/-- The top-order annular Young weight is a fixed bounded complex-linear
operator on raw Fourier L², with norm at most sigma³. -/
noncomputable def thirdFullKineticFiniteCubicRootMultiplierCLM244
    (sigma : ℝ) (hSigma : 0 ≤ sigma) :
    H3FourierComplexL2 →L[ℂ] H3FourierComplexL2 :=
  (show H3FourierComplexL2 →ₗ[ℂ] H3FourierComplexL2 from
    { toFun := thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma
      map_add' := thirdFullKinetic_finiteCubicRootMultiplier_add244 sigma hSigma
      map_smul' := thirdFullKinetic_finiteCubicRootMultiplier_smul244 sigma hSigma }).mkContinuous
        (sigma ^ 3)
        (thirdFullKinetic_finiteCubicRootMultiplier_norm_le244 sigma hSigma)

@[simp]
theorem thirdFullKinetic_finiteCubicRootMultiplierCLM_apply244
    (sigma : ℝ) (hSigma : 0 ≤ sigma) (F : H3FourierComplexL2) :
    thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma F =
      thirdFullKineticFiniteCubicRootMultiplierApply244 sigma hSigma F := rfl

/-- Plancherel identity for the *q³-weighted* integral on the genuine sharp
annulus. Crucially, this is a theorem for every Fourier L² state F. -/
theorem thirdFullKinetic_sharpAnnulusCubicWeight_normSq244
    (rho sigma : ℝ) (hOrder : rho ≤ sigma) (hSigma : 0 ≤ sigma)
    (F : H3FourierComplexL2) :
    ‖thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma
        (h3CriticalFourierSharpLowCutoffCLM sigma F -
          h3CriticalFourierSharpLowCutoffCLM rho F)‖ ^ 2 =
      ∫ ξ in ((h3TerminalRadialFrequencyBelow rho)ᶜ ∩
          h3TerminalRadialFrequencyBelow sigma),
        h3FourierGradientSquare ξ ^ 3 * ‖(F : H3FourierPoint3 → ℂ) ξ‖ ^ 2
          ∂volume := by
  classical
  let S : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow rho)ᶜ ∩
      h3TerminalRadialFrequencyBelow sigma
  have hS : MeasurableSet S :=
    (measurableSet_h3TerminalRadialFrequencyBelow rho).compl.inter
      (measurableSet_h3TerminalRadialFrequencyBelow sigma)
  rw [thirdFullKinetic_finiteCubicRootMultiplierCLM_apply244,
    h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [
    thirdFullKinetic_finiteCubicRootMultiplier_ae244 sigma hSigma
      (h3CriticalFourierSharpLowCutoffCLM sigma F -
        h3CriticalFourierSharpLowCutoffCLM rho F),
    thirdFullKinetic_sharpFourierAnnulusCutoff_ae244 rho sigma hOrder F
  ] with ξ hMult hBand
  rw [hMult, hBand]
  by_cases hIn : ξ ∈ S
  · have hUpper : ξ ∈ h3TerminalRadialFrequencyBelow sigma := hIn.2
    rw [Set.indicator_of_mem hIn, Set.indicator_of_mem hIn]
    rw [thirdFullKineticFiniteCubicRootSymbol244, if_pos hUpper]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (pow_nonneg (h3FourierGradientSquare_nonneg ξ) 3)]
  · rw [Set.indicator_of_notMem hIn, Set.indicator_of_notMem hIn]
    simp

/-- The previous genuine Leray/Laplacian a.e. representative upgrades the
cubic multiplier identity to the EXACT actual Young-gap integrand. -/
theorem thirdFullPhysical_annularYoungResidualWeightedIntegral_eq_normSq244
    (rho sigma : ℝ) (hOrder : rho ≤ sigma) (hSigma : 0 ≤ sigma)
    (U : H3SpectralVelocityState) (j : Fin 3) :
    (∫ ξ in ((h3TerminalRadialFrequencyBelow rho)ᶜ ∩
        h3TerminalRadialFrequencyBelow sigma),
      h3FourierGradientSquare ξ ^ 3 *
      ‖h3RawFinLerayOuterProductDivergence U U j ξ +
        2 * ((h3FourierGradientSquare ξ : ℂ) *
          h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2 ∂volume) =
    ‖thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma
      (thirdFullPhysicalAnnularYoungResidualBandFourierL2244 rho sigma U j)‖ ^ 2 := by
  let S : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow rho)ᶜ ∩
      h3TerminalRadialFrequencyBelow sigma
  let F : H3FourierComplexL2 :=
    thirdFullPhysicalAnnularYoungResidualFourierL2244 U j
  have hAE :
      (∫ ξ in S, h3FourierGradientSquare ξ ^ 3 *
        ‖(F : H3FourierPoint3 → ℂ) ξ‖ ^ 2 ∂volume) =
      (∫ ξ in S, h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence U U j ξ +
          2 * ((h3FourierGradientSquare ξ : ℂ) *
            h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2 ∂volume) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (s := S)
      (thirdFullPhysical_annularYoungResidualFourier_ae244 U j)] with ξ hξ
    rw [hξ]
  have hWeighted := thirdFullKinetic_sharpAnnulusCubicWeight_normSq244
    rho sigma hOrder hSigma F
  change ‖thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma
    (thirdFullPhysicalAnnularYoungResidualBandFourierL2244 rho sigma U j)‖ ^ 2 =
    ∫ ξ in S, h3FourierGradientSquare ξ ^ 3 *
      ‖(F : H3FourierPoint3 → ℂ) ξ‖ ^ 2 ∂volume at hWeighted
  exact hAE.symm.trans hWeighted.symm

/-- The native H³-continuous operator realization of the exact finite-band
Young-gap plus velocity-width functional. -/
noncomputable def thirdFullPhysicalAnnularYoungWidthHilbertCost244
    (rho sigma : ℝ) (hSigma : 0 ≤ sigma)
    (U : H3SpectralVelocityState) : ℝ :=
  2 * (∑ j : Fin 3,
    ‖thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma
      (thirdFullPhysicalAnnularYoungResidualBandFourierL2244 rho sigma U j)‖ ^ 2) +
  (2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2) *
    (∑ j : Fin 3,
      ‖h3CriticalFourierSharpLowCutoffCLM sigma
          (h3SpectralScalarRawFourierL2 (U j)) -
        h3CriticalFourierSharpLowCutoffCLM rho
          (h3SpectralScalarRawFourierL2 (U j))‖ ^ 2)

/-- Fixed finite-band Young-gap plus width depends continuously on the
native weighted H³ spectral state. -/
theorem thirdFullPhysical_annularYoungWidthHilbertCost_continuous244
    (rho sigma : ℝ) (hSigma : 0 ≤ sigma) :
    Continuous (thirdFullPhysicalAnnularYoungWidthHilbertCost244 rho sigma hSigma) := by
  have hYoung : Continuous (fun U : H3SpectralVelocityState =>
      ∑ j : Fin 3,
        ‖thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma
          (thirdFullPhysicalAnnularYoungResidualBandFourierL2244 rho sigma U j)‖ ^ 2) := by
    apply continuous_finsetSum Finset.univ
    intro j _
    exact (continuous_norm.comp
      ((thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma).continuous.comp
        (thirdFullPhysical_annularYoungResidualBand_continuous244 rho sigma j))).pow 2
  have hWidth : Continuous (fun U : H3SpectralVelocityState =>
      ∑ j : Fin 3,
        ‖h3CriticalFourierSharpLowCutoffCLM sigma
            (h3SpectralScalarRawFourierL2 (U j)) -
          h3CriticalFourierSharpLowCutoffCLM rho
            (h3SpectralScalarRawFourierL2 (U j))‖ ^ 2) := by
    apply continuous_finsetSum Finset.univ
    intro j _
    have hRaw : Continuous (fun U : H3SpectralVelocityState =>
        h3SpectralScalarRawFourierL2 (U j)) :=
      continuous_h3SpectralScalarRawFourierL2_244.comp (continuous_apply j)
    exact (continuous_norm.comp
      (((h3CriticalFourierSharpLowCutoffCLM sigma).continuous.comp hRaw).sub
       ((h3CriticalFourierSharpLowCutoffCLM rho).continuous.comp hRaw))).pow 2
  change Continuous (fun U : H3SpectralVelocityState =>
    2 * (∑ j : Fin 3,
      ‖thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma
        (thirdFullPhysicalAnnularYoungResidualBandFourierL2244 rho sigma U j)‖ ^ 2) +
    (2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2) *
      (∑ j : Fin 3,
        ‖h3CriticalFourierSharpLowCutoffCLM sigma
            (h3SpectralScalarRawFourierL2 (U j)) -
          h3CriticalFourierSharpLowCutoffCLM rho
            (h3SpectralScalarRawFourierL2 (U j))‖ ^ 2))
  exact (continuous_const.mul hYoung).add (continuous_const.mul hWidth)

/-- There is no substitute nonlinear functional: the Hilbert norm-square
formula is IDENTICAL to the previously defined actual q³ Young-gap and width
integrals, with their original factors. -/
theorem thirdFullPhysical_actualYoungWidthCost_eq_hilbert244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t rho sigma : ℝ) (hOrder : rho ≤ sigma) (hSigma : 0 ≤ sigma) :
    thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma =
      thirdFullPhysicalAnnularYoungWidthHilbertCost244 rho sigma hSigma
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let S : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow rho)ᶜ ∩
      h3TerminalRadialFrequencyBelow sigma
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let K : ℝ := 2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2
  have hGap :
      (∑ j : Fin 3, ∫ ξ in S,
        h3FourierGradientSquare ξ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U U j ξ +
            2 * ((h3FourierGradientSquare ξ : ℂ) *
              h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2 ∂volume) =
      (∑ j : Fin 3,
        ‖thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma
          (thirdFullPhysicalAnnularYoungResidualBandFourierL2244 rho sigma U j)‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro j _
    exact thirdFullPhysical_annularYoungResidualWeightedIntegral_eq_normSq244
      rho sigma hOrder hSigma U j
  have hMass :
      (∑ j : Fin 3, ∫ ξ in S,
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume) =
      (∑ j : Fin 3,
        ‖h3CriticalFourierSharpLowCutoffCLM sigma
            (h3SpectralScalarRawFourierL2 (U j)) -
          h3CriticalFourierSharpLowCutoffCLM rho
            (h3SpectralScalarRawFourierL2 (U j))‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro j _
    exact (thirdFullKinetic_sharpFourierAnnulusCutoff_norm_sq_eq_integral244
      rho sigma hOrder (h3SpectralScalarRawFourierL2 (U j))).symm
  change 2 * (∑ j : Fin 3, ∫ ξ in S,
        h3FourierGradientSquare ξ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U U j ξ +
            2 * ((h3FourierGradientSquare ξ : ℂ) *
              h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2 ∂volume) +
      K * (∑ j : Fin 3, ∫ ξ in S,
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume) =
    2 * (∑ j : Fin 3,
        ‖thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma
          (thirdFullPhysicalAnnularYoungResidualBandFourierL2244 rho sigma U j)‖ ^ 2) +
      K * (∑ j : Fin 3,
        ‖h3CriticalFourierSharpLowCutoffCLM sigma
            (h3SpectralScalarRawFourierL2 (U j)) -
          h3CriticalFourierSharpLowCutoffCLM rho
            (h3SpectralScalarRawFourierL2 (U j))‖ ^ 2)
  rw [hGap, hMass]

/-- The original, genuine physical nonlinear Young/width cost is continuous
at every strictly positive time, unconditionally for each fixed annulus. -/
theorem thirdFullPhysical_actualAnnularYoungWidthCost_continuousAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (rho sigma t : ℝ) (hOrder : rho ≤ sigma) (hSigma : 0 ≤ sigma)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousAt
      (fun s : ℝ => thirdFullPhysicalActualAnnularYoungWidthCost244
        hH3 s rho sigma) t := by
  have hSpectral : ContinuousAt
      (h3AuditActualSpectralVelocityTotal hH3) t :=
    h3Audit_initialActualSpectralVelocity_continuousAt hH3 ht
  have hCont :=
    (thirdFullPhysical_annularYoungWidthHilbertCost_continuous244
      rho sigma hSigma).continuousAt.comp hSpectral
  have hEq :
      (fun s : ℝ => thirdFullPhysicalActualAnnularYoungWidthCost244
        hH3 s rho sigma) =
      (fun s : ℝ => thirdFullPhysicalAnnularYoungWidthHilbertCost244
        rho sigma hSigma (h3AuditActualSpectralVelocityTotal hH3 s)) := by
    funext s
    exact thirdFullPhysical_actualYoungWidthCost_eq_hilbert244
      hH3 s rho sigma hOrder hSigma
  rw [hEq]
  exact hCont

/-- Remove the formerly assumed nonlinear time-continuity premise from the
exact physical annular kinetic deficit, using only actual H³ path data. -/
theorem thirdFullPhysical_actualAnnularKineticDeficit_continuousAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b rho sigma t : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousAt
      (fun s : ℝ => thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b s rho sigma) t := by
  exact thirdFullPhysical_actualAnnularKineticDeficit_continuousAt_of_young244
    hH3 b rho sigma t ht
    (thirdFullPhysical_actualAnnularYoungWidthCost_continuousAt244
      hH3 rho sigma t hOrder (hRho.trans hOrder) ht)

/-- A single strict actual physical annular deficit now produces its positive
viscous window WITHOUT any nonlinear Young-continuity assumption. -/
theorem thirdFullPhysical_annularDeficit_snapshotRightWindowCharge_auto244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (epsilon : ℝ) (hEps : 0 < epsilon)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) <
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      (∀ s : ℝ, s ∈ Set.Icc x (x + delta) →
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
        epsilon ≤
          thirdFullPhysicalActualAnnularKineticDeficit244
            hH3 b s rho sigma) ∧
      delta * (epsilon /
        thirdFullPhysicalAnnularCapClockFactor244 u b rho epsilon) ≤
        ∫ r in a..T, velocityH3DissipationAt u r := by
  have hxAbs : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hx.1), hx.2⟩
  exact thirdFullPhysical_annularDeficit_snapshotRightWindowCharge244
    hH3 hClass hDInt b hb rho sigma hRho hOrder x hx epsilon hEps
    (thirdFullPhysical_actualAnnularYoungWidthCost_continuousAt244
      hH3 rho sigma x hOrder (hRho.trans hOrder) hxAbs)
    hExcess hPeak

end
end PrimeTensor.FirstMonomialTriad

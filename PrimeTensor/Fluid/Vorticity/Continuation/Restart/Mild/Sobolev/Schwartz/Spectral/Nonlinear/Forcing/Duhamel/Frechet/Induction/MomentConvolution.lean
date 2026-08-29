import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentAlgebra

/-!
# Fréchet endpoint induction: generic convolution moments

This file replaces the named convolution-moment checkpoints by one theorem
valid for every nonnegative real exponent `q`.

Writing

    m_q(F) = ∫ w_q(ξ) |F̂(ξ)| dξ,
    w_q(ξ) = ‖ξ‖^q,

the generic frequency split from `MomentAlgebra`

    w_q(ξ)
      ≤
    2^q (w_q(η) + w_q(ξ - η))

gives the Young estimate

    m_q(F * G)
      ≤
    2^q (m_q(F)m_0(G) + m_0(F)m_q(G)).

This is the nonlinear convolution input needed by every later induction level.
No named exponent appears in the proof.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentConvolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Left generic-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionMomentLeftMajorant
    (q : ℝ)
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    (h3FourierMomentWeight q η *
        ‖h3SpectralScalarRawFourier F η‖) *
      ‖h3SpectralScalarRawFourier G (ξ - η)‖

/-- Right generic-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionMomentRightMajorant
    (q : ℝ)
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier F η‖ *
      (h3FourierMomentWeight q (ξ - η) *
        ‖h3SpectralScalarRawFourier G (ξ - η)‖)

/-- Complete generic-moment Young majorant. -/
noncomputable def h3RawProductConvolutionMomentMajorant
    (q : ℝ)
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  h3FourierMomentSplitCoefficient q *
    (h3RawProductConvolutionMomentLeftMajorant q F G ξ +
      h3RawProductConvolutionMomentRightMajorant q F G ξ)

/-- Actual generic weighted `L¹` mass of the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionMomentMass
    (q : ℝ)
    (F G : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierMomentWeight q ξ *
      ‖h3RawProductConvolution F G ξ‖

/-- The left generic Young majorant is integrable whenever the first input has
an integrable `q` moment. -/
theorem h3RawProductConvolutionMomentLeftMajorant_integrable
    {q : ℝ}
    (F G : H3SpectralScalarState)
    (hFq : H3RawFourierMomentIntegrable q F) :
    Integrable
      (h3RawProductConvolutionMomentLeftMajorant q F G)
      (volume : Measure H3FourierPoint3) := by
  have hG0 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hFq' :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierMomentWeight q η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3) := by
    exact hFq

  have hConv :=
    hFq'.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hG0

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          (h3FourierMomentWeight q η *
              ‖h3SpectralScalarRawFourier F η‖) *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖)
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The right generic Young majorant is integrable whenever the second input
has an integrable `q` moment. -/
theorem h3RawProductConvolutionMomentRightMajorant_integrable
    {q : ℝ}
    (F G : H3SpectralScalarState)
    (hGq : H3RawFourierMomentIntegrable q G) :
    Integrable
      (h3RawProductConvolutionMomentRightMajorant q F G)
      (volume : Measure H3FourierPoint3) := by
  have hF0 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 F)).norm

  have hGq' :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierMomentWeight q ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3) := by
    exact hGq

  have hConv :=
    hF0.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hGq'

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η‖ *
            (h3FourierMomentWeight q (ξ - η) *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖))
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The complete generic convolution majorant is integrable. -/
theorem h3RawProductConvolutionMomentMajorant_integrable
    {q : ℝ}
    (F G : H3SpectralScalarState)
    (hFq : H3RawFourierMomentIntegrable q F)
    (hGq : H3RawFourierMomentIntegrable q G) :
    Integrable
      (h3RawProductConvolutionMomentMajorant q F G)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawProductConvolutionMomentMajorant
  exact
    ((h3RawProductConvolutionMomentLeftMajorant_integrable
        F G hFq).add
      (h3RawProductConvolutionMomentRightMajorant_integrable
        F G hGq)).const_mul
          (h3FourierMomentSplitCoefficient q)

/-- The generic convolution majorant is pointwise nonnegative. -/
theorem h3RawProductConvolutionMomentMajorant_nonneg
    (q : ℝ)
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    0 ≤ h3RawProductConvolutionMomentMajorant q F G ξ := by
  have hLeft :
      0 ≤ h3RawProductConvolutionMomentLeftMajorant q F G ξ := by
    unfold h3RawProductConvolutionMomentLeftMajorant
    exact
      integral_nonneg fun η =>
        mul_nonneg
          (mul_nonneg
            (h3FourierMomentWeight_nonneg q η)
            (norm_nonneg _))
          (norm_nonneg _)

  have hRight :
      0 ≤ h3RawProductConvolutionMomentRightMajorant q F G ξ := by
    unfold h3RawProductConvolutionMomentRightMajorant
    exact
      integral_nonneg fun η =>
        mul_nonneg
          (norm_nonneg _)
          (mul_nonneg
            (h3FourierMomentWeight_nonneg q (ξ - η))
            (norm_nonneg _))

  unfold h3RawProductConvolutionMomentMajorant
  exact
    mul_nonneg
      (h3FourierMomentSplitCoefficient_nonneg q)
      (add_nonneg hLeft hRight)

/-- Exact total mass of the left generic Young majorant. -/
theorem h3RawProductConvolutionMomentLeftMajorant_integral_eq
    {q : ℝ}
    (F G : H3SpectralScalarState)
    (hFq : H3RawFourierMomentIntegrable q F) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionMomentLeftMajorant q F G ξ)
      =
    h3SpectralScalarRawFourierMomentMass q F *
      h3SpectralScalarRawFourierL1Mass G := by
  let fq : H3FourierPoint3 → ℝ :=
    fun η =>
      h3FourierMomentWeight q η *
        ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖h3SpectralScalarRawFourier G ζ‖

  have hFq' :
      Integrable fq (volume : Measure H3FourierPoint3) := by
    dsimp only [fq]
    exact hFq

  have hG0 :
      Integrable g0 (volume : Measure H3FourierPoint3) := by
    dsimp only [g0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hConv :=
    MeasureTheory.integral_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hFq'
      hG0

  unfold h3RawProductConvolutionMomentLeftMajorant
  unfold h3SpectralScalarRawFourierMomentMass
  unfold h3SpectralScalarRawFourierL1Mass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        fq η * g0 (ξ - η))
      =
    (∫ η : H3FourierPoint3, fq η) *
      ∫ ζ : H3FourierPoint3, g0 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        fq η * g0 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          fq g0 (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure H3FourierPoint3) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      symm
      exact
        MeasureTheory.convolution_mul
          (𝕜 := ℝ)
          (G := H3FourierPoint3)
          (μ := (volume : Measure H3FourierPoint3))
          (f := fq)
          (g := g0)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, fq η) *
        ∫ ζ : H3FourierPoint3, g0 ζ := by
      exact hConv

/-- Exact total mass of the right generic Young majorant. -/
theorem h3RawProductConvolutionMomentRightMajorant_integral_eq
    {q : ℝ}
    (F G : H3SpectralScalarState)
    (hGq : H3RawFourierMomentIntegrable q G) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionMomentRightMajorant q F G ξ)
      =
    h3SpectralScalarRawFourierL1Mass F *
      h3SpectralScalarRawFourierMomentMass q G := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖h3SpectralScalarRawFourier F η‖

  let gq : H3FourierPoint3 → ℝ :=
    fun ζ =>
      h3FourierMomentWeight q ζ *
        ‖h3SpectralScalarRawFourier G ζ‖

  have hF0 :
      Integrable f0 (volume : Measure H3FourierPoint3) := by
    dsimp only [f0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 F)).norm

  have hGq' :
      Integrable gq (volume : Measure H3FourierPoint3) := by
    dsimp only [gq]
    exact hGq

  have hConv :=
    MeasureTheory.integral_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hF0
      hGq'

  unfold h3RawProductConvolutionMomentRightMajorant
  unfold h3SpectralScalarRawFourierL1Mass
  unfold h3SpectralScalarRawFourierMomentMass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * gq (ξ - η))
      =
    (∫ η : H3FourierPoint3, f0 η) *
      ∫ ζ : H3FourierPoint3, gq ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * gq (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f0 gq (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure H3FourierPoint3) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      symm
      exact
        MeasureTheory.convolution_mul
          (𝕜 := ℝ)
          (G := H3FourierPoint3)
          (μ := (volume : Measure H3FourierPoint3))
          (f := f0)
          (g := gq)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f0 η) *
        ∫ ζ : H3FourierPoint3, gq ζ := by
      exact hConv

/-- Exact total mass of the complete generic convolution majorant. -/
theorem h3RawProductConvolutionMomentMajorant_integral_eq
    {q : ℝ}
    (F G : H3SpectralScalarState)
    (hFq : H3RawFourierMomentIntegrable q F)
    (hGq : H3RawFourierMomentIntegrable q G) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionMomentMajorant q F G ξ)
      =
    h3FourierMomentSplitCoefficient q *
      (h3SpectralScalarRawFourierMomentMass q F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierMomentMass q G) := by
  have hLeftInt :=
    h3RawProductConvolutionMomentLeftMajorant_integrable
      F G hFq

  have hRightInt :=
    h3RawProductConvolutionMomentRightMajorant_integrable
      F G hGq

  unfold h3RawProductConvolutionMomentMajorant

  rw [integral_const_mul]
  rw [integral_add hLeftInt hRightInt]
  rw [
    h3RawProductConvolutionMomentLeftMajorant_integral_eq
      F G hFq,
    h3RawProductConvolutionMomentRightMajorant_integral_eq
      F G hGq
  ]

/-- The exact raw convolution is dominated almost everywhere by the generic
Young majorant. -/
theorem h3RawProductConvolution_moment_le_majorant_ae
    {q : ℝ}
    (hq : 0 ≤ q)
    (F G : H3SpectralScalarState)
    (hFq : H3RawFourierMomentIntegrable q F)
    (hGq : H3RawFourierMomentIntegrable q G) :
    ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
      h3FourierMomentWeight q ξ *
          ‖h3RawProductConvolution F G ξ‖
        ≤
      h3RawProductConvolutionMomentMajorant q F G ξ := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let fq : H3FourierPoint3 → ℝ :=
    fun η =>
      h3FourierMomentWeight q η *
        ‖h3SpectralScalarRawFourier F η‖

  let gq : H3FourierPoint3 → ℝ :=
    fun ζ =>
      h3FourierMomentWeight q ζ *
        ‖h3SpectralScalarRawFourier G ζ‖

  have hF0 :
      Integrable f0
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 F)).norm

  have hG0 :
      Integrable g0
        (volume : Measure H3FourierPoint3) := by
    dsimp only [g0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hFq' :
      Integrable fq
        (volume : Measure H3FourierPoint3) := by
    dsimp only [fq]
    exact hFq

  have hGq' :
      Integrable gq
        (volume : Measure H3FourierPoint3) := by
    dsimp only [gq]
    exact hGq

  have hLeftProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          fq p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hFq'.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      fq, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * gq (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hGq'
    simpa only [
      f0, gq,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            fq η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * gq (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw :
      0 ≤ h3FourierMomentWeight q ξ :=
    h3FourierMomentWeight_nonneg q ξ

  have hRawKernel :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η))
        (volume : Measure H3FourierPoint3) :=
    h3RawProductKernel_integrable F G ξ

  have hRawWeighted :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul (h3FourierMomentWeight q ξ)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierMomentSplitCoefficient q *
            (fq η * g0 (ξ - η) +
              f0 η * gq (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul
      (h3FourierMomentSplitCoefficient q)

  have hPointwise :
      ∀ η : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        h3FourierMomentSplitCoefficient q *
          (fq η * g0 (ξ - η) +
            f0 η * gq (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierMomentWeight_le_split hq ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      h3FourierMomentWeight q ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        h3FourierMomentWeight q ξ *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
        rw [norm_mul]
      _ ≤
        (h3FourierMomentSplitCoefficient q *
          (h3FourierMomentWeight q η +
            h3FourierMomentWeight q (ξ - η))) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right
          hFreq hProdNonneg
      _ =
        h3FourierMomentSplitCoefficient q *
          (fq η * g0 (ξ - η) +
            f0 η * gq (ξ - η)) := by
        dsimp only [f0, g0, fq, gq]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        h3FourierMomentSplitCoefficient q *
          (fq η * g0 (ξ - η) +
            f0 η * gq (ξ - η)) :=
    integral_mono
      hRawWeighted hInnerMajor hPointwise

  have hNormIntegral :
      ‖h3RawProductConvolution F G ξ‖
        ≤
      ∫ η : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η)‖ := by
    change
      ‖∫ η : H3FourierPoint3,
          h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
        ≤
      ∫ η : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η)‖
    exact norm_integral_le_integral_norm _

  calc
    h3FourierMomentWeight q ξ *
        ‖h3RawProductConvolution F G ξ‖
        ≤
      h3FourierMomentWeight q ξ *
        (∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖) :=
      mul_le_mul_of_nonneg_left
        hNormIntegral hw
    _ =
      ∫ η : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖ := by
      rw [integral_const_mul]
    _ ≤
      ∫ η : H3FourierPoint3,
        h3FourierMomentSplitCoefficient q *
          (fq η * g0 (ξ - η) +
            f0 η * gq (ξ - η)) :=
      hIntegralLe
    _ =
      h3RawProductConvolutionMomentMajorant q F G ξ := by
      unfold h3RawProductConvolutionMomentMajorant
      unfold h3RawProductConvolutionMomentLeftMajorant
      unfold h3RawProductConvolutionMomentRightMajorant
      dsimp only [f0, g0, fq, gq]
      rw [← integral_add hLeftξ hRightξ]
      rw [← integral_const_mul]

/-- The exact raw product convolution inherits an integrable generic `q`
moment from generic `q` moments on both inputs. -/
theorem h3RawProductConvolution_moment_integrable_of
    {q : ℝ}
    (hq : 0 ≤ q)
    (F G : H3SpectralScalarState)
    (hFq : H3RawFourierMomentIntegrable q F)
    (hGq : H3RawFourierMomentIntegrable q G) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight q ξ *
          ‖h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hMajor :=
    h3RawProductConvolutionMomentMajorant_integrable
      F G hFq hGq

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight hq).aestronglyMeasurable.mul
      (h3RawProductConvolution_integrable F G).aestronglyMeasurable.norm

  have hDom :=
    h3RawProductConvolution_moment_le_majorant_ae
      hq F G hFq hGq

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards [hDom] with ξ hξ

  have hTarget0 :
      0 ≤
        h3FourierMomentWeight q ξ *
          ‖h3RawProductConvolution F G ξ‖ :=
    mul_nonneg
      (h3FourierMomentWeight_nonneg q ξ)
      (norm_nonneg _)

  have hMajor0 :
      0 ≤
        h3RawProductConvolutionMomentMajorant q F G ξ :=
    h3RawProductConvolutionMomentMajorant_nonneg q F G ξ

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTarget0,
    abs_of_nonneg hMajor0
  ] using hξ

/-- Generic Young inequality for the exact raw product convolution. -/
theorem h3RawProductConvolutionMomentMass_le
    {q : ℝ}
    (hq : 0 ≤ q)
    (F G : H3SpectralScalarState)
    (hFq : H3RawFourierMomentIntegrable q F)
    (hGq : H3RawFourierMomentIntegrable q G) :
    h3RawProductConvolutionMomentMass q F G
      ≤
    h3FourierMomentSplitCoefficient q *
      (h3SpectralScalarRawFourierMomentMass q F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierMomentMass q G) := by
  have hTarget :=
    h3RawProductConvolution_moment_integrable_of
      hq F G hFq hGq

  have hMajor :=
    h3RawProductConvolutionMomentMajorant_integrable
      F G hFq hGq

  have hDom :=
    h3RawProductConvolution_moment_le_majorant_ae
      hq F G hFq hGq

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawProductConvolutionMomentMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionMomentMajorant q F G ξ :=
      hIntegral
    _ =
      h3FourierMomentSplitCoefficient q *
        (h3SpectralScalarRawFourierMomentMass q F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierMomentMass q G) :=
      h3RawProductConvolutionMomentMajorant_integral_eq
        F G hFq hGq

end
end Euclidean
end Bridge
end PrimeTensor

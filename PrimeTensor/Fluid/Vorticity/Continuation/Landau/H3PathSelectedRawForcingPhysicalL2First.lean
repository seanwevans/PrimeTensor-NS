import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedRawForcingPhysicalL2Zero
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedRawForcingRadialL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.Selected.Forcing.First
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Transport
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# First physical L² derivative of the selected raw forcing

The unprojected selected forcing now has public radial Fourier `L²` control.
At weight one this controls every coordinate multiplier

    d_a(ξ) div(W ⊗ W)_i(ξ)

in Fourier `L²`.  The already-proved first raw Fourier moment supplies the
`L¹` input needed to differentiate the ordinary inverse-Fourier integral.

This file packages the generic first-coordinate inverse-Fourier derivative on
`Point3`, transports the multiplier through Plancherel, and concludes that
every first spatial derivative of the real selected raw forcing belongs to
physical `L²`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform LineDeriv Topology

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedRawForcingPhysicalL2First
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedRawForcingPhysicalL2First :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic physical Plancherel helpers -/

private theorem memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedRawFirst
    {f : H3FourierPoint3 → ℂ}
    (hf1 : Integrable f (volume : Measure H3FourierPoint3))
    (hf2 : MemLp f 2 (volume : Measure H3FourierPoint3)) :
    MemLp
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
      2
      (volume : Measure Point3) := by

  let f2 : H3FourierComplexL2 := hf2.toLp f
  let u2 : H3FourierComplexL2 :=
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm f2
  let p2 : MeasureTheory.Lp ℂ 2 (volume : Measure Point3) :=
    MeasureTheory.Lp.compMeasurePreserving
      (WithLp.toLp 2 : Point3 → H3FourierPoint3)
      (PiLp.volume_preserving_toLp (PrimeTensor.Axis Depth.three))
      u2

  have hCompat :
      FourierTransformInv.fourierInv f
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ) := by
    dsimp only [u2, f2]
    exact h3FourierInv_integrable_memLp2_ae_eq_L2 hf1 hf2

  have hComp :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hCompat

  have hFrom :
      ((p2 : MeasureTheory.Lp ℂ 2 (volume : Measure Point3)) : Point3 → ℂ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    dsimp only [p2]
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        u2
        (PiLp.volume_preserving_toLp (PrimeTensor.Axis Depth.three))

  have hAE :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      ((p2 : MeasureTheory.Lp ℂ 2 (volume : Measure Point3)) : Point3 → ℂ) :=
    hComp.trans hFrom.symm

  exact
    (memLp_congr_ae hAE).2
      (MeasureTheory.Lp.memLp p2)

private theorem memLp_re_of_memLp_complex_h3SelectedRawFirst
    {f : Point3 → ℂ}
    (hf : MemLp f 2 (volume : Measure Point3)) :
    MemLp
      (fun x : Point3 => (f x).re)
      2
      (volume : Measure Point3) := by

  let F : MeasureTheory.Lp ℂ 2 (volume : Measure Point3) := hf.toLp f
  let R : MeasureTheory.Lp ℝ 2 (volume : Measure Point3) :=
    Complex.reCLM.compLp F

  have hF :
      ((F : MeasureTheory.Lp ℂ 2 (volume : Measure Point3)) : Point3 → ℂ)
        =ᵐ[(volume : Measure Point3)] f := by
    dsimp only [F]
    exact MeasureTheory.MemLp.coeFn_toLp hf

  have hR :
      ((R : MeasureTheory.Lp ℝ 2 (volume : Measure Point3)) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (((F : MeasureTheory.Lp ℂ 2 (volume : Measure Point3)) : Point3 → ℂ) x).re) := by
    dsimp only [R]
    exact Complex.reCLM.coeFn_compLp F

  have hAE :
      (fun x : Point3 => (f x).re)
        =ᵐ[(volume : Measure Point3)]
      ((R : MeasureTheory.Lp ℝ 2 (volume : Measure Point3)) : Point3 → ℝ) := by
    filter_upwards [hF, hR] with x hxF hxR
    calc
      (f x).re
          =
        (((F : MeasureTheory.Lp ℂ 2 (volume : Measure Point3)) : Point3 → ℂ) x).re :=
        congrArg Complex.re hxF.symm
      _ =
        ((R : MeasureTheory.Lp ℝ 2 (volume : Measure Point3)) : Point3 → ℝ) x :=
        hxR.symm

  exact
    (memLp_congr_ae hAE).2
      (MeasureTheory.Lp.memLp R)

/-! ## Generic first derivative of an inverse Fourier integral -/

private theorem fourierInv_hasLineDerivAt_coordinate_of_integrable_firstMoment
    {f : H3FourierPoint3 → ℂ}
    (hf : Integrable f (volume : Measure H3FourierPoint3))
    (hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3))
    (i : Fin 3)
    (x : H3FourierPoint3) :
    HasLineDerivAt ℝ
      (FourierTransformInv.fourierInv f)
      (FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol i ξ * f ξ)
        x)
      x
      (h3FourierAxisDirection (h3AxisOfFin3 i)) := by

  let v : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 i)

  have hFourier :
      HasFDerivAt
        (FourierTransform.fourier f)
        (FourierTransform.fourier
          (VectorFourier.fourierSMulRight (innerSL ℝ) f)
          (-x))
        (-x) :=
    Real.hasFDerivAt_fourier hf hMoment (-x)

  have hComp := hFourier.comp x ((hasFDerivAt_id x).neg)
  have hLine := hComp.hasLineDerivAt v

  have hSMulInt :
      Integrable
        (VectorFourier.fourierSMulRight (innerSL ℝ) f)
        (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi * ‖innerSL (E := H3FourierPoint3) ℝ‖) *
              (‖ξ‖ * ‖f ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hMoment.const_mul
        (2 * Real.pi * ‖innerSL (E := H3FourierPoint3) ℝ‖)

    apply hDom.mono'
    · exact hf.aestronglyMeasurable.fourierSMulRight
    · filter_upwards with ξ
      calc
        ‖VectorFourier.fourierSMulRight (innerSL ℝ) f ξ‖
            ≤
          2 * Real.pi * ‖innerSL (E := H3FourierPoint3) ℝ‖ * ‖ξ‖ * ‖f ξ‖ :=
          VectorFourier.norm_fourierSMulRight_le (innerSL ℝ) f ξ
        _ =
          (2 * Real.pi * ‖innerSL (E := H3FourierPoint3) ℝ‖) *
            (‖ξ‖ * ‖f ξ‖) := by ring

  have hDerivativeValue :
      ((FourierTransform.fourier
          (VectorFourier.fourierSMulRight (innerSL ℝ) f)
          (-x)).comp
        (-ContinuousLinearMap.id ℝ H3FourierPoint3))
        v
        =
      FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol i ξ * f ξ)
        x := by
    rw [ContinuousLinearMap.comp_apply]
    simp only [neg_apply, ContinuousLinearMap.id_apply]
    rw [Real.fourier_continuousLinearMap_apply hSMulInt]
    rw [Real.fourierInv_eq_fourier_neg]
    apply Real.fourier_congr_ae
    filter_upwards with ξ
    rw [h3FourierDerivativeSymbol_eq_inner]
    simp only [VectorFourier.fourierSMulRight_apply, v, smul_eq_mul]
    rw [map_neg, innerSL_apply_apply]
    simp [Complex.real_smul] <;> push_cast <;> ring

  rw [hDerivativeValue] at hLine

  have hRepresentativeEq :
      FourierTransformInv.fourierInv f
        =
      (FourierTransform.fourier f ∘ Neg.neg) := by
    funext y
    exact Real.fourierInv_eq_fourier_neg f y

  rw [hRepresentativeEq]
  simpa only [v] using hLine

private theorem fourierInv_re_onPoint3_spatialC1_of_integrable_firstMoment
    {f : H3FourierPoint3 → ℂ}
    (hf : Integrable f (volume : Measure H3FourierPoint3))
    (hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3)) :
    SpatialC1
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by

  have hMom :
      ∀ (n : ℕ), n ≤ (1 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hnNat : n ≤ 1 := by exact_mod_cast hn
    interval_cases n
    · simpa only [pow_zero, one_mul] using hf.norm
    · simpa only [pow_one] using hMoment

  have hFourier :
      ContDiff ℝ 1 (FourierTransform.fourier f) :=
    Real.contDiff_fourier hMom

  have hNeg : ContDiff ℝ 1 (fun x : H3FourierPoint3 => -x) := by
    fun_prop

  have hInv :
      ContDiff ℝ 1
        (fun x : H3FourierPoint3 =>
          FourierTransformInv.fourierInv f x) := by
    have hComp :
        ContDiff ℝ 1
          (fun x : H3FourierPoint3 =>
            FourierTransform.fourier f (-x)) :=
      hFourier.comp hNeg
    simpa only [Real.fourierInv_eq_fourier_neg] using hComp

  have hToLp :
      ContDiff ℝ 1
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) :=
    PiLp.contDiff_toLp

  have hComplex :
      ContDiff ℝ 1
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            f
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) :=
    hInv.comp hToLp

  change
    ContDiff ℝ 1
      (Complex.reCLM ∘
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            f
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)))

  exact Complex.reCLM.contDiff.comp hComplex

private theorem fourierInv_re_onPoint3_spatialDerivative_eq
    {f : H3FourierPoint3 → ℂ}
    (hf : Integrable f (volume : Measure H3FourierPoint3))
    (hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3))
    (a : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    spatial3.d a
        (fun y : Point3 =>
          (FourierTransformInv.fourierInv
            f
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) y)).re)
        x
      =
    (FourierTransformInv.fourierInv
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis a) ξ *
          f ξ)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by

  let g : ScalarField3 :=
    fun y : Point3 =>
      (FourierTransformInv.fourierInv
        f
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) y)).re

  let i : Fin 3 := h3ClassicalizationFinOfAxis a
  let ξ : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  have hgC1 : SpatialC1 g := by
    dsimp only [g]
    exact
      fourierInv_re_onPoint3_spatialC1_of_integrable_firstMoment
        hf hMoment

  have hTransport :=
    h3TransportScalarField_hasLineDerivAt hgC1 a ξ

  have hPoint : h3FourierToPoint3CLM ξ = x := by
    ext j
    rfl

  have hTransportFunction :
      (fun y : H3FourierPoint3 =>
        g (h3FourierToPoint3CLM y))
        =
      (fun y : H3FourierPoint3 =>
        (FourierTransformInv.fourierInv f y).re) := by
    funext y
    dsimp only [g]
    congr 2

  rw [hTransportFunction, hPoint] at hTransport

  change
    HasLineDerivAt ℝ
      (fun y : H3FourierPoint3 =>
        (FourierTransformInv.fourierInv f y).re)
      (spatial3.d a g x)
      ξ
      (h3FourierAxisDirection a)
    at hTransport

  have hComplex :=
    fourierInv_hasLineDerivAt_coordinate_of_integrable_firstMoment
      hf hMoment i ξ

  unfold HasLineDerivAt at hComplex

  have hReal :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt
      (0 : ℝ)
      hComplex

  have hFourier :
      HasLineDerivAt ℝ
        (fun y : H3FourierPoint3 =>
          (FourierTransformInv.fourierInv f y).re)
        ((FourierTransformInv.fourierInv
          (fun η : H3FourierPoint3 =>
            h3FourierDerivativeSymbol i η * f η)
          ξ).re)
        ξ
        (h3FourierAxisDirection (h3AxisOfFin3 i)) := by
    unfold HasLineDerivAt
    simpa only [Function.comp_def, Complex.reCLM_apply] using hReal

  have hAxis : h3AxisOfFin3 i = a := by
    dsimp only [i]
    exact h3AxisOfFin3_h3ClassicalizationFinOfAxis a

  rw [hAxis] at hFourier

  have hUnique := hTransport.unique hFourier

  simpa only [g, i, ξ] using hUnique

/-! ## Selected raw forcing first Fourier coordinate L² -/

private theorem h3SelectedRestartRawForcing_firstCoordinate_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          h3RawFinOuterProductDivergence
            (W t) (W t) i ξ)
      2
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinOuterProductDivergence (W t) (W t) i

  have hRadial :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 1 : ℝ) : ℂ) * N ξ)
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_radialWeight_memLp2
        1 hν U₀ hA hU₀ ht htR i

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hNInt :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact h3RawFinOuterProductDivergence_integrable (W t) (W t) i

  have hCoordInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ * N ξ)
        (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) * (‖ξ‖ * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hMoment.const_mul (2 * Real.pi)

    apply hDom.mono'
    · exact
        (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
          hNInt.aestronglyMeasurable
    · filter_upwards with ξ
      calc
        ‖h3FourierDerivativeSymbol a ξ * N ξ‖
            =
          ‖h3FourierDerivativeSymbol a ξ‖ * ‖N ξ‖ := by rw [norm_mul]
        _ ≤
          ((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖ := by
          exact
            mul_le_mul_of_nonneg_right
              (by
                simpa [h3FourierGradientMagnitude] using
                  norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ)
              (norm_nonneg _)
        _ =
          (2 * Real.pi) * (‖ξ‖ * ‖N ξ‖) := by ring

  refine
    hRadial.of_le_mul
      (c := 2 * Real.pi)
      hCoordInt.aestronglyMeasurable
      ?_

  filter_upwards with ξ

  have hTwoPi : 0 ≤ 2 * Real.pi := by positivity

  rw [norm_mul]

  have hDeriv :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ * ‖N ξ‖
        ≤
      ((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖ := by
      unfold h3FourierGradientMagnitude at hDeriv
      exact
        mul_le_mul_of_nonneg_right hDeriv (norm_nonneg _)
    _ =
      (2 * Real.pi) *
        ‖((‖ξ‖ ^ 1 : ℝ) : ℂ) * N ξ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp only [pow_one, abs_of_nonneg (norm_nonneg ξ)]
      ring

/-! ## Physical first derivative L² -/

/-- Every first spatial derivative of the real selected raw forcing belongs to
physical `L²`. -/
theorem h3SelectedRestartRealRawForcing_spatial_d_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (spatial3.d a
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv
            (h3RawFinOuterProductDivergence
              (W t) (W t) i)
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re))
      2
      (volume : Measure Point3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinOuterProductDivergence (W t) (W t) i

  let af : Fin 3 := h3ClassicalizationFinOfAxis a

  let raw : H3FourierPoint3 → ℂ :=
    fun ξ => h3FourierDerivativeSymbol af ξ * N ξ

  have hNInt :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact h3RawFinOuterProductDivergence_integrable (W t) (W t) i

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR.le i

  have hRawInt :
      Integrable raw (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, af, N, W]
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) *
              (‖ξ‖ *
                ‖h3RawFinOuterProductDivergence
                  ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀) t)
                  ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀) t)
                  i ξ‖))
          (volume : Measure H3FourierPoint3) :=
      (h3RawFinOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR.le i).const_mul (2 * Real.pi)

    apply hDom.mono'
    · exact
        (h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis a)).aestronglyMeasurable.mul
          (h3RawFinOuterProductDivergence_integrable
            ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀) t)
            ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀) t)
            i).aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_mul]
      have hDeriv :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis a) ξ
      unfold h3FourierGradientMagnitude at hDeriv
      calc
        ‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ‖ *
            ‖h3RawFinOuterProductDivergence
              ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀) t)
              ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀) t)
              i ξ‖
            ≤
          ((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawFinOuterProductDivergence
              ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀) t)
              ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀) t)
              i ξ‖ :=
          mul_le_mul_of_nonneg_right hDeriv (norm_nonneg _)
        _ =
          (2 * Real.pi) *
            (‖ξ‖ *
              ‖h3RawFinOuterProductDivergence
                ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀) t)
                ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀) t)
                i ξ‖) := by ring

  have hRaw2 :
      MemLp raw 2 (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, af, N, W]
    exact
      h3SelectedRestartRawForcing_firstCoordinate_memLp2
        hν U₀ hA hU₀ ht htR.le i
        (h3ClassicalizationFinOfAxis a)

  have hComplex :
      MemLp
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            raw
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        2
        (volume : Measure Point3) :=
    memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedRawFirst
      hRawInt hRaw2

  have hReal :
      MemLp
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv
            raw
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        2
        (volume : Measure Point3) :=
    memLp_re_of_memLp_complex_h3SelectedRawFirst hComplex

  have hEq :
      spatial3.d a
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv
              N
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    funext x
    dsimp only [raw, af]
    exact
      fourierInv_re_onPoint3_spatialDerivative_eq
        hNInt hMoment a x

  rw [hEq]
  exact hReal

end

end Euclidean
end Bridge
end PrimeTensor

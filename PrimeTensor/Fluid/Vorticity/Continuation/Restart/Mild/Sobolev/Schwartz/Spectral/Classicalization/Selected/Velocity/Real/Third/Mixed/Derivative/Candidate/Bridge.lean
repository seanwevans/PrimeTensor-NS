import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Second.Mixed.Derivative.Candidate.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Third.Temporal.Derivative.PDE.Form
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C3.Spatial.Regularity

/-!
# Classicalization: real order-three mixed-derivative candidate bridge

The remaining selected order-three time derivative will have the complex
coefficient

    ν * Σₖ D⁵u[eₐ,e_b,e_c,eₖ,eₖ] - D³N[eₐ,e_b,e_c].

The real PDE frontier is already available in concrete Euclidean form:

    ν * Σₖ ∂ₐ∂ᵦ∂𝑐∂ₖ∂ₖ u - ∂ₐ∂ᵦ∂𝑐 Re N.

This file proves that taking the real part of the complex coefficient gives
exactly that concrete real candidate.

No temporal differentiation or new estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealThirdMixedDerivativeCandidateBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-! ## Ordered higher partial calculus -/

private theorem contDiff_four_spatial_d_four_eq_iteratedFDeriv_four_axes_order3
    {f : ScalarField3}
    (hf : ContDiff ℝ 4 f)
    (x : Point3)
    (a b c d : PrimeTensor.Axis Depth.three) :
    spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (spatial3.d d f)))
        x
      =
    iteratedFDeriv ℝ 4 f x
      (![axisDirection a, axisDirection b, axisDirection c, axisDirection d] :
        Fin 4 → Point3) := by

  let m3 : Fin 3 → Point3 :=
    ![axisDirection b, axisDirection c, axisDirection d]

  let m4 : Fin 4 → Point3 :=
    ![axisDirection a, axisDirection b, axisDirection c, axisDirection d]

  have hf3 : SpatialC3 f := by
    unfold SpatialC3
    exact hf.of_le (by norm_num)

  have hThirdFun :
      (fun y : Point3 =>
        spatial3.d b
          (spatial3.d c
            (spatial3.d d f))
          y)
        =
      (fun y : Point3 =>
        iteratedFDeriv ℝ 3 f y m3) := by
    funext y
    dsimp only [m3]
    exact
      hf3.spatial_d_three_eq_iteratedFDeriv_three_axes
        y b c d

  have hD3C1 :
      ContDiff ℝ 1
        (iteratedFDeriv ℝ 3 f) := by
    exact
      hf.iteratedFDeriv_right
        (m := 1)
        (i := 3)
        (by norm_num)

  let evalCLM :
      (Point3 [×3]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    {
      toFun := fun T => T m3
      map_add' := by
        intro T S
        rfl
      map_smul' := by
        intro q T
        rfl
      cont := continuous_eval_const m3
    }

  have hEvalC1 :
      ContDiff ℝ 1
        (fun y : Point3 =>
          iteratedFDeriv ℝ 3 f y m3) := by
    change
      ContDiff ℝ 1
        (fun y : Point3 =>
          evalCLM (iteratedFDeriv ℝ 3 f y))
    exact
      hD3C1.continuousLinearMap_comp evalCLM

  have hScalarDiff :
      DifferentiableAt ℝ
        (fun y : Point3 =>
          iteratedFDeriv ℝ 3 f y m3)
        x :=
    hEvalC1.differentiable_one.differentiableAt

  have hD3Diff :
      DifferentiableAt ℝ
        (iteratedFDeriv ℝ 3 f)
        x :=
    hD3C1.differentiable_one.differentiableAt

  have hRec :
      iteratedFDeriv ℝ 4 f x m4
        =
      fderiv ℝ
          (fun y : Point3 =>
            iteratedFDeriv ℝ 3 f y
              (Fin.tail m4))
          x
          (m4 0) :=
    hD3Diff.iteratedFDeriv_succ_apply_left'

  change
    partialDeriv a
        (fun y : Point3 =>
          spatial3.d b
            (spatial3.d c
              (spatial3.d d f))
            y)
        x
      =
    iteratedFDeriv ℝ 4 f x
      (![axisDirection a, axisDirection b, axisDirection c, axisDirection d] :
        Fin 4 → Point3)

  rw [hThirdFun]

  rw [
    partialDeriv_eq_fderiv_axisDirection
      a hScalarDiff
  ]

  simpa only [
    m3,
    m4,
    Fin.tail_vecCons,
    Matrix.cons_val_zero
  ] using hRec.symm

/-- A spatially `C⁵` scalar field has the expected ordered fifth-partial
formula. -/
private theorem contDiff_five_spatial_d_five_eq_iteratedFDeriv_five_axes
    {f : ScalarField3}
    (hf : ContDiff ℝ 5 f)
    (x : Point3)
    (a b c d e : PrimeTensor.Axis Depth.three) :
    spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (spatial3.d d
              (spatial3.d e f))))
        x
      =
    iteratedFDeriv ℝ 5 f x
      (![
        axisDirection a,
        axisDirection b,
        axisDirection c,
        axisDirection d,
        axisDirection e
      ] : Fin 5 → Point3) := by

  let m4 : Fin 4 → Point3 :=
    ![axisDirection b, axisDirection c, axisDirection d, axisDirection e]

  let m5 : Fin 5 → Point3 :=
    ![
      axisDirection a,
      axisDirection b,
      axisDirection c,
      axisDirection d,
      axisDirection e
    ]

  have hFourthFun :
      (fun y : Point3 =>
        spatial3.d b
          (spatial3.d c
            (spatial3.d d
              (spatial3.d e f)))
          y)
        =
      (fun y : Point3 =>
        iteratedFDeriv ℝ 4 f y m4) := by
    funext y
    dsimp only [m4]
    exact
      contDiff_four_spatial_d_four_eq_iteratedFDeriv_four_axes_order3
        (hf.of_le (by norm_num))
        y b c d e

  have hD4C1 :
      ContDiff ℝ 1
        (iteratedFDeriv ℝ 4 f) := by
    exact
      hf.iteratedFDeriv_right
        (m := 1)
        (i := 4)
        (by norm_num)

  let evalCLM :
      (Point3 [×4]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    {
      toFun := fun T => T m4
      map_add' := by
        intro T S
        rfl
      map_smul' := by
        intro q T
        rfl
      cont := continuous_eval_const m4
    }

  have hEvalC1 :
      ContDiff ℝ 1
        (fun y : Point3 =>
          iteratedFDeriv ℝ 4 f y m4) := by
    change
      ContDiff ℝ 1
        (fun y : Point3 =>
          evalCLM (iteratedFDeriv ℝ 4 f y))
    exact
      hD4C1.continuousLinearMap_comp evalCLM

  have hScalarDiff :
      DifferentiableAt ℝ
        (fun y : Point3 =>
          iteratedFDeriv ℝ 4 f y m4)
        x :=
    hEvalC1.differentiable_one.differentiableAt

  have hD4Diff :
      DifferentiableAt ℝ
        (iteratedFDeriv ℝ 4 f)
        x :=
    hD4C1.differentiable_one.differentiableAt

  have hRec :
      iteratedFDeriv ℝ 5 f x m5
        =
      fderiv ℝ
          (fun y : Point3 =>
            iteratedFDeriv ℝ 4 f y
              (Fin.tail m5))
          x
          (m5 0) :=
    hD4Diff.iteratedFDeriv_succ_apply_left'

  change
    partialDeriv a
        (fun y : Point3 =>
          spatial3.d b
            (spatial3.d c
              (spatial3.d d
                (spatial3.d e f)))
            y)
        x
      =
    iteratedFDeriv ℝ 5 f x
      (![
        axisDirection a,
        axisDirection b,
        axisDirection c,
        axisDirection d,
        axisDirection e
      ] : Fin 5 → Point3)

  rw [hFourthFun]

  rw [
    partialDeriv_eq_fderiv_axisDirection
      a hScalarDiff
  ]

  simpa only [
    m4,
    m5,
    Fin.tail_vecCons,
    Matrix.cons_val_zero
  ] using hRec.symm

/-! ## Selected velocity fifth-order real/complex bridge -/

/-- The fifth Fréchet derivative of the selected real `Point3` representative
is the real part of the complex fifth Fréchet derivative after transporting
every direction through `h3Point3ToFourierCLM`. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_fifthFrechet_eval_eq_re
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (m : Fin 5 → Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 5
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W t i))
        x m
      =
    (iteratedFDeriv ℝ 5
        (h3SpectralScalarC1Representative
          (W t i))
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hComplexC5 :
      ContDiff ℝ 5
        (h3SpectralScalarC1Representative
          (W t i)) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
        5 hν U₀ hA hU₀ ht htR.le i

  have hRealC5 :
      ContDiff ℝ 5
        (h3SpectralScalarRealC1Representative
          (W t i)) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1Representative_contDiff_nat
        5 hν U₀ hA hU₀ ht htR.le i

  have hLeft :
      iteratedFDeriv ℝ 5
          (h3SpectralScalarRealC1Representative
            (W t i))
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 5
          (h3SpectralScalarC1Representative
            (W t i))
          (h3Point3ToFourierCLM x)) := by
    unfold h3SpectralScalarRealC1Representative

    change
      iteratedFDeriv ℝ 5
          (Complex.reCLM ∘
            h3SpectralScalarC1Representative
              (W t i))
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 5
          (h3SpectralScalarC1Representative
            (W t i))
          (h3Point3ToFourierCLM x))

    exact
      Complex.reCLM.iteratedFDeriv_comp_left
        hComplexC5.contDiffAt
        (by norm_num)

  rw [
    h3SpectralScalarRealC1RepresentativeOnPoint3_eq_comp
      (W t i)
  ]

  have hRight :=
    h3Point3ToFourierCLM.iteratedFDeriv_comp_right
      hRealC5
      x
      (i := 5)
      (by norm_num)

  rw [hRight]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply
  ]

  rw [hLeft]

  rfl

/-- An ordered concrete fifth spatial partial of the selected real
representative is the real part of the matching complex fifth Fréchet
coordinate. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_five_eq_re_fifthFrechet
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a b c d e : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (spatial3.d d
              (spatial3.d e
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W t i))))))
        x
      =
    (iteratedFDeriv ℝ 5
        (h3SpectralScalarC1Representative
          (W t i))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        ![
          h3FourierAxisDirection a,
          h3FourierAxisDirection b,
          h3FourierAxisDirection c,
          h3FourierAxisDirection d,
          h3FourierAxisDirection e
        ]).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : ScalarField3 :=
    h3SpectralScalarRealC1RepresentativeOnPoint3
      (W t i)

  let m : Fin 5 → Point3 :=
    ![
      axisDirection a,
      axisDirection b,
      axisDirection c,
      axisDirection d,
      axisDirection e
    ]

  let mf : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection a,
      h3FourierAxisDirection b,
      h3FourierAxisDirection c,
      h3FourierAxisDirection d,
      h3FourierAxisDirection e
    ]

  have hfC5 :
      ContDiff ℝ 5 f := by
    dsimp only [f, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
        5 hν U₀ hA hU₀ ht htR.le i

  have hSpatial :=
    contDiff_five_spatial_d_five_eq_iteratedFDeriv_five_axes
      hfC5 x a b c d e

  have hBridge :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_fifthFrechet_eval_eq_re
      hν U₀ hA hU₀ ht htR i x m

  have hm :
      (fun k : Fin 5 =>
        h3Point3ToFourierCLM (m k))
        =
      mf := by
    funext k
    fin_cases k
    · change
        h3Point3ToFourierCLM (axisDirection a)
          =
        h3FourierAxisDirection a
      exact h3Point3ToFourierCLM_axisDirection a
    · change
        h3Point3ToFourierCLM (axisDirection b)
          =
        h3FourierAxisDirection b
      exact h3Point3ToFourierCLM_axisDirection b
    · change
        h3Point3ToFourierCLM (axisDirection c)
          =
        h3FourierAxisDirection c
      exact h3Point3ToFourierCLM_axisDirection c
    · change
        h3Point3ToFourierCLM (axisDirection d)
          =
        h3FourierAxisDirection d
      exact h3Point3ToFourierCLM_axisDirection d
    · change
        h3Point3ToFourierCLM (axisDirection e)
          =
        h3FourierAxisDirection e
      exact h3Point3ToFourierCLM_axisDirection e

  rw [hm] at hBridge

  dsimp only [f, W, m, mf] at hSpatial hBridge ⊢

  exact hSpatial.trans hBridge

/-! ## Instantaneous forcing third-order real/complex bridge -/

/-- Third-Fréchet transport for the selected instantaneous forcing before
specializing to coordinate directions. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_thirdFrechet_eval_eq_re
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (m : Fin 3 → Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 3
        (fun y : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W t) (W t) i y).re)
        x m
      =
    (iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let G : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceC0Representative
      (W t) (W t) i

  let Gre : H3FourierPoint3 → ℝ :=
    Complex.reCLM ∘ G

  let f : ScalarField3 :=
    fun y : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i y).re

  have hGC3 :
      ContDiff ℝ 3 G := by
    dsimp only [G, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_contDiff_three
        hν U₀ hA hU₀ ht htR.le i

  have hGreC3 :
      ContDiff ℝ 3 Gre := by
    dsimp only [Gre]
    exact
      Complex.reCLM.contDiff.comp hGC3

  have hLeft :
      iteratedFDeriv ℝ 3
          Gre
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 3
          G
          (h3Point3ToFourierCLM x)) := by
    dsimp only [Gre]
    exact
      Complex.reCLM.iteratedFDeriv_comp_left
        hGC3.contDiffAt
        (by norm_num)

  have hfEq :
      f
        =
      Gre ∘ h3Point3ToFourierCLM := by
    funext y
    dsimp only [f, Gre, G]
    unfold
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
    rfl

  change
    iteratedFDeriv ℝ 3 f x m
      =
    (iteratedFDeriv ℝ 3
        G
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))).re

  rw [hfEq]

  have hRight :=
    h3Point3ToFourierCLM.iteratedFDeriv_comp_right
      hGreC3
      x
      (i := 3)
      (by norm_num)

  rw [hRight]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply
  ]

  rw [hLeft]

  rfl

/-- The ordered concrete third spatial partial of the real instantaneous
forcing is the real part of the matching complex forcing third-Fréchet
coordinate. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_three_eq_re_thirdFrechet
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a b c : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (fun y : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W t) (W t) i y).re)))
        x
      =
    (iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        ![
          h3FourierAxisDirection a,
          h3FourierAxisDirection b,
          h3FourierAxisDirection c
        ]).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : ScalarField3 :=
    fun y : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i y).re

  let m : Fin 3 → Point3 :=
    ![
      axisDirection a,
      axisDirection b,
      axisDirection c
    ]

  let mf : Fin 3 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection a,
      h3FourierAxisDirection b,
      h3FourierAxisDirection c
    ]

  have hfC3 :
      SpatialC3 f := by
    unfold SpatialC3
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_three
        hν U₀ hA hU₀ ht htR.le i

  have hSpatial :
      spatial3.d a
          (spatial3.d b
            (spatial3.d c f))
          x
        =
      iteratedFDeriv ℝ 3 f x m := by
    dsimp only [m]
    exact
      hfC3.spatial_d_three_eq_iteratedFDeriv_three_axes
        x a b c

  have hBridge :=
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_thirdFrechet_eval_eq_re
      hν U₀ hA hU₀ ht htR i x m

  have hm :
      (fun k : Fin 3 =>
        h3Point3ToFourierCLM (m k))
        =
      mf := by
    funext k
    fin_cases k
    · change
        h3Point3ToFourierCLM (axisDirection a)
          =
        h3FourierAxisDirection a
      exact h3Point3ToFourierCLM_axisDirection a
    · change
        h3Point3ToFourierCLM (axisDirection b)
          =
        h3FourierAxisDirection b
      exact h3Point3ToFourierCLM_axisDirection b
    · change
        h3Point3ToFourierCLM (axisDirection c)
          =
        h3FourierAxisDirection c
      exact h3Point3ToFourierCLM_axisDirection c

  rw [hm] at hBridge

  dsimp only [f, W, m, mf] at hSpatial hBridge ⊢

  exact hSpatial.trans hBridge

/-! ## Full candidate bridge -/

/-- Taking real parts of the complex third-Fréchet time-derivative coefficient
produces exactly the concrete order-three mixed-derivative PDE candidate. -/
theorem h3SelectedVelocity_C1_thirdFrechet_coordinate_timeDerivativeCandidate_re_eq_thirdMixedDerivativeCandidate
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let xf : H3FourierPoint3 :=
      (WithLp.toLp 2 : Point3 → H3FourierPoint3) x
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let ec : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 c)
    let m : Fin 3 → H3FourierPoint3 :=
      ![ea, eb, ec]
    Complex.re
      ((ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 5
              (h3SpectralScalarC1Representative
                (W t i))
              xf
              ![
                ea,
                eb,
                ec,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        -
      iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        xf m)
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d
            (h3AxisOfFin3 a)
            (spatial3.d
              (h3AxisOfFin3 b)
              (spatial3.d
                (h3AxisOfFin3 c)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (h3SpectralScalarRealC1RepresentativeOnPoint3
                      (W t i))))))
            x)
      -
    spatial3.d
      (h3AxisOfFin3 a)
      (spatial3.d
        (h3AxisOfFin3 b)
        (spatial3.d
          (h3AxisOfFin3 c)
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W t) (W t) i y).re)))
      x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let xf : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)

  let m : Fin 3 → H3FourierPoint3 :=
    ![ea, eb, ec]

  let term : Fin 3 → ℂ :=
    fun k =>
      iteratedFDeriv ℝ 5
        (h3SpectralScalarC1Representative
          (W t i))
        xf
        ![
          ea,
          eb,
          ec,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  let force : ℂ :=
    iteratedFDeriv ℝ 3
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      xf m

  have hTerm
      (k : Fin 3) :
      (term k).re
        =
      spatial3.d
        (h3AxisOfFin3 a)
        (spatial3.d
          (h3AxisOfFin3 b)
          (spatial3.d
            (h3AxisOfFin3 c)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W t i))))))
        x := by
    dsimp only [term, xf, ea, eb, ec]
    exact
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_five_eq_re_fifthFrechet
        hν U₀ hA hU₀ ht htR i x
        (h3AxisOfFin3 a)
        (h3AxisOfFin3 b)
        (h3AxisOfFin3 c)
        (h3AxisOfFin3 k)
        (h3AxisOfFin3 k)).symm

  have hTrace :
      (∑ k : Fin 3, term k).re
        =
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 a)
          (spatial3.d
            (h3AxisOfFin3 b)
            (spatial3.d
              (h3AxisOfFin3 c)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W t i))))))
          x := by
    change
      Complex.reCLM (∑ k : Fin 3, term k)
        =
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 a)
          (spatial3.d
            (h3AxisOfFin3 b)
            (spatial3.d
              (h3AxisOfFin3 c)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W t i))))))
          x
    rw [map_sum]
    exact
      Finset.sum_congr rfl
        (fun k _hk => hTerm k)

  have hForce :
      force.re
        =
      spatial3.d
        (h3AxisOfFin3 a)
        (spatial3.d
          (h3AxisOfFin3 b)
          (spatial3.d
            (h3AxisOfFin3 c)
            (fun y : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W t) (W t) i y).re)))
        x := by
    dsimp only [force, xf, m, ea, eb, ec]
    exact
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_three_eq_re_thirdFrechet
        hν U₀ hA hU₀ ht htR i x
        (h3AxisOfFin3 a)
        (h3AxisOfFin3 b)
        (h3AxisOfFin3 c)).symm

  change
    Complex.re
      ((ν : ℂ) * (∑ k : Fin 3, term k) - force)
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d
            (h3AxisOfFin3 a)
            (spatial3.d
              (h3AxisOfFin3 b)
              (spatial3.d
                (h3AxisOfFin3 c)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (h3SpectralScalarRealC1RepresentativeOnPoint3
                      (W t i))))))
            x)
      -
    spatial3.d
      (h3AxisOfFin3 a)
      (spatial3.d
        (h3AxisOfFin3 b)
        (spatial3.d
          (h3AxisOfFin3 c)
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W t) (W t) i y).re)))
      x

  rw [Complex.sub_re, Complex.mul_re]

  simp only [
    Complex.ofReal_re,
    Complex.ofReal_im,
    zero_mul,
    sub_zero
  ]

  rw [hTrace, hForce]

end

end Euclidean
end Bridge
end PrimeTensor

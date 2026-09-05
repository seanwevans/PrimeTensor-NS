import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Point3.Frechet.Continuity
import PrimeTensor.Bridge.Euclidean.Partials.Third

/-!
# Classicalization: cubic third-partial difference continuity

`CubicPoint3FrechetContinuity` has already transported the selected cubic
Fourier estimate all the way to the third Frechet derivative of the real
`Point3` representative.

This file performs the remaining Euclidean identification between that
Frechet derivative and the project's concrete ordered coordinate derivatives.

The bridge is deliberately split into two reusable facts.

1. For a spatially `C²` scalar field, the ordered second coordinate partial is
   `iteratedFDeriv ℝ 2` evaluated on the corresponding two `axisDirection`s.
2. For a spatially `C³` scalar field, the ordered third coordinate partial is
   `iteratedFDeriv ℝ 3` evaluated on the corresponding three
   `axisDirection`s.

The second fact uses Mathlib's left-recursive definition of
`iteratedFDeriv`, so the order is exactly

    outer axis, middle axis, inner axis.

No mixed-partial symmetry is used.

The selected-path conclusion of this file is still phrased for the
representative of the spectral *difference state*.  The next increment can
therefore isolate the linearity statement

    Rep (F - G) = Rep F - Rep G

and convert this difference-to-zero theorem into ordinary `ContinuousAt` of
the third spatial jet.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationCubicThirdPartialDifferenceContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- The project's ordered second coordinate partial is the second Frechet
derivative evaluated on the two corresponding coordinate directions. -/
theorem SpatialC2.secondPartial_eq_iteratedFDeriv_two_axes
    {dim : Depth}
    {f : PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC2 f)
    (x : PrimeTensor.Point ℝ dim)
    (i j : PrimeTensor.Axis dim) :
    partialDeriv i
        (fun y => partialDeriv j f y)
        x
      =
    iteratedFDeriv ℝ 2 f x
      (![axisDirection i, axisDirection j] :
        Fin 2 → PrimeTensor.Point ℝ dim) := by
  rw [
    hf.secondPartial_eq_fderiv_fderiv
      x i j
  ]

  simpa using
    (iteratedFDeriv_two_apply
      (𝕜 := ℝ)
      f
      x
      (![axisDirection i, axisDirection j] :
        Fin 2 → PrimeTensor.Point ℝ dim)).symm

/-- The project's ordered third coordinate partial is the complete third
Frechet derivative evaluated on the three corresponding coordinate
directions.

The first entry of the direction vector is the *outermost* derivative, in
accord with `iteratedFDeriv_succ_apply_left`. -/
theorem SpatialC3.spatial_d_three_eq_iteratedFDeriv_three_axes
    {dim : Depth}
    {f : PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC3 f)
    (x : PrimeTensor.Point ℝ dim)
    (a b c : PrimeTensor.Axis dim) :
    (spatial dim).d a
        ((spatial dim).d b
          ((spatial dim).d c f))
        x
      =
    iteratedFDeriv ℝ 3 f x
      (![axisDirection a, axisDirection b, axisDirection c] :
        Fin 3 → PrimeTensor.Point ℝ dim) := by
  let m2 : Fin 2 → PrimeTensor.Point ℝ dim :=
    ![axisDirection b, axisDirection c]

  let m3 : Fin 3 → PrimeTensor.Point ℝ dim :=
    ![axisDirection a, axisDirection b, axisDirection c]

  have hf2 : SpatialC2 f :=
    hf.toSpatialC2

  have hInnerC2 :
      SpatialC2
        (fun y =>
          partialDeriv c f y) :=
    hf.partialDeriv_contDiff_two c

  have hSecondC1 :
      SpatialC1
        (fun y =>
          partialDeriv b
            (fun z => partialDeriv c f z)
            y) := by
    unfold SpatialC1
    rw [
      hInnerC2.partialDeriv_fun_eq
        b
    ]
    exact
      hInnerC2.fderiv_axisDirection_contDiff_one
        b

  have hSecondFun :
      (fun y =>
        partialDeriv b
          (fun z => partialDeriv c f z)
          y)
        =
      (fun y =>
        iteratedFDeriv ℝ 2 f y m2) := by
    funext y
    dsimp only [m2]
    exact
      hf2.secondPartial_eq_iteratedFDeriv_two_axes
        y b c

  have hScalarDiff :
      DifferentiableAt ℝ
        (fun y =>
          iteratedFDeriv ℝ 2 f y m2)
        x := by
    rw [← hSecondFun]
    exact
      hSecondC1.differentiable_one.differentiableAt

  have hD2C1 :
      ContDiff ℝ 1
        (iteratedFDeriv ℝ 2 f) := by
    unfold SpatialC3 at hf
    exact
      hf.iteratedFDeriv_right
        (m := 1)
        (i := 2)
        (by norm_num)

  have hD2Diff :
      DifferentiableAt ℝ
        (iteratedFDeriv ℝ 2 f)
        x :=
    hD2C1.differentiable_one.differentiableAt

  have hRec :
      iteratedFDeriv ℝ 3 f x m3
        =
      fderiv ℝ
          (fun y =>
            iteratedFDeriv ℝ 2 f y
              (Fin.tail m3))
          x
          (m3 0) :=
    hD2Diff.iteratedFDeriv_succ_apply_left'

  change
    partialDeriv a
        (fun y =>
          partialDeriv b
            (fun z => partialDeriv c f z)
            y)
        x
      =
    iteratedFDeriv ℝ 3 f x
      (![axisDirection a, axisDirection b, axisDirection c] :
        Fin 3 → PrimeTensor.Point ℝ dim)

  rw [hSecondFun]

  rw [
    partialDeriv_eq_fderiv_axisDirection
      a hScalarDiff
  ]

  simpa only [
    m2,
    m3,
    Fin.tail_vecCons,
    Matrix.cons_val_zero
  ] using hRec.symm

/-- Cubic moment integrability makes the real representative on the project's
actual `Point3` carrier spatially `C³`. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_three_of_cubic
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H) :
    ContDiff ℝ 3
      (h3SpectralScalarRealC1RepresentativeOnPoint3 H) := by
  rw [
    h3SpectralScalarRealC1RepresentativeOnPoint3_eq_comp
      H
  ]

  exact
    (h3SpectralScalarRealC1Representative_contDiff_three_of_cubic
      H hThree).comp_continuousLinearMap

/-- For the selected restart path, every ordered third spatial partial of the
real representative of the spectral difference state tends to zero at each
strict positive interior time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_thirdPartial_difference_norm_tendsto_zero
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a b c : PrimeTensor.Axis Depth.three) :
    Tendsto
      (fun r : ℝ =>
        ‖spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ r i
                  -
                  h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ s i))))
          x‖)
      (𝓝 s)
      (𝓝 0) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let m : Fin 3 → Point3 :=
    ![axisDirection a, axisDirection b, axisDirection c]

  have hFrechet :
      Tendsto
        (fun r : ℝ =>
          ‖iteratedFDeriv ℝ 3
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W r i - W s i))
            x m‖)
        (𝓝 s)
        (𝓝 0) := by
    dsimp only [m]
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_thirdFrechet_difference_eval_norm_tendsto_zero
        hν U₀ hA hU₀ hs hsR i x
        (![axisDirection a, axisDirection b, axisDirection c] :
          Fin 3 → Point3)

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEventuallyEq :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 3
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r i - W s i))
          x m‖
          =
        ‖spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i - W s i))))
          x‖ := by
    filter_upwards [hInterval] with r hr

    have hrThreeOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ hr.1 hr.2.le i

    have hsThreeOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ hs hsR.le i

    have hrThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_three_classicalization_cubicFrechet
      ] using hrThreeOrd

    have hsThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W s i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_three_classicalization_cubicFrechet
      ] using hsThreeOrd

    have hDiffThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i - W s i) :=
      h3RawFourierMomentIntegrable_three_sub
        (W r i) (W s i) hrThree hsThree

    have hC3 :
        SpatialC3
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r i - W s i)) := by
      unfold SpatialC3
      exact
        h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_three_of_cubic
          (W r i - W s i)
          hDiffThree

    have hAxis :=
      hC3.spatial_d_three_eq_iteratedFDeriv_three_axes
        x a b c

    dsimp only [m]

    change
      ‖iteratedFDeriv ℝ 3
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r i - W s i))
          x
          (![axisDirection a, axisDirection b, axisDirection c] :
            Fin 3 → Point3)‖
        =
      ‖(spatial Depth.three).d a
          ((spatial Depth.three).d b
            ((spatial Depth.three).d c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i - W s i))))
          x‖

    exact congrArg norm hAxis.symm

  have hTarget :
      Tendsto
        (fun r : ℝ =>
          ‖spatial3.d a
            (spatial3.d b
              (spatial3.d c
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W r i - W s i))))
            x‖)
        (𝓝 s)
        (𝓝 0) :=
    hFrechet.congr' hEventuallyEq

  simpa only [W] using hTarget

end
end Euclidean
end Bridge
end PrimeTensor

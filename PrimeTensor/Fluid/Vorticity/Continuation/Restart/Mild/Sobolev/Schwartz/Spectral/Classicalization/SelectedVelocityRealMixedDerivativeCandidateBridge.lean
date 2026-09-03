import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealSpatialPartialBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocitySpatialTemporalDerivativePDEForm
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.CubicThirdPartialDifferenceContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedForcingC1SpatialRegularity

/-!
# Classicalization: real mixed-derivative candidate bridge

The complex first spatial Fréchet coordinate has an explicit time derivative,

    ν * Σₖ D³u[eₐ,eₖ,eₖ] - DN[eₐ].

The real mixed-regularity frontier is written instead with the concrete
Euclidean candidate

    ν * Σₖ ∂ₐ∂ₖ∂ₖ u - ∂ₐ Re N.

This file proves that taking the real part of the complex coefficient gives
exactly that concrete real candidate.

There are two representation steps.

* The selected third Fréchet derivative is transported through real-part
  extraction and the canonical `Point3 → H3FourierPoint3` map, then identified
  with the ordered third concrete spatial partial.
* The selected forcing first Fréchet derivative is transported through the
  same two fixed linear maps and identified with `spatial3.d`.

No time differentiation, new estimate, or mixed-partial commutation is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealMixedDerivativeCandidateBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- One ordered third concrete spatial partial of the selected real
representative is the real part of the corresponding complex third Fréchet
coordinate. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_three_eq_re_thirdFrechet
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
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W t i))))
        x
      =
    (iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (W t i))
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

  let H : H3SpectralScalarState :=
    W t i

  have hThreeOrd :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
      3 hν U₀ hA hU₀ ht htR.le i

  have hThree :
      H3RawFourierMomentIntegrable (3 : ℝ) H := by
    unfold H3RawFourierMomentIntegrable
    simpa only [
      H,
      W,
      h3FourierMomentWeight_three_classicalization_cubicFrechet
    ] using hThreeOrd

  have hC3 :
      SpatialC3
        (h3SpectralScalarRealC1RepresentativeOnPoint3 H) := by
    unfold SpatialC3
    dsimp only [H, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
        3 hν U₀ hA hU₀ ht htR.le i

  have hSpatial :=
    hC3.spatial_d_three_eq_iteratedFDeriv_three_axes
      x a b c

  let m : Fin 3 → Point3 :=
    ![axisDirection a, axisDirection b, axisDirection c]

  let mf : Fin 3 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection a,
      h3FourierAxisDirection b,
      h3FourierAxisDirection c
    ]

  have hAxis
      (d : PrimeTensor.Axis Depth.three) :
      (WithLp.toLp 2 : Point3 → H3FourierPoint3) (axisDirection d)
        =
      h3FourierAxisDirection d := by
    simpa only [h3Point3ToFourierCLM_apply] using
      h3Point3ToFourierCLM_axisDirection d

  have hm :
      (fun k : Fin 3 =>
        h3Point3ToFourierCLM (m k))
        =
      mf := by
    funext k
    fin_cases k <;>
      simp [
        m,
        mf,
        h3Point3ToFourierCLM_apply,
        hAxis
      ]

  have hTransport :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_thirdFrechet_eval_eq_re
      H hThree x m

  rw [hm] at hTransport

  dsimp only [H, W, m, mf] at hSpatial hTransport ⊢

  exact hSpatial.trans hTransport

/-- First-Fréchet transport for the selected instantaneous forcing, before
specializing to a coordinate direction. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_firstFrechet_eval_eq_re
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (m : Fin 1 → Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 1
        (fun y : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W t) (W t) i y).re)
        x m
      =
    (iteratedFDeriv ℝ 1
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

  have hGC1 :
      ContDiff ℝ 1 G := by
    dsimp only [G, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_contDiff_one
        hν U₀ hA hU₀ ht htR.le i

  have hGreC1 :
      ContDiff ℝ 1 Gre := by
    dsimp only [Gre]
    exact
      Complex.reCLM.contDiff.comp hGC1

  have hLeft :
      iteratedFDeriv ℝ 1
          Gre
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 1
          G
          (h3Point3ToFourierCLM x)) := by
    dsimp only [Gre]
    exact
      Complex.reCLM.iteratedFDeriv_comp_left
        hGC1.contDiffAt
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
    iteratedFDeriv ℝ 1 f x m
      =
    (iteratedFDeriv ℝ 1
        G
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))).re

  rw [hfEq]

  have hRight :=
    h3Point3ToFourierCLM.iteratedFDeriv_comp_right
      hGreC1
      x
      (i := 1)
      (by norm_num)

  rw [hRight]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply
  ]

  rw [hLeft]

  rfl

/-- The concrete spatial partial of the real selected forcing is the real part
of the Fourier-carrier forcing Fréchet derivative in the matching coordinate
direction. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_eq_re_fderiv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d
        a
        (fun y : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W t) (W t) i y).re)
        x
      =
    ((fderiv ℝ
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
      (h3FourierAxisDirection a)).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : ScalarField3 :=
    fun y : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i y).re

  have hfC1 :
      SpatialC1 f := by
    unfold SpatialC1
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_one
        hν U₀ hA hU₀ ht htR.le i

  have hPartial :
      spatial3.d a f x
        =
      (fderiv ℝ f x) (axisDirection a) := by
    exact
      hfC1.partialDeriv_eq_fderiv_axisDirection
        x a

  have hBridge :=
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_firstFrechet_eval_eq_re
      hν U₀ hA hU₀ ht htR i x
      (fun _ : Fin 1 => axisDirection a)

  have hAxis :
      (WithLp.toLp 2 : Point3 → H3FourierPoint3) (axisDirection a)
        =
      h3FourierAxisDirection a := by
    simpa only [h3Point3ToFourierCLM_apply] using
      h3Point3ToFourierCLM_axisDirection a

  have hBridge' :
      (fderiv ℝ f x) (axisDirection a)
        =
      ((fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        (h3FourierAxisDirection a)).re := by
    simpa only [
      f,
      W,
      iteratedFDeriv_one_apply,
      h3Point3ToFourierCLM_apply,
      hAxis
    ] using hBridge

  change
    spatial3.d a f x
      =
    ((fderiv ℝ
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
      (h3FourierAxisDirection a)).re

  exact hPartial.trans hBridge'

/-- Taking real parts of the complex first-Fréchet time-derivative coefficient
produces exactly the concrete real mixed-derivative PDE candidate. -/
theorem h3SelectedVelocity_C1_fderiv_coordinate_timeDerivativeCandidate_re_eq_mixedDerivativeCandidate
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let xf : H3FourierPoint3 :=
      (WithLp.toLp 2 : Point3 → H3FourierPoint3) x
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    Complex.re
      ((ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 3
              (h3SpectralScalarC1Representative
                (W t i))
              xf
              ![
                ea,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        -
      (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          xf) ea)
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d
            (h3AxisOfFin3 a)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W t i))))
            x)
      -
    spatial3.d
      (h3AxisOfFin3 a)
      (fun y : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t) i y).re)
      x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let xf : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let term : Fin 3 → ℂ :=
    fun k =>
      iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (W t i))
        xf
        ![
          ea,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  have hTerm
      (k : Fin 3) :
      (term k).re
        =
      spatial3.d
        (h3AxisOfFin3 a)
        (spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W t i))))
        x := by
    exact
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_three_eq_re_thirdFrechet
        hν U₀ hA hU₀ ht htR i x
        (h3AxisOfFin3 a)
        (h3AxisOfFin3 k)
        (h3AxisOfFin3 k)).symm

  have hTrace :
      (∑ k : Fin 3, term k).re
        =
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 a)
          (spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W t i))))
          x := by
    change
      Complex.reCLM (∑ k : Fin 3, term k)
        =
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 a)
          (spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W t i))))
          x
    rw [map_sum]
    exact
      Finset.sum_congr rfl
        (fun k _hk => hTerm k)

  have hForce :
      ((fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          xf) ea).re
        =
      spatial3.d
        (h3AxisOfFin3 a)
        (fun y : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W t) (W t) i y).re)
        x := by
    dsimp only [xf, ea]
    exact
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_eq_re_fderiv
        hν U₀ hA hU₀ ht htR i x
        (h3AxisOfFin3 a)).symm

  change
    Complex.re
      ((ν : ℂ) * (∑ k : Fin 3, term k)
        -
      (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          xf) ea)
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d
            (h3AxisOfFin3 a)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W t i))))
            x)
      -
    spatial3.d
      (h3AxisOfFin3 a)
      (fun y : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t) i y).re)
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

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Time.Derivative.Pointwise.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Second.Partial.Bridge

/-!
# Classicalization: second spatial partial of the real temporal derivative

The pointwise real/complex temporal-derivative bridge now identifies

    d/dt Re uᶜ(t,toLp x) = Re (d/dt uᶜ(t,toLp x)).

Both temporal-derivative fields are spatially `C²`.  This file differentiates
that representation identity twice in the ordinary `Point3` variable and
records the exact ordered two-axis formula.

No time/space commutation is asserted here.  The result only identifies the
already-existing spatial second derivative of the temporal derivative with the
real part of the complex second Fréchet derivative of the complex temporal
derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealTimeDerivativeSecondPartialBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Generic order-two transport through real-part extraction and the canonical
`Point3 → H3FourierPoint3` linear map. -/
private theorem contDiff_two_re_comp_h3Point3ToFourierCLM_secondFrechet_eval_eq_re
    {gC : H3FourierPoint3 → ℂ}
    (hgC : ContDiff ℝ 2 gC)
    (x : Point3)
    (m : Fin 2 → Point3) :
    iteratedFDeriv ℝ 2
        (fun y : Point3 =>
          (gC (h3Point3ToFourierCLM y)).re)
        x m
      =
    (iteratedFDeriv ℝ 2
        gC
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))).re := by

  let gR : H3FourierPoint3 → ℝ :=
    fun ξ => (gC ξ).re

  have hgR : ContDiff ℝ 2 gR := by
    dsimp only [gR]
    simpa only [
      Function.comp_apply,
      Complex.reCLM_apply
    ] using
      hgC.continuousLinearMap_comp Complex.reCLM

  have hLeft :
      iteratedFDeriv ℝ 2
          gR
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 2
          gC
          (h3Point3ToFourierCLM x)) := by
    dsimp only [gR]

    change
      iteratedFDeriv ℝ 2
          (Complex.reCLM ∘ gC)
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 2
          gC
          (h3Point3ToFourierCLM x))

    exact
      Complex.reCLM.iteratedFDeriv_comp_left
        hgC.contDiffAt
        (by norm_num)

  have hRight :=
    h3Point3ToFourierCLM.iteratedFDeriv_comp_right
      hgR
      x
      (i := 2)
      (by norm_num)

  change
    iteratedFDeriv ℝ 2
        (gR ∘ h3Point3ToFourierCLM)
        x m
      =
    (iteratedFDeriv ℝ 2
        gC
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))).re

  rw [hRight]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply
  ]

  rw [hLeft]

  rfl

/-- The ordered second spatial partial of the actual real temporal derivative
is the real part of the corresponding complex second-Fréchet derivative of the
actual complex temporal derivative. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_timeDerivative_secondPartial_eq_re_complexTimeDerivative_secondFrechet_axes
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a b : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d a
        (spatial3.d b
          (fun y : Point3 =>
            deriv
              (fun s : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W s i) y)
              t))
        x
      =
    (iteratedFDeriv ℝ 2
        (fun ξ : H3FourierPoint3 =>
          deriv
            (fun s : ℝ =>
              h3SpectralScalarC1Representative
                (W s i) ξ)
            t)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        (![h3FourierAxisDirection a, h3FourierAxisDirection b] :
          Fin 2 → H3FourierPoint3)).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let gC : H3FourierPoint3 → ℂ :=
    fun ξ =>
      deriv
        (fun s : ℝ =>
          h3SpectralScalarC1Representative
            (W s i) ξ)
        t

  let gR : Point3 → ℝ :=
    fun y =>
      deriv
        (fun s : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s i) y)
        t

  have hgC : ContDiff ℝ 2 gC := by
    dsimp only [gC, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_timeDerivative_spatial_contDiff_two
        hν U₀ hA hU₀ ht htR i

  have hFieldEq :
      gR
        =
      (fun y : Point3 =>
        (gC (h3Point3ToFourierCLM y)).re) := by
    funext y

    have hPoint :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_timeDerivative_eq_re_complexTimeDerivative
        hν U₀ hA hU₀ ht htR i y

    dsimp only at hPoint
    dsimp only [gR, gC, W]

    simpa only [
      h3Point3ToFourierCLM_apply
    ] using hPoint

  have hgRComp :
      SpatialC2
        (fun y : Point3 =>
          (gC (h3Point3ToFourierCLM y)).re) := by
    unfold SpatialC2

    have hgReal : ContDiff ℝ 2 (fun ξ : H3FourierPoint3 => (gC ξ).re) := by
      simpa only [
        Function.comp_apply,
        Complex.reCLM_apply
      ] using
        hgC.continuousLinearMap_comp Complex.reCLM

    exact
      hgReal.comp_continuousLinearMap

  have hPartial :
      spatial3.d a
          (spatial3.d b
            (fun y : Point3 =>
              (gC (h3Point3ToFourierCLM y)).re))
          x
        =
      iteratedFDeriv ℝ 2
          (fun y : Point3 =>
            (gC (h3Point3ToFourierCLM y)).re)
          x
          (![axisDirection a, axisDirection b] : Fin 2 → Point3) := by
    change
      partialDeriv a
          (fun y =>
            partialDeriv b
              (fun z : Point3 =>
                (gC (h3Point3ToFourierCLM z)).re)
              y)
          x
        =
      iteratedFDeriv ℝ 2
          (fun y : Point3 =>
            (gC (h3Point3ToFourierCLM y)).re)
          x
          (![axisDirection a, axisDirection b] : Fin 2 → Point3)

    exact
      hgRComp.secondPartial_eq_iteratedFDeriv_two_axes
        x a b

  have hFrechet :=
    contDiff_two_re_comp_h3Point3ToFourierCLM_secondFrechet_eval_eq_re
      hgC
      x
      (![axisDirection a, axisDirection b] : Fin 2 → Point3)

  have hDirections :
      (fun k : Fin 2 =>
        h3Point3ToFourierCLM
          ((![axisDirection a, axisDirection b] : Fin 2 → Point3) k))
        =
      (![h3FourierAxisDirection a, h3FourierAxisDirection b] :
        Fin 2 → H3FourierPoint3) := by
    funext k
    fin_cases k
    · change
        h3Point3ToFourierCLM (axisDirection a)
          =
        h3FourierAxisDirection a
      exact
        h3Point3ToFourierCLM_axisDirection a
    · change
        h3Point3ToFourierCLM (axisDirection b)
          =
        h3FourierAxisDirection b
      exact
        h3Point3ToFourierCLM_axisDirection b

  change
    spatial3.d a
        (spatial3.d b gR)
        x
      =
    (iteratedFDeriv ℝ 2
        gC
        (h3Point3ToFourierCLM x)
        (![h3FourierAxisDirection a, h3FourierAxisDirection b] :
          Fin 2 → H3FourierPoint3)).re

  rw [hFieldEq]

  calc
    spatial3.d a
        (spatial3.d b
          (fun y : Point3 =>
            (gC (h3Point3ToFourierCLM y)).re))
        x
        =
      iteratedFDeriv ℝ 2
        (fun y : Point3 =>
          (gC (h3Point3ToFourierCLM y)).re)
        x
        (![axisDirection a, axisDirection b] : Fin 2 → Point3) :=
      hPartial

    _ =
      (iteratedFDeriv ℝ 2
          gC
          (h3Point3ToFourierCLM x)
          (fun k =>
            h3Point3ToFourierCLM
              ((![axisDirection a, axisDirection b] : Fin 2 → Point3) k))).re :=
      hFrechet

    _ =
      (iteratedFDeriv ℝ 2
          gC
          (h3Point3ToFourierCLM x)
          (![h3FourierAxisDirection a, h3FourierAxisDirection b] :
            Fin 2 → H3FourierPoint3)).re := by
      rw [hDirections]

    _ =
      (iteratedFDeriv ℝ 2
          (fun ξ : H3FourierPoint3 =>
            deriv
              (fun s : ℝ =>
                h3SpectralScalarC1Representative
                  (W s i) ξ)
              t)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
          (![h3FourierAxisDirection a, h3FourierAxisDirection b] :
            Fin 2 → H3FourierPoint3)).re := by
      simp only [
        gC,
        h3Point3ToFourierCLM_apply
      ]

/-- Velocity-component form of the second-spatial-partial temporal-derivative
representation bridge. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_timeDerivative_secondPartial_eq_re_complexTimeDerivative_secondFrechet_axes
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (j a b : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d a
        (spatial3.d b
          (fun y : Point3 =>
            temporal.d
              (fun s : ℝ =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  hν U₀ hA hU₀ s y).component j)
              t))
        x
      =
    (iteratedFDeriv ℝ 2
        (fun ξ : H3FourierPoint3 =>
          deriv
            (fun s : ℝ =>
              h3SpectralScalarC1Representative
                (W s (h3ClassicalizationFinOfAxis j)) ξ)
            t)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        (![h3FourierAxisDirection a, h3FourierAxisDirection b] :
          Fin 2 → H3FourierPoint3)).re := by
  dsimp only

  change
    spatial3.d a
        (spatial3.d b
          (fun y : Point3 =>
            deriv
              (fun s : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ s
                    (h3ClassicalizationFinOfAxis j))
                  y)
              t))
        x
      =
    (iteratedFDeriv ℝ 2
        (fun ξ : H3FourierPoint3 =>
          deriv
            (fun s : ℝ =>
              h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ s
                  (h3ClassicalizationFinOfAxis j))
                ξ)
            t)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        (![h3FourierAxisDirection a, h3FourierAxisDirection b] :
          Fin 2 → H3FourierPoint3)).re

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_timeDerivative_secondPartial_eq_re_complexTimeDerivative_secondFrechet_axes
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)
      x a b

end

end Euclidean
end Bridge
end PrimeTensor

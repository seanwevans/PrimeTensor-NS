import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Hessian.Trace.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Third.Partial.Difference.Continuity

/-!
# Classicalization: selected real second-partial / second-Fréchet bridge

The selected real `Point3` representative already has an exact transport of its
complete second Fréchet derivative to the complex Fourier carrier.  The
Euclidean partial calculus also identifies an ordered pair of concrete
coordinate derivatives with evaluation of the second Fréchet derivative on
the corresponding coordinate directions.

This file composes those two bridges.  At every strict positive interior
restart time,

    ∂ₐ∂ᵦ uᵢ(t,x)

is exactly the real part of the complex selected second Fréchet derivative
evaluated on the two Fourier coordinate directions associated with `a` and
`b`.

The component theorem packages the same identity directly for the selected
real velocity.  No derivative commutation, temporal limit, or new estimate is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealSecondPartialBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- An ordered concrete second spatial partial of the selected real `Point3`
representative is the real part of the corresponding complex second Fréchet
coordinate evaluation. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_secondPartial_eq_re_secondFrechet_axes
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
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W t i)))
        x
      =
    (iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t i))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        (![h3FourierAxisDirection a, h3FourierAxisDirection b] :
          Fin 2 → H3FourierPoint3)).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : ScalarField3 :=
    h3SpectralScalarRealC1RepresentativeOnPoint3
      (W t i)

  have hf2 : SpatialC2 f := by
    unfold SpatialC2
    dsimp only [f, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
        2 hν U₀ hA hU₀ ht htR.le i

  have hPartial :
      spatial3.d a (spatial3.d b f) x
        =
      iteratedFDeriv ℝ 2 f x
        (![axisDirection a, axisDirection b] : Fin 2 → Point3) := by
    change
      partialDeriv a
          (fun y => partialDeriv b f y)
          x
        =
      iteratedFDeriv ℝ 2 f x
        (![axisDirection a, axisDirection b] : Fin 2 → Point3)
    exact
      hf2.secondPartial_eq_iteratedFDeriv_two_axes
        x a b

  have hBridge :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_secondFrechet_eval_eq_re
      hν U₀ hA hU₀ ht htR i x
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
      exact h3Point3ToFourierCLM_axisDirection a
    · change
        h3Point3ToFourierCLM (axisDirection b)
          =
        h3FourierAxisDirection b
      exact h3Point3ToFourierCLM_axisDirection b

  calc
    spatial3.d a (spatial3.d b f) x
        =
      iteratedFDeriv ℝ 2 f x
        (![axisDirection a, axisDirection b] : Fin 2 → Point3) :=
      hPartial

    _ =
      (iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative
            (W t i))
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
          (![h3FourierAxisDirection a, h3FourierAxisDirection b] :
            Fin 2 → H3FourierPoint3)).re := by
      dsimp only [f]
      rw [hDirections] at hBridge
      simpa only [
        W,
        h3Point3ToFourierCLM_apply
      ] using hBridge

/-- Velocity-component form of the ordered second-partial / second-Fréchet
bridge. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_secondPartial_eq_re_secondFrechet_axes
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
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀ t y).component j))
        x
      =
    (iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t (h3ClassicalizationFinOfAxis j)))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        (![h3FourierAxisDirection a, h3FourierAxisDirection b] :
          Fin 2 → H3FourierPoint3)).re := by
  dsimp only

  change
    spatial3.d a
        (spatial3.d b
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ t
              (h3ClassicalizationFinOfAxis j))))
        x
      =
    (iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t
            (h3ClassicalizationFinOfAxis j)))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        (![h3FourierAxisDirection a, h3FourierAxisDirection b] :
          Fin 2 → H3FourierPoint3)).re

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_secondPartial_eq_re_secondFrechet_axes
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)
      x a b

end

end Euclidean
end Bridge
end PrimeTensor

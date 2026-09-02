import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealSecondFrechetBridge

/-!
# Classicalization: selected real Point3 Hessian-trace bridge

The selected real temporal PDE has already been transported to `Point3`, and
the preceding increment transports the complete second Fréchet derivative from
the complex Fourier carrier to the real `Point3` representative.

The only remaining representation issue in the Laplacian term is the
coordinate direction itself.  This is exact: the Fourier-side direction was
defined to be

    WithLp.toLp 2 (axisDirection i),

which is precisely the image of the ordinary project coordinate direction
through `h3Point3ToFourierCLM`.

This file records that definitional equality, specializes the second-Fréchet
transport to repeated coordinate directions, sums the three diagonal entries,
and rewrites the real temporal PDE as

    ∂ₜ u = ν tr(D²_x u) - Re forcing

entirely on the ordinary `Point3` carrier.

No new estimate, regularity hypothesis, or derivative commutation is used.
The next increment can identify the repeated-direction second Fréchet terms
with the project's nested `spatial3.d` Laplacian.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealHessianTraceBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The canonical `Point3 → H3FourierPoint3` map sends an ordinary coordinate
unit vector to exactly the Fourier coordinate direction used by the spectral
PDE. -/
@[simp]
theorem h3Point3ToFourierCLM_axisDirection
    (i : PrimeTensor.Axis Depth.three) :
    h3Point3ToFourierCLM (axisDirection i)
      =
    h3FourierAxisDirection i := by
  rfl

/-- The diagonal second Fréchet derivative of the real `Point3`
representative, on one repeated ordinary coordinate direction, is the real
part of the corresponding complex Fourier-carrier diagonal derivative. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_secondFrechet_axisDirection_eq_re
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
    iteratedFDeriv ℝ 2
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W t i))
        x
        (fun _ : Fin 2 => axisDirection a)
      =
    (iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t i))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        (fun _ : Fin 2 =>
          h3FourierAxisDirection a)).re := by
  dsimp only

  simpa only [
    h3Point3ToFourierCLM_apply,
    h3FourierAxisDirection
  ] using
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_secondFrechet_eval_eq_re
      hν U₀ hA hU₀ ht htR i x
      (fun _ : Fin 2 => axisDirection a))

/-- The real part of the selected complex Hessian trace is exactly the
three-coordinate second-Fréchet trace of the real `Point3` representative. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedHessianTrace_re_eq_realPoint3SecondFrechetTrace
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∑ j : Fin 3,
      iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t i))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        (fun _ : Fin 2 =>
          h3FourierAxisDirection (h3AxisOfFin3 j))).re
      =
    ∑ j : Fin 3,
      iteratedFDeriv ℝ 2
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W t i))
        x
        (fun _ : Fin 2 =>
          axisDirection (h3AxisOfFin3 j)) := by
  dsimp only

  change
    Complex.reCLM
        (∑ j : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t i))
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 j)))
      =
    ∑ j : Fin 3,
      iteratedFDeriv ℝ 2
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t i))
        x
        (fun _ : Fin 2 =>
          axisDirection (h3AxisOfFin3 j))

  rw [map_sum]

  apply Finset.sum_congr rfl
  intro j _hj

  exact
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_secondFrechet_axisDirection_eq_re
      hν U₀ hA hU₀ ht htR i x
      (h3AxisOfFin3 j)).symm

/-- Scalar-coordinate real PDE form with the entire Hessian trace written on
the ordinary `Point3` carrier. -/
theorem temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_realPoint3SecondFrechetTrace_sub_forcing
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    temporal.d
      (fun s : ℝ =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (W s i) x)
      t
      =
    ν *
        (∑ j : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W t i))
            x
            (fun _ : Fin 2 =>
              axisDirection (h3AxisOfFin3 j)))
      -
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (W t) (W t) i x).re := by
  dsimp only

  rw [
    temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_re_selectedHessianTrace_sub_forcing
      hν U₀ hA hU₀ ht htR i x
  ]

  rw [Complex.sub_re, Complex.mul_re]

  simp only [
    Complex.ofReal_re,
    Complex.ofReal_im,
    zero_mul,
    sub_zero
  ]

  rw [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedHessianTrace_re_eq_realPoint3SecondFrechetTrace
      hν U₀ hA hU₀ ht htR i x
  ]

/-- Velocity-component form of the real `Point3` Hessian-trace PDE bridge. -/
theorem temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_eq_realPoint3SecondFrechetTrace_sub_forcing
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    temporal.d
      (fun s : ℝ =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hA hU₀ s x).component j)
      t
      =
    ν *
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W t (h3ClassicalizationFinOfAxis j)))
            x
            (fun _ : Fin 2 =>
              axisDirection (h3AxisOfFin3 k)))
      -
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (W t) (W t)
      (h3ClassicalizationFinOfAxis j) x).re := by
  dsimp only

  change
    temporal.d
      (fun s : ℝ =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s
            (h3ClassicalizationFinOfAxis j))
          x)
      t
      =
    ν *
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t
                (h3ClassicalizationFinOfAxis j)))
            x
            (fun _ : Fin 2 =>
              axisDirection (h3AxisOfFin3 k)))
      -
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t)
      (h3ClassicalizationFinOfAxis j) x).re

  exact
    temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_realPoint3SecondFrechetTrace_sub_forcing
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)
      x

end

end Euclidean
end Bridge
end PrimeTensor

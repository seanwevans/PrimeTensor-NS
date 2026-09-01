import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityTimeDerivativeSpatialC1
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealTemporalDerivativeRegularity
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Classicalization: real Point3 time derivative is spatially C¹

The complex selected time derivative is now spatially `C¹` on the Fourier
Euclidean carrier.  The mixed regularity frontier, however, is stated for the
ordinary real selected velocity on the project's `Point3` carrier.

This file is only representation transport.

* compose the complex spatially `C¹` derivative field with `WithLp.toLp`;
* take its real part through the continuous linear map `Complex.reCLM`;
* identify that resulting field with the ordinary derivative of the real
  selected representative by transporting the complex derivative's little-o
  remainder through the bound `|re z| ≤ ‖z‖`;
* package the result in the selected real velocity component notation.

Thus, at every strict positive interior restart time, the actual real temporal
derivative is a spatially `C¹` scalar field.  No new estimate or frontier
hypothesis is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealTimeDerivativeSpatialC1
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The ordinary time derivative of one selected real scalar representative,
transported to `Point3`, is spatially `C¹` at every strict positive interior
restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_timeDerivative_spatial_contDiff_one
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContDiff ℝ 1
      (fun x : Point3 =>
        deriv
          (fun s : ℝ =>
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (W s i) x)
          t) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let toLp : Point3 → H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3)

  let gC : H3FourierPoint3 → ℂ :=
    fun ξ =>
      deriv
        (fun s : ℝ =>
          h3SpectralScalarC1Representative
            (W s i) ξ)
        t

  have hComplex :
      ContDiff ℝ 1 gC := by
    dsimp only [gC, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_timeDerivative_spatial_contDiff_one
        hν U₀ hA hU₀ ht htR i

  have hToLp :
      ContDiff ℝ 1 toLp := by
    dsimp only [toLp]
    exact
      (PiLp.contDiff_toLp :
        ContDiff ℝ 1
          (WithLp.toLp 2 : Point3 → H3FourierPoint3))

  have hPull :
      ContDiff ℝ 1
        (fun x : Point3 => gC (toLp x)) := by
    exact hComplex.comp hToLp

  have hRealCandidate :
      ContDiff ℝ 1
        (fun x : Point3 => (gC (toLp x)).re) := by
    simpa only [
      Function.comp_apply,
      Complex.reCLM_apply
    ] using
      hPull.continuousLinearMap_comp Complex.reCLM

  have hEq :
      (fun x : Point3 =>
        deriv
          (fun s : ℝ =>
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (W s i) x)
          t)
        =
      (fun x : Point3 => (gC (toLp x)).re) := by
    funext x

    let fCtime : ℝ → ℂ :=
      fun s : ℝ =>
        h3SpectralScalarC1Representative
          (W s i) (toLp x)

    have hComplexBase :
        HasDerivAt
          fCtime
          (h3SpectralScalarHeatTimeGeneratorRepresentative
              ν t (U₀ i) (toLp x)
            -
            ((ν : ℂ) *
                (∑ j : Fin 3,
                  h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
                    ν t W W i (toLp x)
                    (h3FourierAxisDirection (h3AxisOfFin3 j))
                    (h3FourierAxisDirection (h3AxisOfFin3 j)))
              +
            h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i (toLp x)))
          t := by
      dsimp only [fCtime, W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_hasDerivAt_time
          hν U₀ hA hU₀ ht htR i (toLp x)

    have hComplexDeriv :
        HasDerivAt
          fCtime
          (deriv fCtime t)
          t :=
      hComplexBase.congr_deriv hComplexBase.deriv.symm

    have hRealDeriv :
        HasDerivAt
          (fun s : ℝ => (fCtime s).re)
          ((deriv fCtime t).re)
          t := by
      apply HasDerivAt.of_isLittleO

      have hReBigO :
          (fun s : ℝ =>
            (fCtime s - fCtime t -
              (s - t) • deriv fCtime t).re)
            =O[𝓝 t]
          (fun s : ℝ =>
            fCtime s - fCtime t -
              (s - t) • deriv fCtime t) := by
        exact
          (Asymptotics.isBigOWith_of_le
            (𝓝 t)
            (fun s => by
              simpa only [Real.norm_eq_abs] using
                Complex.abs_re_le_norm
                  (fCtime s - fCtime t -
                    (s - t) • deriv fCtime t))).isBigO

      have hReLittleO :
          (fun s : ℝ =>
            (fCtime s - fCtime t -
              (s - t) • deriv fCtime t).re)
            =o[𝓝 t]
          (fun s : ℝ => s - t) :=
        hReBigO.trans_isLittleO hComplexDeriv.isLittleO

      simpa only [
        Complex.sub_re,
        Complex.smul_re
      ] using hReLittleO

    dsimp only [gC, toLp]

    unfold
      h3SpectralScalarRealC1RepresentativeOnPoint3
      h3SpectralScalarRealC1Representative

    simpa only [fCtime] using hRealDeriv.deriv

  rw [hEq]
  exact hRealCandidate

/-- Velocity-component form: the actual temporal derivative of the selected
real restart velocity is spatially `C¹`. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_timeDerivative_spatial_contDiff_one
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (j : PrimeTensor.Axis Depth.three) :
    ContDiff ℝ 1
      (fun x : Point3 =>
        temporal.d
          (fun s : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀ s x).component j)
          t) := by
  change
    ContDiff ℝ 1
      (fun x : Point3 =>
        deriv
          (fun s : ℝ =>
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ s
                (h3ClassicalizationFinOfAxis j))
              x)
          t)

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_timeDerivative_spatial_contDiff_one
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)

end

end Euclidean
end Bridge
end PrimeTensor

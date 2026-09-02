import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityMixedDerivativeCandidateTimeContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealTimeDerivativeSpatialC1

/-!
# Classicalization: real Point3 temporal derivative in complex PDE form

The selected complex representative already satisfies the exact spatial PDE

    ∂ₜ uᶜ = ν tr(D²uᶜ) - Nᶜ(u,u).

The mixed-regularity frontier is written for the real `Point3` representative.
This file performs only that representation transport.

At a fixed ordinary spatial point `x`, the real selected representative is the
real part of the complex representative evaluated at `WithLp.toLp 2 x`.
Transporting the complex time derivative through `Complex.re` therefore gives
the exact real temporal derivative as the real part of the already-closed
complex PDE expression.

No spatial differentiation, derivative commutation, or new estimate occurs in
this increment.  The next layer can differentiate this field identity in the
project's concrete `spatial3.d` language and compare it directly with the
continuous mixed-derivative candidate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealTimeDerivativePDEBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Scalar-coordinate form: the actual real `Point3` temporal derivative is
the real part of the exact complex Hessian-trace-minus-forcing PDE expression.
-/
theorem temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_re_selectedHessianTrace_sub_forcing
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
    ((ν : ℂ) *
        (∑ j : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (W t i))
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 j)))
      -
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (W t) (W t) i x).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let xH : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let fCtime : ℝ → ℂ :=
    fun s : ℝ =>
      h3SpectralScalarC1Representative
        (W s i) xH

  have hComplexBase :
      HasDerivAt
        fCtime
        (h3SpectralScalarHeatTimeGeneratorRepresentative
            ν t (U₀ i) xH
          -
          ((ν : ℂ) *
              (∑ j : Fin 3,
                h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
                  ν t W W i xH
                  (h3FourierAxisDirection (h3AxisOfFin3 j))
                  (h3FourierAxisDirection (h3AxisOfFin3 j)))
            +
          h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i xH))
        t := by
    dsimp only [fCtime, xH, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_hasDerivAt_time
        hν U₀ hA hU₀ ht htR i
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

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

  have hPDE :
      deriv fCtime t
        =
      (ν : ℂ) *
          (∑ j : Fin 3,
            iteratedFDeriv ℝ 2
              (h3SpectralScalarC1Representative
                (W t i))
              xH
              (fun _ : Fin 2 =>
                h3FourierAxisDirection (h3AxisOfFin3 j)))
        -
      h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i xH := by
    dsimp only [fCtime]
    simpa only [W, xH] using
      deriv_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_eq_selectedHessianTrace_sub_forcing
        hν U₀ hA hU₀ ht htR i
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  change
    deriv
      (fun s : ℝ =>
        (fCtime s).re)
      t
      =
    ((ν : ℂ) *
        (∑ j : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (W t i))
            xH
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 j)))
      -
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (W t) (W t) i x).re

  rw [hRealDeriv.deriv, hPDE]

  unfold
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3

  rfl

/-- Velocity-component form of the same real `Point3` temporal PDE bridge. -/
theorem temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_eq_re_selectedHessianTrace_sub_forcing
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
    ((ν : ℂ) *
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (W t (h3ClassicalizationFinOfAxis j)))
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 k)))
      -
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
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
    ((ν : ℂ) *
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t
                (h3ClassicalizationFinOfAxis j)))
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 k)))
      -
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t)
      (h3ClassicalizationFinOfAxis j) x).re

  exact
    temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_re_selectedHessianTrace_sub_forcing
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)
      x

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealMixedDerivativeCandidateBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityFirstFrechetTimeDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Classicalization: time derivative of a selected real spatial partial

The selected complex first spatial Fréchet coordinate already has an ordinary
time derivative.  The preceding bridge identifies the real part of its
coefficient with the concrete real mixed-derivative PDE candidate, while the
selected real spatial-partial bridge identifies its path with `spatial3.d`.

This file combines those facts.

For a fixed scalar coordinate `i`, spatial coordinate `a`, and physical point
`x`, the concrete first spatial partial

    r ↦ ∂ₐ uᵢ(r,x)

has an ordinary time derivative at every strict positive interior restart time,
and that derivative is the actual spatial partial of the actual temporal
derivative,

    ∂ₐ(∂ₜ uᵢ)(t,x).

The proof does not invoke a general mixed-partial theorem.  Both orders are
identified with the same explicit PDE candidate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealSpatialPartialTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, the concrete real spatial
partial of one selected scalar coordinate has time derivative equal to the
concrete spatial partial of the actual temporal derivative. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_hasDerivAt_time
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
    HasDerivAt
      (fun r : ℝ =>
        spatial3.d
          (h3AxisOfFin3 a)
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r i))
          x)
      (spatial3.d
        (h3AxisOfFin3 a)
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i) y)
            t)
        x)
      t := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let xf : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let C : ℝ → ℂ :=
    fun r : ℝ =>
      (fderiv ℝ
          (h3SpectralScalarC1Representative
            (W r i))
          xf) ea

  let coefficient : ℂ :=
    (ν : ℂ) *
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
        xf) ea

  let P : ℝ → ℝ :=
    fun r : ℝ =>
      spatial3.d
        (h3AxisOfFin3 a)
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W r i))
        x

  have hComplex :
      HasDerivAt C coefficient t := by
    dsimp only [C, coefficient, W, xf, ea]
    exact
      h3SelectedVelocity_C1_fderiv_coordinate_hasDerivAt_time
        hν U₀ hA hU₀ ht htR i a
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  have hReal :
      HasDerivAt
        (fun r : ℝ => (C r).re)
        coefficient.re
        t := by
    change
      HasDerivAt
        (Complex.reCLM ∘ C)
        (Complex.reCLM coefficient)
        t
    exact
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt
        t hComplex

  have hWindow :
      Set.Ioo (0 : ℝ) R ∈ 𝓝 t := by
    apply Ioo_mem_nhds
    · exact ht
    · simpa only [R] using htR

  have hPathEq :
      P =ᶠ[𝓝 t]
        (fun r : ℝ => (C r).re) := by
    filter_upwards [hWindow] with r hr

    have hBridge :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_eq_re_firstFrechet
        hν U₀ hA hU₀
        hr.1
        (by
          simpa only [R] using hr.2)
        i x
        (h3AxisOfFin3 a)

    dsimp only at hBridge
    dsimp only [P, C, W, xf, ea]
    exact hBridge

  have hSpatialRaw :
      HasDerivAt
        P
        coefficient.re
        t :=
    hReal.congr_of_eventuallyEq hPathEq

  have hCandidate :
      coefficient.re
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
    dsimp only [coefficient, W, xf, ea]
    exact
      h3SelectedVelocity_C1_fderiv_coordinate_timeDerivativeCandidate_re_eq_mixedDerivativeCandidate
        hν U₀ hA hU₀ ht htR i a x

  have hPDE :=
    spatial_d_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_mixedDerivativeCandidate
      hν U₀ hA hU₀ ht htR i x
      (h3AxisOfFin3 a)

  dsimp only at hPDE

  have hCoefficient :
      coefficient.re
        =
      spatial3.d
        (h3AxisOfFin3 a)
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i) y)
            t)
        x := by
    exact hCandidate.trans hPDE.symm

  have hSpatial :
      HasDerivAt
        P
        (spatial3.d
          (h3AxisOfFin3 a)
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W r i) y)
              t)
          x)
        t :=
    hSpatialRaw.congr_deriv hCoefficient

  dsimp only [P, W] at hSpatial ⊢
  exact hSpatial

end

end Euclidean
end Bridge
end PrimeTensor

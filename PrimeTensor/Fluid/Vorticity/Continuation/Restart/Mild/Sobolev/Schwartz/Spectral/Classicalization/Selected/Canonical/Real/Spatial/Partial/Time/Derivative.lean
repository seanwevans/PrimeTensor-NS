import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Canonical.Real.Mixed.Derivative.Candidate.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Canonical.First.Frechet.Time.Derivative
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Classicalization: time derivative of a canonical real spatial partial

The canonical reconstruction now has all three ingredients needed to recover the
actual real mixed derivative at order one:

* its fixed first spatial Frechet coordinate has the explicit Navier--Stokes
  time derivative coefficient;
* the concrete real spatial partial is the real part of that canonical first
  Frechet coordinate;
* the real part of the canonical coefficient is exactly the concrete
  mixed-derivative PDE candidate.

The existing selected real PDE theorem already identifies that candidate with

    partial_a (partial_t u_i)(t,x).

Combining these facts gives an ordinary time derivative for the concrete real
spatial partial along the canonical physical extension:

    d/dt (partial_a u_i)(t,x) = partial_a (partial_t u_i)(t,x).

No general mixed-partial theorem, new derivative interchange, or new estimate is
used.  The only transport back to the historical selected branch is through the
exact equality of the two physical extensions when invoking the already-proved
real PDE identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalRealSpatialPartialTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, the concrete real spatial
partial of one selected scalar coordinate along the canonical physical
extension has time derivative equal to the concrete spatial partial of the
actual temporal derivative. -/
theorem h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_realC1RepresentativeOnPoint3_spatial_d_hasDerivAt_time
    {nu A t : ℝ}
    (hnu : 0 < nu)
    (U0 : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU0 : ‖U0‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius nu A)
    (i a : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hnu U0 hA hU0
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
    h3FinHeatLerayRestartRadius nu A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hnu U0 hA hU0

  let xf : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let C : ℝ → ℂ :=
    fun r : ℝ =>
      (fderiv ℝ
          (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
            hnu U0 hA hU0 r i)
          xf) ea

  let coefficient : ℂ :=
    (nu : ℂ) *
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 3
            (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
              hnu U0 hA hU0 t i)
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
      h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_fderiv_coordinate_hasDerivAt_time
        hnu U0 hA hU0 ht htR i a
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
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_realC1RepresentativeOnPoint3_spatial_d_eq_re_canonical_firstFrechet
        hnu U0 hA hU0
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
      nu *
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
      h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_timeDerivativeCandidate_re_eq_mixedDerivativeCandidate
        hnu U0 hA hU0 ht htR i a x

  have hPDE :=
    spatial_d_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_mixedDerivativeCandidate
      hnu U0 hA hU0 ht htR i x
      (h3AxisOfFin3 a)

  dsimp only at hPDE

  have hPhysicalExtension :
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
          hnu U0 hA hU0
        =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hnu U0 hA hU0 :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_eq_mildSolutionAtRestartRadiusPhysicalExtension
      hnu U0 hA hU0

  rw [← hPhysicalExtension] at hPDE

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

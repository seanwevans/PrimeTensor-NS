import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealSpatialPDEForm
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityMixedDerivativeCandidateTimeContinuity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Classicalization: spatial derivative of the selected temporal PDE

The selected real temporal derivative is now known pointwise in the concrete
Euclidean language:

    ∂ₜ uᵢ
      =
    ν * Σₖ ∂ₖ∂ₖ uᵢ
      - Re Nᵢ(u,u).

At every strict positive interior restart time,

* `uᵢ` is spatially `C³`, so each diagonal second partial is spatially `C¹`;
* the instantaneous real forcing is spatially `C¹`.

Hence the right-hand side may be differentiated once along any ordinary
coordinate line.  This file performs exactly that differentiation and proves

    ∂ₐ(∂ₜ uᵢ)
      =
    ν * Σₖ ∂ₐ∂ₖ∂ₖ uᵢ
      - ∂ₐ Re Nᵢ(u,u).

The right-hand side is precisely the mixed-derivative candidate whose time
continuity was already proved.

No derivative commutation is used: the third partial order remains
`a, k, k`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocitySpatialTemporalDerivativePDEForm
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- A spatially `C¹` field restricted to a coordinate line has derivative equal
to the project's concrete spatial partial. -/
theorem SpatialC1.hasDerivAt_coordinateLine_spatial_d
    {f : ScalarField3}
    (hf : SpatialC1 f)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun r : ℝ => f (coordinateLine x a r))
      (spatial3.d a f x)
      (x a) := by
  have hDiff :
      DifferentiableAt ℝ f x :=
    hf.differentiable_one.differentiableAt

  have hComp :
      HasDerivAt
        (f ∘ coordinateLine x a)
        ((fderiv ℝ f x) (axisDirection a))
        (x a) :=
    hDiff.hasFDerivAt.comp_hasDerivAt_of_eq
      (x a)
      (coordinateLine_hasDerivAt x a)
      (coordinateLine_at_base x a).symm

  have hValue :
      (fderiv ℝ f x) (axisDirection a)
        =
      spatial3.d a f x := by
    change
      (fderiv ℝ f x) (axisDirection a)
        =
      partialDeriv a f x
    exact
      (hf.partialDeriv_eq_fderiv_axisDirection
        x a).symm

  have hComp' :
      HasDerivAt
        (f ∘ coordinateLine x a)
        (spatial3.d a f x)
        (x a) :=
    hComp.congr_deriv hValue

  change
    HasDerivAt
      (f ∘ coordinateLine x a)
      (spatial3.d a f x)
      (x a)

  exact hComp'

/-- Scalar-coordinate form: the actual spatial partial of the actual temporal
derivative equals the already-isolated mixed-derivative PDE candidate. -/
theorem spatial_d_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_mixedDerivativeCandidate
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
        temporal.d
          (fun s : ℝ =>
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (W s i) y)
          t)
      x
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d a
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W t i))))
            x)
      -
    spatial3.d
      a
      (fun y : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t) i y).re)
      x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let u : ScalarField3 :=
    h3SpectralScalarRealC1RepresentativeOnPoint3
      (W t i)

  let F : ScalarField3 :=
    fun y : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i y).re

  let T : ScalarField3 :=
    fun y : Point3 =>
      temporal.d
        (fun s : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s i) y)
        t

  have huC3 : SpatialC3 u := by
    unfold SpatialC3
    dsimp only [u, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
        3 hν U₀ hA hU₀ ht htR.le i

  have hFC1 : SpatialC1 F := by
    unfold SpatialC1
    dsimp only [F, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_one
        hν U₀ hA hU₀ ht htR.le i

  have hField :
      T
        =
      (fun y : Point3 =>
        ν *
            (∑ k : Fin 3,
              spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  u)
                y)
          -
        F y) := by
    funext y
    dsimp only [T, u, F]
    simpa only [W] using
      temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_spatialLaplacian_sub_forcing
        hν U₀ hA hU₀ ht htR i y

  have hTermC1
      (k : Fin 3) :
      SpatialC1
        (spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            u)) :=
    huC3.secondPartial_spatialC1
      (h3AxisOfFin3 k)
      (h3AxisOfFin3 k)

  have hTrace :
      HasDerivAt
        (fun r : ℝ =>
          ∑ k : Fin 3,
            spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                u)
              (coordinateLine x a r))
        (∑ k : Fin 3,
          spatial3.d a
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                u))
            x)
        (x a) := by
    apply HasDerivAt.fun_sum
    intro k _hk
    exact
      (hTermC1 k).hasDerivAt_coordinateLine_spatial_d
        x a

  have hForce :=
    hFC1.hasDerivAt_coordinateLine_spatial_d x a

  have hTraceDeriv :
      deriv
        (fun r : ℝ =>
          ∑ k : Fin 3,
            spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                u)
              (coordinateLine x a r))
        (x a)
      =
    ∑ k : Fin 3,
      spatial3.d a
        (spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            u))
        x :=
    hTrace.deriv

  have hForceDeriv :
      deriv
        (fun r : ℝ =>
          F (coordinateLine x a r))
        (x a)
      =
    spatial3.d a F x :=
    hForce.deriv

  change
    spatial3.d a T x
      =
    ν *
          (∑ k : Fin 3,
            spatial3.d a
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  u))
              x)
      -
    spatial3.d a F x

  rw [hField]

  change
    partialDeriv a
        (fun y : Point3 =>
          ν *
              (∑ k : Fin 3,
                spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    u)
                  y)
            -
          F y)
        x
      =
    ν *
          (∑ k : Fin 3,
            spatial3.d a
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  u))
              x)
      -
    spatial3.d a F x

  unfold partialDeriv

  change
    deriv
        ((fun r : ℝ =>
            ν *
              (∑ k : Fin 3,
                spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    u)
                  (coordinateLine x a r)))
          -
        (fun r : ℝ =>
          F (coordinateLine x a r)))
        (x a)
      =
    ν *
          (∑ k : Fin 3,
            spatial3.d a
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  u))
              x)
      -
    spatial3.d a F x

  rw [
    deriv_sub
      (hTrace.differentiableAt.const_mul ν)
      hForce.differentiableAt,
    deriv_const_mul ν hTrace.differentiableAt,
    hTraceDeriv,
    hForceDeriv
  ]

/-- Velocity-component form of the same spatially differentiated temporal PDE.
This is the pointwise identification needed to transfer the already-proved
candidate time continuity to the actual mixed derivative. -/
theorem spatial_d_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_eq_mixedDerivativeCandidate
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d
      a
      (fun y : Point3 =>
        temporal.d
          (fun s : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀ s y).component j)
          t)
      x
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d a
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (fun y : Point3 =>
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                    hν U₀ hA hU₀ t y).component j)))
            x)
      -
    spatial3.d
      a
      (fun y : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t)
          (h3ClassicalizationFinOfAxis j) y).re)
      x := by
  dsimp only

  change
    spatial3.d
      a
      (fun y : Point3 =>
        temporal.d
          (fun s : ℝ =>
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ s
                (h3ClassicalizationFinOfAxis j))
              y)
          t)
      x
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d a
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ t
                    (h3ClassicalizationFinOfAxis j)))))
            x)
      -
    spatial3.d
      a
      (fun y : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t)
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t)
          (h3ClassicalizationFinOfAxis j) y).re)
      x

  exact
    spatial_d_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_mixedDerivativeCandidate
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)
      x a

end

end Euclidean
end Bridge
end PrimeTensor

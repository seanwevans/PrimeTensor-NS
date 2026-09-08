import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Integrable
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Classical.Overlap
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Pointwise.Velocity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.C1.Point.Evaluation.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Point3Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.F.Deriv.Coordinate.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Vorticity.Flux

/-!
# Uniform H³ pointwise envelopes for the old endpoint velocity and first jet

The vorticity Fubini reduction has reached a scalar spatial norm-mass estimate.
The nonlinear part of the pressure-free vorticity RHS contains first spatial
derivatives of advection,

    ∂ₐ ((u · ∇)u_j),

whose `L²` estimate uses the standard split

    (∂ₐu · ∇)u_j + u · ∇(∂ₐu_j).

The H³ tail already controls every first and second derivative in `L²`.
What remains for that product estimate is a uniform pointwise bound on

* the velocity itself;
* every first spatial derivative.

This file derives those two envelopes without introducing any new Sobolev
theorem.  Every genuine endpoint slice is the canonical weighted H³ encoding
of the old preterminal velocity.  The canonical real `C¹` representative is
pointwise equal to the old velocity, while the existing Fourier deweighting
bounds give

    |u_j(x)|       ≤ C₀ ‖U‖,
    |∂ₐu_j(x)|    ≤ C₁ ‖U‖.

The retained tail energy bounds the endpoint spectral state by `2E`, uniformly
over the closed elapsed interval.

No temporal regularity, pressure regularity, or mild equation is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Zero-order real point evaluation of one scalar H³ state is bounded by the
existing raw-Fourier deweighting coefficient. -/
theorem norm_h3SpectralScalarRealC1RepresentativeOnPoint3_apply_le
    (G : H3SpectralScalarState)
    (x : Point3) :
    ‖h3SpectralScalarRealC1RepresentativeOnPoint3 G x‖
      ≤
    h3RawFourierL1DeweightingCoefficient * ‖G‖ := by
  let xH : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let z : ℂ :=
    h3SpectralScalarC1Representative G xH

  have hRe :
      ‖z.re‖ ≤ ‖z‖ := by
    simpa [Real.norm_eq_abs] using
      Complex.abs_re_le_norm z

  have hComplex :
      ‖z‖
        ≤
      h3RawFourierL1DeweightingCoefficient * ‖G‖ := by
    dsimp only [z, xH]
    exact
      norm_h3SpectralScalarC1Representative_apply_le
        G
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  change
    ‖(h3SpectralScalarC1Representative
        G
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re‖
      ≤
    h3RawFourierL1DeweightingCoefficient * ‖G‖

  exact hRe.trans hComplex

/-- First spatial point evaluation of one scalar H³ state is bounded by the
existing first-moment deweighting coefficient. -/
theorem norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : Point3) :
    ‖spatial3.d
        (h3AxisOfFin3 i)
        (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
        x‖
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * ‖G‖ := by
  rw [
    h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
  ]

  let xH : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let z : ℂ :=
    FourierTransformInv.fourierInv
      (h3SpectralScalarRawFourierCoordinateDerivative G i)
      xH

  have hRe :
      ‖z.re‖ ≤ ‖z‖ := by
    simpa [Real.norm_eq_abs] using
      Complex.abs_re_le_norm z

  have hComplex :
      ‖z‖
        ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * ‖G‖ := by
    have h :=
      norm_h3SpectralScalarC1Representative_fderiv_apply_fin_le
        G i xH
    rw [
      h3SpectralScalarC1Representative_fderiv_apply_fin
    ] at h
    simpa only [z] using h

  exact hRe.trans hComplex

/-- Every bounded endpoint-canonical spectral slice has norm at most `2E`. -/
theorem norm_h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_apply_le_twoE
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint q‖
      ≤
    2 * E := by
  rw [
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_apply
  ]

  exact
    norm_h3PreterminalCanonicalSpectralStateOnElapsed_le_twoA
      hNS
      ht
      hEnd
      hE
      (canonicalH3TailDataFrom_integrableOnElapsed
        hEnd hTail)
      (canonicalH3TailDataFrom_energyOnElapsed_le_twoE
        hE hEnd hTail)
      q

/-- Every scalar coordinate of an endpoint-canonical spectral slice is bounded
by the same `2E` ceiling. -/
theorem norm_h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_component_le_twoE
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    ‖(h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint q) i‖
      ≤
    2 * E := by
  exact
    (h3SpectralFinVector_coordinate_norm_le
      (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint q)
      i).trans
      (norm_h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_apply_le_twoE
        hNS ht hEnd hE hTail hEndpoint q)

/-- Uniform pointwise bound for every old logged velocity component on the
closed elapsed interval. -/
theorem norm_loggedVelocityComponent_le_endpointH3Envelope
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    ‖loggedVelocityComponent
        u (t + (q : ℝ)) j x‖
      ≤
    h3RawFourierL1DeweightingCoefficient * (2 * E) := by
  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  have hOld :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          ((P q) i) x
        =
      loggedVelocityComponent
        u (t + (q : ℝ)) j x := by
    have hFunctions :=
      h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_component_eq_old
        hNS ht hEnd hE hTail hEndpoint q i

    have hx := congrFun hFunctions x

    simpa only [
      P,
      i,
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using hx

  have hRep :
      ‖h3SpectralScalarRealC1RepresentativeOnPoint3
          ((P q) i) x‖
        ≤
      h3RawFourierL1DeweightingCoefficient * ‖(P q) i‖ :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_apply_le
      ((P q) i) x

  have hCoord :
      ‖(P q) i‖ ≤ 2 * E := by
    dsimp only [P]
    exact
      norm_h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_component_le_twoE
        hNS ht hEnd hE hTail hEndpoint q i

  rw [← hOld]

  exact
    hRep.trans
      (mul_le_mul_of_nonneg_left
        hCoord
        h3RawFourierL1DeweightingCoefficient_nonneg)

/-- Uniform pointwise bound for every first spatial derivative of every old
logged velocity component on the closed elapsed interval. -/
theorem norm_loggedVelocityComponent_spatial_d_le_endpointH3Envelope
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (a j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    ‖spatial3.d
        a
        (loggedVelocityComponent
          u (t + (q : ℝ)) j)
        x‖
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      (2 * E) := by
  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis a

  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  have hOld :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          ((P q) i)
        =
      loggedVelocityComponent
        u (t + (q : ℝ)) j := by
    have hFunctions :=
      h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_component_eq_old
        hNS ht hEnd hE hTail hEndpoint q i

    simpa only [
      P,
      i,
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using hFunctions

  have hDerivEq :
      spatial3.d
          a
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            ((P q) i))
          x
        =
      spatial3.d
          a
          (loggedVelocityComponent
            u (t + (q : ℝ)) j)
          x := by
    exact
      congrArg
        (fun f : Point3 → ℝ =>
          spatial3.d a f x)
        hOld

  have hRep :
      ‖spatial3.d
          a
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            ((P q) i))
          x‖
        ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖(P q) i‖ := by
    have h :=
      norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
        ((P q) i) k x

    rw [
      h3AxisOfFin3_h3ClassicalizationFinOfAxis a
    ] at h

    exact h

  have hCoord :
      ‖(P q) i‖ ≤ 2 * E := by
    dsimp only [P]
    exact
      norm_h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_component_le_twoE
        hNS ht hEnd hE hTail hEndpoint q i

  rw [← hDerivEq]

  exact
    hRep.trans
      (mul_le_mul_of_nonneg_left
        hCoord
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg)

end

end Euclidean
end Bridge
end PrimeTensor

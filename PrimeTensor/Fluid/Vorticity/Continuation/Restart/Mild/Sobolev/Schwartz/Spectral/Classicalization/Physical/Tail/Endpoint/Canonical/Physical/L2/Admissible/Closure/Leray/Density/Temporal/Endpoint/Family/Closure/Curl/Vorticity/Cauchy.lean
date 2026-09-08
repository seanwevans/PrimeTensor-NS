import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.RHSExpansion
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Velocity.Pairing.Continuity
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Cauchy--Schwarz bridge for endpoint vorticity mass estimates

`RHSExpansion` reduces the pressure-free vorticity right-hand side to products
of old velocity derivatives.  `SquareBound` supplies uniform spatial square
bounds for every derivative through order three.

This file packages the only generic analytic step needed to turn those square
bounds into compact-test `L¹` bounds: Cauchy--Schwarz against a fixed weak test.

For a compact smooth test `ψ` and a scalar field `f` with

    ∫ f² ≤ M,

we prove

    ∫ ‖ψ‖ ‖f‖
      ≤ ‖ψ‖₂ M^(1/2).

The theorem is stated directly in terms of `SpatialL2SquareBound`, so later
nonlinear estimates only have to supply a pointwise endpoint envelope for one
factor and one square bound for the other.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityCauchy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityCauchy :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Real `L²` mass of a compactly supported smooth weak test. -/
noncomputable def h3WeakTestFunctionL2Mass
    (ψ : H3WeakTestFunction) : ℝ :=
  (∫ x : Point3, ‖ψ x‖ ^ (2 : ℝ) ∂volume) ^
    (1 / (2 : ℝ))

theorem h3WeakTestFunctionL2Mass_nonneg
    (ψ : H3WeakTestFunction) :
    0 ≤ h3WeakTestFunctionL2Mass ψ := by
  unfold h3WeakTestFunctionL2Mass
  positivity

/-- A square-bound plus strong measurability gives the corresponding `L²`
membership. -/
theorem memLp_two_of_spatialL2SquareBound
    {f : ScalarField3}
    {M : ℝ}
    (hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure Point3))
    (hBound : SpatialL2SquareBound f M) :
    MemLp
      f
      2
      (volume : Measure Point3) := by
  rw [memLp_two_iff_integrable_sq_norm hfMeas]
  simpa only [
    Real.norm_eq_abs,
    sq_abs
  ] using hBound.1

/-- Cauchy--Schwarz against a compact weak test, normalized by a
`SpatialL2SquareBound`. -/
theorem integral_weakTest_norm_mul_norm_le_of_spatialL2SquareBound
    (ψ : H3WeakTestFunction)
    {f : ScalarField3}
    {M : ℝ}
    (hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure Point3))
    (hBound : SpatialL2SquareBound f M) :
    (∫ x : Point3,
        ‖ψ x‖ * ‖f x‖
      ∂volume)
      ≤
    h3WeakTestFunctionL2Mass ψ *
      M ^ (1 / (2 : ℝ)) := by
  have hψ :
      MemLp
        (ψ : Point3 → ℝ)
        (ENNReal.ofReal 2)
        (volume : Measure Point3) :=
    ψ.continuous.memLp_of_hasCompactSupport
      ψ.hasCompactSupport

  have hfTwo :
      MemLp
        f
        2
        (volume : Measure Point3) :=
    memLp_two_of_spatialL2SquareBound
      hfMeas hBound

  have hf :
      MemLp
        f
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    simpa using hfTwo

  have hHolder :
      (∫ x : Point3,
          ‖ψ x‖ * ‖f x‖
        ∂volume)
        ≤
      (∫ x : Point3,
          ‖ψ x‖ ^ (2 : ℝ)
        ∂volume) ^ (1 / (2 : ℝ))
        *
      (∫ x : Point3,
          ‖f x‖ ^ (2 : ℝ)
        ∂volume) ^ (1 / (2 : ℝ)) := by
    exact
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
        Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall
          (fun x : Point3 => norm_nonneg (ψ x)))
        (Filter.Eventually.of_forall
          (fun x : Point3 => norm_nonneg (f x)))
        hψ.norm
        hf.norm

  have hSqLe :
      (∫ x : Point3,
          ‖f x‖ ^ (2 : ℝ)
        ∂volume)
        ≤
      M := by
    simpa only [
      Real.norm_eq_abs,
      Real.rpow_two,
      sq_abs
    ] using hBound.2

  have hSqNonneg :
      0 ≤
        ∫ x : Point3,
          ‖f x‖ ^ (2 : ℝ)
        ∂volume := by
    exact integral_nonneg
      (fun x : Point3 => by positivity)

  have hRoot :
      (∫ x : Point3,
          ‖f x‖ ^ (2 : ℝ)
        ∂volume) ^ (1 / (2 : ℝ))
        ≤
      M ^ (1 / (2 : ℝ)) := by
    exact
      Real.rpow_le_rpow
        hSqNonneg
        hSqLe
        (by norm_num)

  unfold h3WeakTestFunctionL2Mass
  exact
    hHolder.trans
      (mul_le_mul_of_nonneg_left
        hRoot
        (by positivity))

end

end Euclidean
end Bridge
end PrimeTensor

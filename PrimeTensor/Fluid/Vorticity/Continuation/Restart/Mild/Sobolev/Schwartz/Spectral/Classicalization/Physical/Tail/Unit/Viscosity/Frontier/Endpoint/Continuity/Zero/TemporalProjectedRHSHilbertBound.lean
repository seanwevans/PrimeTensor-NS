import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalProjectedRHSIncrementBound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Defect.Orthogonality

/-!
# Zeroth-order endpoint continuity: Hilbert-norm weak increment bound

`TemporalProjectedRHSIncrementBound` controls the old divergence-free weak
velocity increment by

    (sum_i ‖phi_i‖_2) * C(E) * q.

The density/duality step should instead see the native finite physical
`PiLp 2` Hilbert norm.  For three coordinates each coordinate norm is bounded
by the product norm, hence

    sum_i ‖phi_i‖_2
      <=
    3 * ‖Phi‖,

where `Phi = h3WeakTestVectorPhysicalL2Hilbert phi`.

This file records that finite-dimensional norm comparison and inserts it into
the weak velocity-increment estimate.  The result is a genuine bounded
functional estimate in the Hilbert norm, ready for extension from compact
smooth divergence-free tests to their closed span.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroProjectedRHSWeakHilbertBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The coordinate-summed scalar `L²` norm used by the preceding weak estimate
is bounded by three times the native physical `PiLp 2` Hilbert norm. -/
theorem h3WeakTestVectorPhysicalL2L1Norm_le_three_mul_norm
    (φ : H3WeakTestVector) :
    h3WeakTestVectorPhysicalL2L1Norm φ
      ≤
    3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖ := by
  unfold h3WeakTestVectorPhysicalL2L1Norm

  have hCoord
      (i : Fin 3) :
      ‖h3WeakTestFunctionPhysicalL2 (φ i)‖
        ≤
      ‖h3WeakTestVectorPhysicalL2Hilbert φ‖ := by
    simpa only [
      h3WeakTestVectorPhysicalL2Hilbert,
      PiLp.toLp_apply
    ] using
      (PiLp.norm_apply_le
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        i)

  calc
    (∑ i : Fin 3,
      ‖h3WeakTestFunctionPhysicalL2 (φ i)‖)
        ≤
      ∑ i : Fin 3,
        ‖h3WeakTestVectorPhysicalL2Hilbert φ‖ := by
      exact
        Finset.sum_le_sum
          (fun i hi => hCoord i)
    _ =
      3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖ := by
      simp

/-- Hilbert-norm form of the old divergence-free weak velocity-increment
estimate.  The only analytic hypothesis beyond the old preterminal solution is
the explicit pressure-defect mass frontier used to justify the Fubini step. -/
theorem norm_h3PreterminalLoggedVelocity_weakPairingDifference_le_three_mul_hilbertNorm_of_pressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hPressure :
      H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail φ) :
    ‖∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume‖
      ≤
    ((3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)
      *
    h3UnitViscosityZeroRHSBound E)
      *
    q := by
  have hWeak :=
    norm_h3PreterminalLoggedVelocity_weakPairingDifference_le_of_pressureDefect
      hNS ht hEnd hE hTail φ hφ hq hPressure

  have hTest :=
    h3WeakTestVectorPhysicalL2L1Norm_le_three_mul_norm φ

  have hRHSNonneg :
      0 ≤ h3UnitViscosityZeroRHSBound E :=
    h3UnitViscosityZeroRHSBound_nonneg hE

  calc
    ‖∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume‖
        ≤
      (h3WeakTestVectorPhysicalL2L1Norm φ
        *
      h3UnitViscosityZeroRHSBound E)
        *
      q :=
      hWeak
    _ ≤
      ((3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      q := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            hTest
            hRHSNonneg)
          hq.1

end

end Euclidean
end Bridge
end PrimeTensor

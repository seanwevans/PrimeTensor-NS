import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2HeatMovingTime

/-!
# Physical L² temporal admissibility: vector unit-heat quotient

The scalar quotient-safe heat-generator convergence is already proved by
dominated convergence.  The interaction-picture argument is cleaner if that
result is packaged once for the full three-component raw Fourier `L²` state.

For weighted H³ velocity data `U`, define

    Q₁(h,U)
      = h⁻¹ • (S₁(h) raw(U) - raw(U)).

Coordinatewise this is exactly the scalar quotient already controlled in
`FourierL2HeatGeneratorConvergence`.  Therefore, as `h → 0+`,

    Q₁(h,U) → A₁(U),

where `A₁` is the unit-viscosity raw Fourier generator vector.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatVectorQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Three-component unit-viscosity raw Fourier heat difference quotient. -/
noncomputable def h3RawFourierL2UnitHeatVectorQuotientState
    (h : ℝ)
    (U : H3SpectralFinVectorState) :
    H3RawFourierL2FinVectorState :=
  h⁻¹ •
    (h3RawFourierL2HeatApplyNN
        1 zero_le_one
        (Real.toNNReal h)
        (h3SpectralFinVectorRawFourierL2 U)
      -
     h3SpectralFinVectorRawFourierL2 U)

/-- Each coordinate of the vector quotient is literally the scalar quotient. -/
@[simp]
theorem h3RawFourierL2UnitHeatVectorQuotientState_apply
    (h : ℝ)
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFourierL2UnitHeatVectorQuotientState
        h U i
      =
    h3RawFourierL2HeatQuotientState
      1 h zero_le_one (U i) := by
  rfl

/-- The full vector unit-heat quotient converges strongly from the right to the
unit-viscosity generator vector. -/
theorem tendsto_h3RawFourierL2UnitHeatVectorQuotientState_zero_right
    (U : H3SpectralFinVectorState) :
    Tendsto
      (fun h : ℝ =>
        h3RawFourierL2UnitHeatVectorQuotientState
          h U)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3RawFourierL2UnitGeneratorStateVector U)) := by
  rw [tendsto_pi_nhds]
  intro i

  simpa only [
    h3RawFourierL2UnitHeatVectorQuotientState_apply,
    h3RawFourierL2UnitGeneratorStateVector_apply
  ] using
    tendsto_h3RawFourierL2HeatQuotientState_zero_right
      1 zero_le_one (U i)

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Heat.Quotient.Vector
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Physical L² temporal admissibility: interaction-picture slope algebra

Fix a final time `q`.  For a raw Fourier `L²` path `D`, consider

    I(r) = S₁(q-r) D(r)

on the region `r < q`.

For `s < y < q`, let `h = y-s` and `r = q-y`.  Since

    q-s = h + r

and the quotient-safe heat action is a semigroup,

    S₁(q-s) = S₁(r) S₁(h).

Therefore the interaction slope factors exactly as

    slope I s y
      =
    S₁(q-y)
      (slope D s y - Q₁(y-s,U)),

provided `D(s)` is the raw deweighting of the weighted H³ state `U`.

This is pure semigroup/module algebra.  The next file will take limits and
perform the generator cancellation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatInteractionSlope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact slope factorization for the unit-heat interaction picture. -/
theorem h3RawFourierL2UnitHeatInteractionSlope_eq
    {q s y : ℝ}
    (hsq : s < q)
    (hsy : s < y)
    (hyq : y < q)
    (U : H3SpectralFinVectorState)
    (D : ℝ → H3RawFourierL2FinVectorState)
    (hDs :
      D s =
        h3SpectralFinVectorRawFourierL2 U) :
    slope
        (fun r : ℝ =>
          h3RawFourierL2HeatApplyNN
            1 zero_le_one
            (Real.toNNReal (q - r))
            (D r))
        s y
      =
    h3RawFourierL2HeatApplyNN
      1 zero_le_one
      (Real.toNNReal (q - y))
      (slope D s y -
        h3RawFourierL2UnitHeatVectorQuotientState
          (y - s) U) := by
  have hys : 0 ≤ y - s :=
    sub_nonneg.mpr hsy.le

  have hqy : 0 ≤ q - y :=
    sub_nonneg.mpr hyq.le

  have hqs : 0 ≤ q - s :=
    sub_nonneg.mpr hsq.le

  have hTime :
      Real.toNNReal (q - s)
        =
      Real.toNNReal (y - s) +
        Real.toNNReal (q - y) := by
    apply NNReal.eq
    calc
      (Real.toNNReal (q - s) : ℝ)
          = q - s := by
            exact Real.coe_toNNReal (q - s) hqs
      _ =
        (y - s) + (q - y) := by
          ring
      _ =
        (Real.toNNReal (y - s) : ℝ) +
          (Real.toNNReal (q - y) : ℝ) := by
            rw [
              Real.coe_toNNReal (y - s) hys,
              Real.coe_toNNReal (q - y) hqy
            ]
      _ =
        ((Real.toNNReal (y - s) +
            Real.toNNReal (q - y) : ℝ≥0) : ℝ) := by
          rw [NNReal.coe_add]

  have hSemigroup :
      h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Real.toNNReal (q - s))
          (D s)
        =
      h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Real.toNNReal (q - y))
          (h3RawFourierL2HeatApplyNN
            1 zero_le_one
            (Real.toNNReal (y - s))
            (D s)) := by
    rw [hTime]
    exact
      h3RawFourierL2HeatApplyNN_add_time
        1 zero_le_one
        (Real.toNNReal (y - s))
        (Real.toNNReal (q - y))
        (D s)

  rw [slope_def_module]

  rw [hSemigroup]

  have hMapSub :
      h3RawFourierL2HeatApplyNN
            1 zero_le_one
            (Real.toNNReal (q - y))
            (D y)
          -
        h3RawFourierL2HeatApplyNN
            1 zero_le_one
            (Real.toNNReal (q - y))
            (h3RawFourierL2HeatApplyNN
              1 zero_le_one
              (Real.toNNReal (y - s))
              (D s))
        =
      h3RawFourierL2HeatApplyNN
        1 zero_le_one
        (Real.toNNReal (q - y))
        (D y -
          h3RawFourierL2HeatApplyNN
            1 zero_le_one
            (Real.toNNReal (y - s))
            (D s)) := by
    change
      h3RawFourierL2HeatCLM
            1 zero_le_one
            (Real.toNNReal (q - y))
            (D y)
          -
        h3RawFourierL2HeatCLM
            1 zero_le_one
            (Real.toNNReal (q - y))
            (h3RawFourierL2HeatApplyNN
              1 zero_le_one
              (Real.toNNReal (y - s))
              (D s))
        =
      h3RawFourierL2HeatCLM
        1 zero_le_one
        (Real.toNNReal (q - y))
        (D y -
          h3RawFourierL2HeatApplyNN
            1 zero_le_one
            (Real.toNNReal (y - s))
            (D s))
    rw [map_sub]

  rw [hMapSub]

  have hMapSmul :
      (y - s)⁻¹ •
        h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Real.toNNReal (q - y))
          (D y -
            h3RawFourierL2HeatApplyNN
              1 zero_le_one
              (Real.toNNReal (y - s))
              (D s))
        =
      h3RawFourierL2HeatApplyNN
        1 zero_le_one
        (Real.toNNReal (q - y))
        ((y - s)⁻¹ •
          (D y -
            h3RawFourierL2HeatApplyNN
              1 zero_le_one
              (Real.toNNReal (y - s))
              (D s))) := by
    change
      (y - s)⁻¹ •
        h3RawFourierL2HeatCLM
          1 zero_le_one
          (Real.toNNReal (q - y))
          (D y -
            h3RawFourierL2HeatApplyNN
              1 zero_le_one
              (Real.toNNReal (y - s))
              (D s))
        =
      h3RawFourierL2HeatCLM
        1 zero_le_one
        (Real.toNNReal (q - y))
        ((y - s)⁻¹ •
          (D y -
            h3RawFourierL2HeatApplyNN
              1 zero_le_one
              (Real.toNNReal (y - s))
              (D s)))
    rw [map_smul]

  rw [hMapSmul]

  apply congrArg
    (h3RawFourierL2HeatApplyNN
      1 zero_le_one
      (Real.toNNReal (q - y)))

  rw [slope_def_module]
  unfold h3RawFourierL2UnitHeatVectorQuotientState
  rw [← hDs]
  simp only [smul_sub]
  abel

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Fifth.Mild.Mass

/-!
# Seventh Fréchet endpoint: fifth convolution frequency split

The sixth endpoint now closes a quantitative full fifth raw Fourier moment for
the selected positive-time mild state.

The next derivative layer feeds that fifth-order state regularity back through
the quadratic forcing. Since the Leray-divergence symbol contributes one
frequency power, a forcing fourth-moment estimate begins with a fifth weighted
convolution bound.

This file isolates the only new frequency algebra:

    ξ = η + (ξ - η).

A case split on the larger convolution frequency gives

    ‖ξ‖ ≤ 2 max(‖η‖, ‖ξ - η‖),

hence

    ‖ξ‖⁵
      ≤
    2⁵ (‖η‖⁵ + ‖ξ - η‖⁵).

The coefficient is deliberately not optimized; the endpoint argument only
needs a finite explicit constant.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSeventhEndpointFifthFrequencySplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Harmless coefficient in the fifth convolution frequency split. -/
noncomputable def h3FourierFifthSplitCoefficient : ℝ :=
  (2 : ℝ) ^ (5 : ℝ)

/-- The fifth split coefficient is nonnegative. -/
theorem h3FourierFifthSplitCoefficient_nonneg :
    0 ≤ h3FourierFifthSplitCoefficient := by
  unfold h3FourierFifthSplitCoefficient
  exact Real.rpow_nonneg (by norm_num) _

/-- The output fifth Fourier weight splits between the two convolution
frequencies. -/
theorem h3FourierFifthWeight_le_split
    (ξ η : H3FourierPoint3) :
    ‖ξ‖ ^ 5
      ≤
    h3FourierFifthSplitCoefficient *
      (‖η‖ ^ 5 + ‖ξ - η‖ ^ 5) := by
  have hξ0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg _

  have hη0 : 0 ≤ ‖η‖ :=
    norm_nonneg _

  have hshift0 : 0 ≤ ‖ξ - η‖ :=
    norm_nonneg _

  have htri :
      ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
    calc
      ‖ξ‖ = ‖η + (ξ - η)‖ := by
        congr 1
        abel
      _ ≤ ‖η‖ + ‖ξ - η‖ :=
        norm_add_le _ _

  have hcoeff0 :
      0 ≤ (2 : ℝ) ^ (5 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _

  have hηw0 :
      0 ≤ ‖η‖ ^ 5 :=
    pow_nonneg hη0 5

  have hshiftw0 :
      0 ≤ ‖ξ - η‖ ^ 5 :=
    pow_nonneg hshift0 5

  have hξpow :
      ‖ξ‖ ^ (5 : ℝ) = ‖ξ‖ ^ (5 : ℕ) :=
    Real.rpow_natCast ‖ξ‖ 5

  have hηpow :
      ‖η‖ ^ (5 : ℝ) = ‖η‖ ^ (5 : ℕ) :=
    Real.rpow_natCast ‖η‖ 5

  have hshiftpow :
      ‖ξ - η‖ ^ (5 : ℝ) = ‖ξ - η‖ ^ (5 : ℕ) :=
    Real.rpow_natCast ‖ξ - η‖ 5

  unfold h3FourierFifthSplitCoefficient

  by_cases hηshift : ‖η‖ ≤ ‖ξ - η‖
  · have htwo :
        ‖ξ‖ ≤ 2 * ‖ξ - η‖ := by
      linarith

    have hrpow :
        ‖ξ‖ ^ (5 : ℝ)
          ≤
        (2 * ‖ξ - η‖) ^ (5 : ℝ) :=
      Real.rpow_le_rpow
        hξ0 htwo (by norm_num)

    have hmul :
        (2 * ‖ξ - η‖) ^ (5 : ℝ)
          =
        (2 : ℝ) ^ (5 : ℝ) *
          ‖ξ - η‖ ^ (5 : ℝ) := by
      rw [
        Real.mul_rpow
          (by norm_num : 0 ≤ (2 : ℝ))
          hshift0
      ]

    calc
      ‖ξ‖ ^ 5
          =
        ‖ξ‖ ^ (5 : ℝ) := by
        rw [hξpow]
      _ ≤
        (2 * ‖ξ - η‖) ^ (5 : ℝ) :=
        hrpow
      _ =
        (2 : ℝ) ^ (5 : ℝ) *
          ‖ξ - η‖ ^ (5 : ℝ) :=
        hmul
      _ =
        (2 : ℝ) ^ (5 : ℝ) *
          ‖ξ - η‖ ^ 5 := by
        rw [hshiftpow]
      _ ≤
        (2 : ℝ) ^ (5 : ℝ) *
          (‖η‖ ^ 5 + ‖ξ - η‖ ^ 5) := by
        exact
          mul_le_mul_of_nonneg_left
            (by linarith)
            hcoeff0

  · have hshiftη :
        ‖ξ - η‖ ≤ ‖η‖ := by
      exact le_of_lt (lt_of_not_ge hηshift)

    have htwo :
        ‖ξ‖ ≤ 2 * ‖η‖ := by
      linarith

    have hrpow :
        ‖ξ‖ ^ (5 : ℝ)
          ≤
        (2 * ‖η‖) ^ (5 : ℝ) :=
      Real.rpow_le_rpow
        hξ0 htwo (by norm_num)

    have hmul :
        (2 * ‖η‖) ^ (5 : ℝ)
          =
        (2 : ℝ) ^ (5 : ℝ) *
          ‖η‖ ^ (5 : ℝ) := by
      rw [
        Real.mul_rpow
          (by norm_num : 0 ≤ (2 : ℝ))
          hη0
      ]

    calc
      ‖ξ‖ ^ 5
          =
        ‖ξ‖ ^ (5 : ℝ) := by
        rw [hξpow]
      _ ≤
        (2 * ‖η‖) ^ (5 : ℝ) :=
        hrpow
      _ =
        (2 : ℝ) ^ (5 : ℝ) *
          ‖η‖ ^ (5 : ℝ) :=
        hmul
      _ =
        (2 : ℝ) ^ (5 : ℝ) *
          ‖η‖ ^ 5 := by
        rw [hηpow]
      _ ≤
        (2 : ℝ) ^ (5 : ℝ) *
          (‖η‖ ^ 5 + ‖ξ - η‖ ^ 5) := by
        exact
          mul_le_mul_of_nonneg_left
            (by linarith)
            hcoeff0

end
end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FourthMildMass

/-!
# Sixth Fréchet endpoint: fourth convolution frequency split

The fifth endpoint now closes a quantitative full fourth raw Fourier moment for
the selected positive-time mild state.

The next derivative layer feeds that fourth-order state regularity back through
the quadratic forcing.  Since the Leray-divergence symbol contributes one
frequency power, a forcing third-moment estimate begins with a fourth weighted
convolution bound.

This file isolates the only new frequency algebra:

    ξ = η + (ξ - η).

A case split on the larger convolution frequency gives

    ‖ξ‖ ≤ 2 max(‖η‖, ‖ξ - η‖),

hence

    ‖ξ‖⁴
      ≤
    2⁴ (‖η‖⁴ + ‖ξ - η‖⁴).

The coefficient is deliberately not optimized; the endpoint argument only
needs a finite explicit constant.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointFourthFrequencySplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Harmless coefficient in the fourth convolution frequency split. -/
noncomputable def h3FourierFourthSplitCoefficient : ℝ :=
  (2 : ℝ) ^ (4 : ℝ)

/-- The fourth split coefficient is nonnegative. -/
theorem h3FourierFourthSplitCoefficient_nonneg :
    0 ≤ h3FourierFourthSplitCoefficient := by
  unfold h3FourierFourthSplitCoefficient
  exact Real.rpow_nonneg (by norm_num) _

/-- The output fourth Fourier weight splits between the two convolution
frequencies. -/
theorem h3FourierFourthWeight_le_split
    (ξ η : H3FourierPoint3) :
    ‖ξ‖ ^ 4
      ≤
    h3FourierFourthSplitCoefficient *
      (‖η‖ ^ 4 + ‖ξ - η‖ ^ 4) := by
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
      0 ≤ (2 : ℝ) ^ (4 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _

  have hηw0 :
      0 ≤ ‖η‖ ^ 4 :=
    pow_nonneg hη0 4

  have hshiftw0 :
      0 ≤ ‖ξ - η‖ ^ 4 :=
    pow_nonneg hshift0 4

  have hξpow :
      ‖ξ‖ ^ (4 : ℝ) = ‖ξ‖ ^ (4 : ℕ) :=
    Real.rpow_natCast ‖ξ‖ 4

  have hηpow :
      ‖η‖ ^ (4 : ℝ) = ‖η‖ ^ (4 : ℕ) :=
    Real.rpow_natCast ‖η‖ 4

  have hshiftpow :
      ‖ξ - η‖ ^ (4 : ℝ) = ‖ξ - η‖ ^ (4 : ℕ) :=
    Real.rpow_natCast ‖ξ - η‖ 4

  unfold h3FourierFourthSplitCoefficient

  by_cases hηshift : ‖η‖ ≤ ‖ξ - η‖
  · have htwo :
        ‖ξ‖ ≤ 2 * ‖ξ - η‖ := by
      linarith

    have hrpow :
        ‖ξ‖ ^ (4 : ℝ)
          ≤
        (2 * ‖ξ - η‖) ^ (4 : ℝ) :=
      Real.rpow_le_rpow
        hξ0 htwo (by norm_num)

    have hmul :
        (2 * ‖ξ - η‖) ^ (4 : ℝ)
          =
        (2 : ℝ) ^ (4 : ℝ) *
          ‖ξ - η‖ ^ (4 : ℝ) := by
      rw [
        Real.mul_rpow
          (by norm_num : 0 ≤ (2 : ℝ))
          hshift0
      ]

    calc
      ‖ξ‖ ^ 4
          =
        ‖ξ‖ ^ (4 : ℝ) := by
        rw [hξpow]
      _ ≤
        (2 * ‖ξ - η‖) ^ (4 : ℝ) :=
        hrpow
      _ =
        (2 : ℝ) ^ (4 : ℝ) *
          ‖ξ - η‖ ^ (4 : ℝ) :=
        hmul
      _ =
        (2 : ℝ) ^ (4 : ℝ) *
          ‖ξ - η‖ ^ 4 := by
        rw [hshiftpow]
      _ ≤
        (2 : ℝ) ^ (4 : ℝ) *
          (‖η‖ ^ 4 + ‖ξ - η‖ ^ 4) := by
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
        ‖ξ‖ ^ (4 : ℝ)
          ≤
        (2 * ‖η‖) ^ (4 : ℝ) :=
      Real.rpow_le_rpow
        hξ0 htwo (by norm_num)

    have hmul :
        (2 * ‖η‖) ^ (4 : ℝ)
          =
        (2 : ℝ) ^ (4 : ℝ) *
          ‖η‖ ^ (4 : ℝ) := by
      rw [
        Real.mul_rpow
          (by norm_num : 0 ≤ (2 : ℝ))
          hη0
      ]

    calc
      ‖ξ‖ ^ 4
          =
        ‖ξ‖ ^ (4 : ℝ) := by
        rw [hξpow]
      _ ≤
        (2 * ‖η‖) ^ (4 : ℝ) :=
        hrpow
      _ =
        (2 : ℝ) ^ (4 : ℝ) *
          ‖η‖ ^ (4 : ℝ) :=
        hmul
      _ =
        (2 : ℝ) ^ (4 : ℝ) *
          ‖η‖ ^ 4 := by
        rw [hηpow]
      _ ≤
        (2 : ℝ) ^ (4 : ℝ) *
          (‖η‖ ^ 4 + ‖ξ - η‖ ^ 4) := by
        exact
          mul_le_mul_of_nonneg_left
            (by linarith)
            hcoeff0

end
end Euclidean
end Bridge
end PrimeTensor

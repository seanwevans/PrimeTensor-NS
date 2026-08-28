import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.MildRawNineQuarter

/-!
# Fractional `9/4` frequency split for nonlinear convolution

The selected mild state now has an integrable `9/4` moment in the exact
canonical raw Fourier representative consumed by the nonlinear forcing layer.

Before propagating that moment through convolution, isolate the only genuinely
new frequency algebra.

For a convolution frequency decomposition

    ξ = η + (ξ - η),

the triangle inequality gives

    ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖.

For the fractional exponent `9/4 > 1`, use the safe max bound

    a + b ≤ 2 max(a,b).

Monotonicity and multiplicativity of nonnegative real powers then give

    ‖ξ‖^(9/4)
      ≤
    2^(9/4) * max(‖η‖^(9/4), ‖ξ-η‖^(9/4))
      ≤
    2^(9/4) * (‖η‖^(9/4) + ‖ξ-η‖^(9/4)).

The coefficient is not optimized.  Its role is only to produce an honest
two-sided Young majorant for the next convolution checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzNineQuarterFrequencySplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Harmless coefficient in the `9/4` convolution frequency split. -/
noncomputable def h3FourierNineQuarterSplitCoefficient : ℝ :=
  (2 : ℝ) ^ ((9 : ℝ) / 4)

/-- The output `9/4` Fourier weight splits between the two convolution
frequencies. -/
theorem h3FourierNineQuarterWeight_le_split
    (ξ η : H3FourierPoint3) :
    h3FourierNineQuarterWeight ξ
      ≤
    h3FourierNineQuarterSplitCoefficient *
      (h3FourierNineQuarterWeight η +
        h3FourierNineQuarterWeight (ξ - η)) := by
  have hp : 0 ≤ (9 : ℝ) / 4 := by
    norm_num

  have hη0 : 0 ≤ ‖η‖ := norm_nonneg _
  have hshift0 : 0 ≤ ‖ξ - η‖ := norm_nonneg _

  have htri :
      ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
    calc
      ‖ξ‖ = ‖η + (ξ - η)‖ := by
        congr 1
        abel
      _ ≤ ‖η‖ + ‖ξ - η‖ :=
        norm_add_le _ _

  have hsum0 :
      0 ≤ ‖η‖ + ‖ξ - η‖ :=
    add_nonneg hη0 hshift0

  have hmax0 :
      0 ≤ max ‖η‖ ‖ξ - η‖ :=
    hη0.trans (le_max_left _ _)

  have hsumMax :
      ‖η‖ + ‖ξ - η‖
        ≤
      2 * max ‖η‖ ‖ξ - η‖ := by
    nlinarith [
      le_max_left ‖η‖ ‖ξ - η‖,
      le_max_right ‖η‖ ‖ξ - η‖
    ]

  have hFirst :
      ‖ξ‖ ^ ((9 : ℝ) / 4)
        ≤
      (‖η‖ + ‖ξ - η‖) ^ ((9 : ℝ) / 4) :=
    Real.rpow_le_rpow
      (norm_nonneg ξ)
      htri
      hp

  have hSecond :
      (‖η‖ + ‖ξ - η‖) ^ ((9 : ℝ) / 4)
        ≤
      (2 * max ‖η‖ ‖ξ - η‖) ^ ((9 : ℝ) / 4) :=
    Real.rpow_le_rpow
      hsum0
      hsumMax
      hp

  have hMaxPower :
      max ‖η‖ ‖ξ - η‖ ^ ((9 : ℝ) / 4)
        =
      max
        (‖η‖ ^ ((9 : ℝ) / 4))
        (‖ξ - η‖ ^ ((9 : ℝ) / 4)) :=
    Real.rpow_max hη0 hshift0 hp

  have hηPower0 :
      0 ≤ ‖η‖ ^ ((9 : ℝ) / 4) :=
    Real.rpow_nonneg hη0 _

  have hshiftPower0 :
      0 ≤ ‖ξ - η‖ ^ ((9 : ℝ) / 4) :=
    Real.rpow_nonneg hshift0 _

  have hMaxLe :
      max
          (‖η‖ ^ ((9 : ℝ) / 4))
          (‖ξ - η‖ ^ ((9 : ℝ) / 4))
        ≤
      ‖η‖ ^ ((9 : ℝ) / 4) +
        ‖ξ - η‖ ^ ((9 : ℝ) / 4) := by
    apply max_le
    · exact le_add_of_nonneg_right hshiftPower0
    · exact le_add_of_nonneg_left hηPower0

  have hCoeff0 :
      0 ≤ h3FourierNineQuarterSplitCoefficient := by
    unfold h3FourierNineQuarterSplitCoefficient
    exact Real.rpow_nonneg (by norm_num) _

  unfold h3FourierNineQuarterWeight

  calc
    ‖ξ‖ ^ ((9 : ℝ) / 4)
        ≤
      (‖η‖ + ‖ξ - η‖) ^ ((9 : ℝ) / 4) :=
        hFirst
    _ ≤
      (2 * max ‖η‖ ‖ξ - η‖) ^ ((9 : ℝ) / 4) :=
        hSecond
    _ =
      h3FourierNineQuarterSplitCoefficient *
        max
          (‖η‖ ^ ((9 : ℝ) / 4))
          (‖ξ - η‖ ^ ((9 : ℝ) / 4)) := by
        unfold h3FourierNineQuarterSplitCoefficient
        rw [
          Real.mul_rpow
            (by norm_num : (0 : ℝ) ≤ 2)
            hmax0,
          hMaxPower
        ]
    _ ≤
      h3FourierNineQuarterSplitCoefficient *
        (‖η‖ ^ ((9 : ℝ) / 4) +
          ‖ξ - η‖ ^ ((9 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hMaxLe hCoeff0

end
end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.High.Tail.Decay
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# BKM endpoint: quarter-moment H³ deweighting weight for the high tail

The qualitative high-frequency multiplier decay is now closed.  To obtain a
logarithmic middle-shell count we need an explicit dyadic decay rate.

A quarter power is enough.  Define

    q(ξ) = ‖ξ‖^(5/4) W₃(ξ)⁻¹.

The exact H³ weight already gives

    ‖ξ‖ W₃(ξ)⁻¹ ≤ (1 + ‖ξ‖²)⁻¹.

Multiplying by the extra quarter moment and comparing

    ‖ξ‖^(1/4) ≤ (1 + ‖ξ‖²)^(1/8)

shows

    q(ξ) ≤ (1 + ‖ξ‖²)^(-7/8).

The right-hand side belongs to `L²(R³)` because its square has exponent
`-7/4`, strictly beyond the three-dimensional threshold `-3/2`.

Thus `q ∈ L²`.  The next file can use high-frequency support
`‖ξ‖ ≥ R` to extract

    ‖ξ‖ W₃(ξ)⁻¹
      ≤ R^(-1/4) q(ξ),

giving the explicit dyadic factor `2^{-hi/4}` needed for the logarithmic BKM
cutoff choice.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeBKMEndpointHighFrequencyGradientQuarterWeight
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Fractional standard Bessel majorant -/

/-- The fractional Bessel weight used to dominate the quarter H³ moment. -/
noncomputable def h3BKMQuarterTailBesselWeight
    (ξ : H3FourierPoint3) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ (-(7 : ℝ) / 8)

theorem continuous_h3BKMQuarterTailBesselWeight :
    Continuous h3BKMQuarterTailBesselWeight := by

  unfold h3BKMQuarterTailBesselWeight

  exact
    (continuous_const.add (continuous_norm.pow 2)).rpow_const
      (fun ξ =>
        Or.inl
          (ne_of_gt
            (show 0 < (1 : ℝ) + ‖ξ‖ ^ 2 by
              positivity)))

/--
The fractional Bessel majorant belongs to `L²(R³)`.
-/
theorem h3BKMQuarterTailBesselWeight_memLp2 :
    MemLp
      h3BKMQuarterTailBesselWeight
      2
      (volume : Measure H3FourierPoint3) := by

  have hs :
      (Module.finrank ℝ H3FourierPoint3 : ℝ)
        <
      ((7 : ℝ) / 2) := by
    rw [h3FourierPoint3_finrank]
    norm_num

  have hInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-((7 : ℝ) / 2) / 2))
        (volume : Measure H3FourierPoint3) :=
    integrable_rpow_neg_one_add_norm_sq hs

  have hMeas :
      AEStronglyMeasurable
        h3BKMQuarterTailBesselWeight
        (volume : Measure H3FourierPoint3) :=
    continuous_h3BKMQuarterTailBesselWeight.aestronglyMeasurable

  rw [memLp_two_iff_integrable_sq_norm hMeas]

  refine hInt.congr ?_

  filter_upwards with ξ

  have hB :
      0 < (1 : ℝ) + ‖ξ‖ ^ 2 := by
    positivity

  unfold h3BKMQuarterTailBesselWeight

  rw [
    Real.norm_eq_abs,
    abs_of_pos
      (Real.rpow_pos_of_pos hB (-(7 : ℝ) / 8))
  ]

  symm

  calc
    (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(7 : ℝ) / 8)) ^ 2
        =
      (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(7 : ℝ) / 8)) ^ (2 : ℝ) := by
        exact
          (Real.rpow_natCast
            (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(7 : ℝ) / 8))
            2).symm

    _ =
      ((1 : ℝ) + ‖ξ‖ ^ 2) ^
        ((-(7 : ℝ) / 8) * 2) := by
        rw [
          ← Real.rpow_mul
            hB.le
            (-(7 : ℝ) / 8)
            (2 : ℝ)
        ]

    _ =
      ((1 : ℝ) + ‖ξ‖ ^ 2) ^
        (-((7 : ℝ) / 2) / 2) := by
        congr 1
        ring

/-! ## Quarter raw H³ moment -/

/--
The exact quarter-tail H³ deweighting weight

    ‖ξ‖^(5/4) W₃(ξ)⁻¹.
-/
noncomputable def h3BKMQuarterTailMomentWeight
    (ξ : H3FourierPoint3) : ℝ :=
  ‖ξ‖ ^ ((5 : ℝ) / 4)
    *
  h3SobolevFrequencyWeightInv ξ

theorem continuous_h3BKMQuarterTailMomentWeight :
    Continuous h3BKMQuarterTailMomentWeight := by

  have hMoment :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ ((5 : ℝ) / 4)) :=
    continuous_norm.rpow_const
      (fun ξ =>
        Or.inr
          (by norm_num : 0 ≤ (5 : ℝ) / 4))

  unfold h3BKMQuarterTailMomentWeight

  exact
    hMoment.mul
      continuous_h3SobolevFrequencyWeightInv

/--
The exact quarter-tail H³ moment is pointwise dominated by the fractional
standard Bessel weight.
-/
theorem h3BKMQuarterTailMomentWeight_le_bessel
    (ξ : H3FourierPoint3) :
    h3BKMQuarterTailMomentWeight ξ
      ≤
    h3BKMQuarterTailBesselWeight ξ := by

  let r : ℝ := ‖ξ‖
  let B : ℝ := 1 + ‖ξ‖ ^ 2

  have hr :
      0 ≤ r := by
    dsimp only [r]
    exact norm_nonneg _

  have hB :
      0 < B := by
    dsimp only [B]
    positivity

  have hFirst :
      h3SobolevFrequencyFirstMomentInv ξ
        ≤
      h3StandardInverseBesselWeight ξ :=
    h3SobolevFrequencyFirstMomentInv_le_standard ξ

  have hStdNonneg :
      0 ≤ h3StandardInverseBesselWeight ξ := by
    unfold h3StandardInverseBesselWeight
    positivity

  have hQuarter :
      r ^ ((1 : ℝ) / 4)
        ≤
      B ^ ((1 : ℝ) / 8) := by

    have hSq :
        r ^ 2 ≤ B := by
      dsimp only [r, B]
      linarith

    have hPow :=
      Real.rpow_le_rpow
        (sq_nonneg r)
        hSq
        (by norm_num : 0 ≤ (1 : ℝ) / 8)

    calc
      r ^ ((1 : ℝ) / 4)
          =
        (r ^ 2) ^ ((1 : ℝ) / 8) := by

          calc
            r ^ ((1 : ℝ) / 4)
                =
              r ^ ((2 : ℝ) * ((1 : ℝ) / 8)) := by
                congr 1
                ring

            _ =
              (r ^ (2 : ℝ)) ^ ((1 : ℝ) / 8) := by
                rw [
                  Real.rpow_mul
                    hr
                    (2 : ℝ)
                    ((1 : ℝ) / 8)
                ]

            _ =
              (r ^ 2) ^ ((1 : ℝ) / 8) := by
                exact
                  congrArg
                    (fun z : ℝ => z ^ ((1 : ℝ) / 8))
                    (Real.rpow_natCast r 2)

      _ ≤
        B ^ ((1 : ℝ) / 8) := hPow

  have hSplit :
      r ^ ((5 : ℝ) / 4)
        =
      r ^ ((1 : ℝ) / 4) * r := by

    calc
      r ^ ((5 : ℝ) / 4)
          =
        r ^ (((1 : ℝ) / 4) + 1) := by
          congr 1
          ring

      _ =
        r ^ ((1 : ℝ) / 4) * r ^ (1 : ℝ) := by
          rw [
            Real.rpow_add_of_nonneg
              hr
              (by norm_num : 0 ≤ (1 : ℝ) / 4)
              (by norm_num : 0 ≤ (1 : ℝ))
          ]

      _ =
        r ^ ((1 : ℝ) / 4) * r := by
          rw [Real.rpow_one]

  have hQuarterNonneg :
      0 ≤ r ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg hr _

  have hBQuarterNonneg :
      0 ≤ B ^ ((1 : ℝ) / 8) :=
    Real.rpow_nonneg hB.le _

  unfold
    h3BKMQuarterTailMomentWeight
    h3BKMQuarterTailBesselWeight

  change
    r ^ ((5 : ℝ) / 4)
        *
      h3SobolevFrequencyWeightInv ξ
      ≤
    B ^ (-(7 : ℝ) / 8)

  rw [hSplit]

  calc
    (r ^ ((1 : ℝ) / 4) * r)
        *
      h3SobolevFrequencyWeightInv ξ
        =
      r ^ ((1 : ℝ) / 4)
        *
      h3SobolevFrequencyFirstMomentInv ξ := by
        unfold h3SobolevFrequencyFirstMomentInv
        dsimp only [r]
        ring

    _ ≤
      r ^ ((1 : ℝ) / 4)
        *
      h3StandardInverseBesselWeight ξ :=
      mul_le_mul_of_nonneg_left
        hFirst
        hQuarterNonneg

    _ ≤
      B ^ ((1 : ℝ) / 8)
        *
      h3StandardInverseBesselWeight ξ :=
      mul_le_mul_of_nonneg_right
        hQuarter
        hStdNonneg

    _ =
      B ^ ((1 : ℝ) / 8) * B⁻¹ := by
        unfold h3StandardInverseBesselWeight
        dsimp only [B]

    _ =
      B ^ ((1 : ℝ) / 8) * B ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]

    _ =
      B ^ (((1 : ℝ) / 8) + (-1 : ℝ)) := by
        rw [
          Real.rpow_add
            hB
            ((1 : ℝ) / 8)
            (-1 : ℝ)
        ]

    _ =
      B ^ (-(7 : ℝ) / 8) := by
        congr 1
        ring

/--
The quarter-tail H³ moment belongs to real Fourier `L²`.
-/
theorem h3BKMQuarterTailMomentWeight_memLp2 :
    MemLp
      h3BKMQuarterTailMomentWeight
      2
      (volume : Measure H3FourierPoint3) := by

  apply
    h3BKMQuarterTailBesselWeight_memLp2.of_le
      continuous_h3BKMQuarterTailMomentWeight.aestronglyMeasurable

  filter_upwards with ξ

  have hMomentNonneg :
      0 ≤ h3BKMQuarterTailMomentWeight ξ := by
    unfold h3BKMQuarterTailMomentWeight
    exact
      mul_nonneg
        (Real.rpow_nonneg (norm_nonneg ξ) _)
        (by
          unfold h3SobolevFrequencyWeightInv
          exact
            inv_nonneg.mpr
              (h3SobolevFrequencyWeight_pos ξ).le)

  have hBesselNonneg :
      0 ≤ h3BKMQuarterTailBesselWeight ξ := by
    unfold h3BKMQuarterTailBesselWeight
    exact
      Real.rpow_nonneg
        (by positivity)
        _

  simpa [
    Real.norm_eq_abs,
    abs_of_nonneg hMomentNonneg,
    abs_of_nonneg hBesselNonneg
  ] using
    h3BKMQuarterTailMomentWeight_le_bessel ξ

/-! ## Complex L² package and fixed coefficient -/

/-- Complex-valued copy of the quarter-tail H³ moment. -/
def h3BKMQuarterTailMomentWeightComplex
    (ξ : H3FourierPoint3) : ℂ :=
  h3BKMQuarterTailMomentWeight ξ

theorem h3BKMQuarterTailMomentWeightComplex_memLp2 :
    MemLp
      h3BKMQuarterTailMomentWeightComplex
      2
      (volume : Measure H3FourierPoint3) := by
  exact
    h3BKMQuarterTailMomentWeight_memLp2.ofReal

/-- Canonical Fourier `L²` package of the quarter-tail H³ moment. -/
noncomputable def h3BKMQuarterTailMomentWeightL2 :
    H3FourierComplexL2 :=
  h3BKMQuarterTailMomentWeightComplex_memLp2.toLp
    h3BKMQuarterTailMomentWeightComplex

/-- Fixed quarter-tail deweighting coefficient. -/
noncomputable def h3BKMQuarterTailMomentConstant : ℝ :=
  ‖h3BKMQuarterTailMomentWeightL2‖

theorem h3BKMQuarterTailMomentConstant_nonneg :
    0 ≤ h3BKMQuarterTailMomentConstant := by
  unfold h3BKMQuarterTailMomentConstant
  exact norm_nonneg _

end

end Euclidean
end Bridge
end PrimeTensor

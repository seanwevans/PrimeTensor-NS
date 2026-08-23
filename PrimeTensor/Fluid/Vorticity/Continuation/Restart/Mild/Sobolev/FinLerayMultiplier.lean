import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinLeraySymbol

/-!
# Fin-indexed Leray multiplier on the weighted H³ spectral state

`FinLeraySymbol` proves the pointwise matrix-entry estimate

    ‖Pᵢⱼ(ξ)‖ ≤ 2.

This file lifts that symbol to the actual weighted Fourier `L²` state.  Each
matrix entry acts as a bounded scalar multiplier, and the finite sum over the
three input coordinates produces a bounded operator on

    Fin 3 → H3SpectralScalarState.

Because the project uses the finite-product sup norm, the direct entrywise
estimate gives the coarse but sufficient operator bound

    ‖P G‖ ≤ 6 ‖G‖.

The constant is intentionally not optimized here.  The exact Hilbert-space
orthogonal projection has norm one, but `6` is enough to close the restart
Picard estimate without introducing another finite-dimensional norm bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3FinLerayMultiplier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Measurability of the pointwise symbol -/

/-- The rank-one Leray coefficient is measurable in frequency. -/
theorem measurable_h3LerayRankOneCoefficient
    (i j : Fin 3) :
    Measurable
      (fun ξ : H3FourierPoint3 =>
        h3LerayRankOneCoefficient ξ i j) := by
  have hq :
      Measurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ) := by
    unfold h3FourierGradientSquare
    measurability

  have hi :
      Measurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol i ξ) := by
    unfold h3FourierDerivativeSymbol
    measurability

  have hj :
      Measurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol j ξ) := by
    unfold h3FourierDerivativeSymbol
    measurability

  have hjstar :
      Measurable
        (fun ξ : H3FourierPoint3 =>
          star (h3FourierDerivativeSymbol j ξ)) :=
    continuous_star.measurable.comp hj

  have hden :
      Measurable
        (fun ξ : H3FourierPoint3 =>
          (h3FourierGradientSquare ξ : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hq

  unfold h3LerayRankOneCoefficient
  exact
    Measurable.ite
      (measurableSet_eq_fun hq measurable_const)
      measurable_const
      ((hi.mul hjstar).div hden)

/-- Every Leray matrix entry is measurable in frequency. -/
theorem measurable_h3LerayCoefficient
    (i j : Fin 3) :
    Measurable
      (fun ξ : H3FourierPoint3 =>
        h3LerayCoefficient ξ i j) := by
  unfold h3LerayCoefficient
  exact
    measurable_const.sub
      (measurable_h3LerayRankOneCoefficient i j)

/-! ## One matrix entry as an `L²` multiplier -/

/-- Multiplication by one Leray matrix entry preserves the weighted spectral `L²` state. -/
theorem h3LerayCoefficientFrequency_memLp
    (i j : Fin 3)
    (G : H3SpectralScalarState) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3LerayCoefficient ξ i j * G ξ)
      2 volume := by
  refine
    (MeasureTheory.Lp.memLp G).of_le_mul
      (c := 2)
      ?_ ?_
  · exact
      (measurable_h3LerayCoefficient i j).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable G)
  · filter_upwards with ξ
    calc
      ‖h3LerayCoefficient ξ i j * G ξ‖
          =
        ‖h3LerayCoefficient ξ i j‖ * ‖G ξ‖ := by
          rw [norm_mul]
      _ ≤
        2 * ‖G ξ‖ :=
      mul_le_mul_of_nonneg_right
        (norm_h3LerayCoefficient_le_two ξ i j)
        (norm_nonneg _)

/-- Apply one Leray matrix entry to one weighted H³ scalar state. -/
noncomputable def h3SpectralScalarLerayCoefficientApply
    (i j : Fin 3)
    (G : H3SpectralScalarState) :
    H3SpectralScalarState :=
  (h3LerayCoefficientFrequency_memLp i j G).toLp
    (fun ξ : H3FourierPoint3 =>
      h3LerayCoefficient ξ i j * G ξ)

/-- Pointwise representative of one Leray matrix-entry multiplier. -/
theorem h3SpectralScalarLerayCoefficientApply_ae
    (i j : Fin 3)
    (G : H3SpectralScalarState) :
    (h3SpectralScalarLerayCoefficientApply i j G :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      h3LerayCoefficient ξ i j * G ξ) := by
  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3LerayCoefficientFrequency_memLp i j G)

/-- One Leray matrix entry has scalar `L²` operator norm at most two. -/
theorem norm_h3SpectralScalarLerayCoefficientApply_le
    (i j : Fin 3)
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarLerayCoefficientApply i j G‖
      ≤
    2 * ‖G‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    h3SpectralScalarLerayCoefficientApply_ae i j G
  ] with ξ hξ
  rw [hξ, norm_mul]
  exact
    mul_le_mul_of_nonneg_right
      (norm_h3LerayCoefficient_le_two ξ i j)
      (norm_nonneg _)

/-! ## Full three-component Leray multiplier -/

/-- Apply the finite Fourier Leray matrix to a weighted H³ spectral vector state. -/
noncomputable def h3SpectralFinLerayApply
    (G : H3SpectralFinVectorState) :
    H3SpectralFinVectorState :=
  fun i =>
    ∑ j : Fin 3,
      h3SpectralScalarLerayCoefficientApply
        i j (G j)

/-- Coordinatewise finite-product bound for the lifted Leray multiplier. -/
theorem norm_h3SpectralFinLerayApply_coordinate_le
    (G : H3SpectralFinVectorState)
    (i : Fin 3) :
    ‖h3SpectralFinLerayApply G i‖
      ≤
    6 * ‖G‖ := by
  calc
    ‖h3SpectralFinLerayApply G i‖
        ≤
      ∑ j : Fin 3,
        ‖h3SpectralScalarLerayCoefficientApply
          i j (G j)‖ := by
          exact
            norm_sum_le
              Finset.univ
              (fun j : Fin 3 =>
                h3SpectralScalarLerayCoefficientApply
                  i j (G j))
    _ ≤
      ∑ j : Fin 3,
        2 * ‖G j‖ := by
          exact
            Finset.sum_le_sum
              (fun j _ =>
                norm_h3SpectralScalarLerayCoefficientApply_le
                  i j (G j))
    _ ≤
      ∑ _j : Fin 3,
        2 * ‖G‖ := by
          exact
            Finset.sum_le_sum
              (fun j _ =>
                mul_le_mul_of_nonneg_left
                  (h3SpectralFinVector_coordinate_norm_le G j)
                  (by norm_num))
    _ =
      6 * ‖G‖ := by
          simp
          ring

/-- Coarse operator norm bound for the Leray projector in the finite-product sup norm. -/
theorem norm_h3SpectralFinLerayApply_le
    (G : H3SpectralFinVectorState) :
    ‖h3SpectralFinLerayApply G‖
      ≤
    6 * ‖G‖ := by
  have hRhs :
      0 ≤ 6 * ‖G‖ := by
    positivity
  apply (pi_norm_le_iff_of_nonneg hRhs).2
  intro i
  exact
    norm_h3SpectralFinLerayApply_coordinate_le
      G i

end

end Euclidean
end Bridge
end PrimeTensor

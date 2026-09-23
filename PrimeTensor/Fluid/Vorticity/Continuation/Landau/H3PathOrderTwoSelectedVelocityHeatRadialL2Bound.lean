import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderTwoSelectedVelocityRawFourierL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.Moment.Free.Heat

/-!
# Fixed-lag heat smoothing in weighted Fourier L²

For the remaining order-two fourth-velocity continuity argument we need a
uniform fifth-radial `L²` bound on a positive time slab.

The free-heat and midpoint-head pieces both reduce to one generic estimate.
If `0 < τ₀ ≤ τ`, then by the heat semigroup law

    H_τ = H_{τ₀} H_{τ-τ₀},

and the second factor is an `L²` contraction.  Therefore every natural radial
weight satisfies

    ‖ |ξ|^n H_τ F ‖₂
      ≤ h3HeatNatMomentCoefficient n ν τ₀ * ‖F‖₂.

The important feature is that the coefficient depends only on the fixed lower
heat lag `τ₀`, not on the varying larger time `τ`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedVelocityHeatRadialL2Bound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A fixed positive lower heat lag controls every later radial multiplier. -/
theorem h3HeatFourierMomentMultiplier_le_nat_of_lowerLag
    {ν τ₀ τ : ℝ}
    (hν : 0 < ν)
    (hτ₀ : 0 < τ₀)
    (hτ : τ₀ ≤ τ)
    (n : ℕ)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ n * ‖h3HeatFourierSymbol ν τ ξ‖
      ≤
    h3HeatNatMomentCoefficient n ν τ₀ := by
  have hrem : 0 ≤ τ - τ₀ := sub_nonneg.mpr hτ

  have hSplit :
      h3HeatFourierSymbol ν τ ξ
        =
      h3HeatFourierSymbol ν τ₀ ξ *
        h3HeatFourierSymbol ν (τ - τ₀) ξ := by
    have hsum : τ₀ + (τ - τ₀) = τ := by ring
    calc
      h3HeatFourierSymbol ν τ ξ
          =
        h3HeatFourierSymbol ν (τ₀ + (τ - τ₀)) ξ := by
          rw [hsum]
      _ =
        h3HeatFourierSymbol ν τ₀ ξ *
          h3HeatFourierSymbol ν (τ - τ₀) ξ := by
          simpa only [mul_comm] using
            h3HeatFourierSymbol_add ν τ₀ (τ - τ₀) ξ

  have hLater :
      ‖h3HeatFourierSymbol ν (τ - τ₀) ξ‖ ≤ 1 :=
    norm_h3HeatFourierSymbol_le_one
      hν.le hrem ξ

  have hBase :=
    h3HeatFourierMomentMultiplier_le_nat
      hν hτ₀ n ξ

  have hBase' :
      ‖ξ‖ ^ n *
          ‖h3HeatFourierSymbol ν τ₀ ξ‖
        ≤
      h3HeatNatMomentCoefficient n ν τ₀ := by
    simpa only [h3FourierMomentWeight_natCast] using hBase

  rw [hSplit, norm_mul]

  calc
    ‖ξ‖ ^ n *
        (‖h3HeatFourierSymbol ν τ₀ ξ‖ *
          ‖h3HeatFourierSymbol ν (τ - τ₀) ξ‖)
        =
      (‖ξ‖ ^ n *
        ‖h3HeatFourierSymbol ν τ₀ ξ‖) *
        ‖h3HeatFourierSymbol ν (τ - τ₀) ξ‖ := by
      ring
    _ ≤
      (‖ξ‖ ^ n *
        ‖h3HeatFourierSymbol ν τ₀ ξ‖) * 1 := by
      exact
        mul_le_mul_of_nonneg_left
          hLater
          (mul_nonneg
            (pow_nonneg (norm_nonneg ξ) n)
            (norm_nonneg _))
    _ =
      ‖ξ‖ ^ n *
        ‖h3HeatFourierSymbol ν τ₀ ξ‖ := by
      ring
    _ ≤
      h3HeatNatMomentCoefficient n ν τ₀ :=
      hBase'

/-- Weighted heat-smoothed Fourier amplitude is in `L²`, with a coefficient
depending only on a fixed positive lower lag. -/
theorem h3HeatRadialFourier_memLp2_of_lowerLag
    {ν τ₀ τ : ℝ}
    (hν : 0 < ν)
    (hτ₀ : 0 < τ₀)
    (hτ : τ₀ ≤ τ)
    (n : ℕ)
    (F : H3FourierComplexL2) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          (h3HeatFourierSymbol ν τ ξ * F ξ))
      2
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ :=
    h3HeatNatMomentCoefficient n ν τ₀

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ n : ℝ) : ℂ) *
            (h3HeatFourierSymbol ν τ ξ * F ξ))
        (volume : Measure H3FourierPoint3) := by
    exact
      (Complex.continuous_ofReal.comp
        (continuous_norm.pow n)).aestronglyMeasurable.mul
        ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
          (MeasureTheory.Lp.aestronglyMeasurable F))

  refine
    (MeasureTheory.Lp.memLp F).of_le_mul
      (c := C)
      hMeas
      ?_

  filter_upwards with ξ

  have hWeight0 : 0 ≤ ‖ξ‖ ^ n :=
    pow_nonneg (norm_nonneg ξ) n

  have hPoint :=
    h3HeatFourierMomentMultiplier_le_nat_of_lowerLag
      hν hτ₀ hτ n ξ

  dsimp only [C]

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hWeight0,
    norm_mul
  ]

  calc
    ‖ξ‖ ^ n *
        (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
        =
      (‖ξ‖ ^ n *
        ‖h3HeatFourierSymbol ν τ ξ‖) *
        ‖F ξ‖ := by
      ring
    _ ≤
      h3HeatNatMomentCoefficient n ν τ₀ *
        ‖F ξ‖ :=
      mul_le_mul_of_nonneg_right
        hPoint
        (norm_nonneg _)

/-- Quotient-safe weighted heat-smoothed Fourier state. -/
noncomputable def h3HeatRadialFourierL2OfLowerLag
    {ν τ₀ τ : ℝ}
    (hν : 0 < ν)
    (hτ₀ : 0 < τ₀)
    (hτ : τ₀ ≤ τ)
    (n : ℕ)
    (F : H3FourierComplexL2) :
    H3FourierComplexL2 :=
  (h3HeatRadialFourier_memLp2_of_lowerLag
      hν hτ₀ hτ n F).toLp
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ n : ℝ) : ℂ) *
        (h3HeatFourierSymbol ν τ ξ * F ξ))

/-- The fixed-lag heat package satisfies the quantitative `L²` norm bound. -/
theorem norm_h3HeatRadialFourierL2OfLowerLag_le
    {ν τ₀ τ : ℝ}
    (hν : 0 < ν)
    (hτ₀ : 0 < τ₀)
    (hτ : τ₀ ≤ τ)
    (n : ℕ)
    (F : H3FourierComplexL2) :
    ‖h3HeatRadialFourierL2OfLowerLag
        hν hτ₀ hτ n F‖
      ≤
    h3HeatNatMomentCoefficient n ν τ₀ * ‖F‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul

  have hRep :=
    MeasureTheory.MemLp.coeFn_toLp
      (h3HeatRadialFourier_memLp2_of_lowerLag
        hν hτ₀ hτ n F)

  filter_upwards [hRep] with ξ hξ

  unfold h3HeatRadialFourierL2OfLowerLag
  rw [hξ]

  have hWeight0 : 0 ≤ ‖ξ‖ ^ n :=
    pow_nonneg (norm_nonneg ξ) n

  have hPoint :=
    h3HeatFourierMomentMultiplier_le_nat_of_lowerLag
      hν hτ₀ hτ n ξ

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hWeight0,
    norm_mul
  ]

  calc
    ‖ξ‖ ^ n *
        (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
        =
      (‖ξ‖ ^ n *
        ‖h3HeatFourierSymbol ν τ ξ‖) *
        ‖F ξ‖ := by
      ring
    _ ≤
      h3HeatNatMomentCoefficient n ν τ₀ *
        ‖F ξ‖ :=
      mul_le_mul_of_nonneg_right
        hPoint
        (norm_nonneg _)

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Heat.HalfHolder

/-!
# Uniform positive-lag half-Hölder heat orbit in spectral H³

The fixed-base estimate in `Quarter.Heat.HalfHolder` has coefficient

    L(ν,a) = sqrt ((2π)^2 ν) * (sqrt (ν (a/3)))⁻¹.

On any window whose heat lag is bounded below by `δ > 0`, this coefficient is
uniformly bounded by `L(ν,δ)`.  This file records that monotonicity and lifts it
to the scalar and velocity heat orbits.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- The positive-lag half-Hölder coefficient decreases as the already elapsed
heat time increases. -/
theorem h3HeatPositiveLagHalfHolderCoefficient_le_of_le
    {ν δ a : ℝ}
    (hν : 0 < ν)
    (hδ : 0 < δ)
    (hδa : δ ≤ a) :
    h3HeatPositiveLagHalfHolderCoefficient ν a
      ≤
    h3HeatPositiveLagHalfHolderCoefficient ν δ := by
  unfold h3HeatPositiveLagHalfHolderCoefficient

  have harg :
      ν * (δ / 3) ≤ ν * (a / 3) := by
    nlinarith

  have hsqrt :
      Real.sqrt (ν * (δ / 3))
        ≤
      Real.sqrt (ν * (a / 3)) :=
    Real.sqrt_le_sqrt harg

  have hδsqrt :
      0 < Real.sqrt (ν * (δ / 3)) := by
    exact Real.sqrt_pos.2 (by positivity)

  have hinv :
      (Real.sqrt (ν * (a / 3)))⁻¹
        ≤
      (Real.sqrt (ν * (δ / 3)))⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hδsqrt hsqrt

  exact
    mul_le_mul_of_nonneg_left
      hinv
      (Real.sqrt_nonneg _)

/-- Uniform scalar half-Hölder heat increment on every base lag `a ≥ δ > 0`. -/
theorem norm_h3SpectralScalarHeatApplyNN_add_sub_le_halfHolder_uniformPositiveLag
    {ν δ a h : ℝ}
    (hν : 0 < ν)
    (hδ : 0 < δ)
    (hδa : δ ≤ a)
    (hh : 0 ≤ h)
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk (a + h) (add_nonneg (le_trans hδ.le hδa) hh)) G -
        h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk a (le_trans hδ.le hδa)) G‖
      ≤
    (h3HeatPositiveLagHalfHolderCoefficient ν δ * ‖G‖) *
      Real.sqrt h := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa

  calc
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk (a + h) (add_nonneg ha.le hh)) G -
        h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk a ha.le) G‖
        ≤
      (h3HeatPositiveLagHalfHolderCoefficient ν a * ‖G‖) *
        Real.sqrt h :=
      norm_h3SpectralScalarHeatApplyNN_add_sub_le_halfHolder_positiveLag
        hν ha hh G
    _ ≤
      (h3HeatPositiveLagHalfHolderCoefficient ν δ * ‖G‖) *
        Real.sqrt h := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (h3HeatPositiveLagHalfHolderCoefficient_le_of_le
              hν hδ hδa)
            (norm_nonneg G))
          (Real.sqrt_nonneg h)

/-- Uniform velocity half-Hölder heat increment on every base lag `a ≥ δ > 0`. -/
theorem norm_h3SpectralVelocityHeatApplyNN_add_sub_le_halfHolder_uniformPositiveLag
    {ν δ a h : ℝ}
    (hν : 0 < ν)
    (hδ : 0 < δ)
    (hδa : δ ≤ a)
    (hh : 0 ≤ h)
    (U : H3SpectralVelocityState) :
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk (a + h) (add_nonneg (le_trans hδ.le hδa) hh)) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk a (le_trans hδ.le hδa)) U‖
      ≤
    (h3HeatPositiveLagHalfHolderCoefficient ν δ * ‖U‖) *
      Real.sqrt h := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa

  calc
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk (a + h) (add_nonneg ha.le hh)) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk a ha.le) U‖
        ≤
      (h3HeatPositiveLagHalfHolderCoefficient ν a * ‖U‖) *
        Real.sqrt h :=
      norm_h3SpectralVelocityHeatApplyNN_add_sub_le_halfHolder_positiveLag
        hν ha hh U
    _ ≤
      (h3HeatPositiveLagHalfHolderCoefficient ν δ * ‖U‖) *
        Real.sqrt h := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (h3HeatPositiveLagHalfHolderCoefficient_le_of_le
              hν hδ hδa)
            (norm_nonneg U))
          (Real.sqrt_nonneg h)

end

end Euclidean
end Bridge
end PrimeTensor

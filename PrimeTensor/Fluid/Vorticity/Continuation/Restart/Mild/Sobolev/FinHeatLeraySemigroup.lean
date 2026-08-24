import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SpectralHeatSemigroup
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.HeatDerivativeContinuity

/-!
# Semigroup compatibility of the Fin-indexed heat--Leray kernel

The ordinary spectral heat semigroup is now a contractive continuous linear
map.  To restart the Volterra Duhamel term at an intermediate time we need the
same semigroup law after the divergence derivative and Leray projection.

There are two algebraic ingredients.

1. Heat commutes with the finite Fourier Leray multiplier.  Entrywise this is
   just commutativity of the scalar heat symbol with the scalar Leray matrix
   coefficient.

2. Adding nonnegative heat time after one positive heat-derivative time is
   exactly ordinary heat evolution of the shorter heat-derivative output.
   This is the scalar theorem from `HeatDerivativeContinuity`, lifted through
   the finite divergence sum.

Combining them gives the nonlinear kernel identity

    K_{a+b}(U,V) = H_b (K_a(U,V))

for `a > 0`, `b ≥ 0`.

This is the pointwise kernel restart law needed before splitting the Duhamel
interval integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-! ## Heat commutes with one Leray matrix coefficient -/

/--
One scalar heat multiplier commutes with one scalar Leray matrix-entry
multiplier.
-/
theorem h3SpectralScalarHeatApplyNN_lerayCoefficient_commute
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (i j : Fin 3)
    (G : H3SpectralScalarState) :
    h3SpectralScalarHeatApplyNN ν hν t
        (h3SpectralScalarLerayCoefficientApply i j G)
      =
    h3SpectralScalarLerayCoefficientApply i j
      (h3SpectralScalarHeatApplyNN ν hν t G) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3HeatFrequencyApplyNN_coeFn
      ν hν t
      (h3SpectralScalarLerayCoefficientApply i j G),
    h3SpectralScalarLerayCoefficientApply_ae
      i j G,
    h3SpectralScalarLerayCoefficientApply_ae
      i j (h3SpectralScalarHeatApplyNN ν hν t G),
    h3HeatFrequencyApplyNN_coeFn
      ν hν t G
  ] with ξ hHeatLeft hLerayInner hLerayRight hHeatG
  unfold h3SpectralScalarHeatApplyNN at hLerayRight ⊢
  rw [hHeatLeft, hLerayInner, hLerayRight, hHeatG]
  ring

/-! ## Heat commutes with the full finite Leray multiplier -/

/--
The ordinary spectral heat semigroup commutes with the finite three-component
Leray multiplier.
-/
theorem h3SpectralVelocityHeatApplyNN_finLeray_commute
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (G : H3SpectralFinVectorState) :
    h3SpectralVelocityHeatApplyNN ν hν t
        (h3SpectralFinLerayApply G)
      =
    h3SpectralFinLerayApply
      (h3SpectralVelocityHeatApplyNN ν hν t G) := by
  funext i
  unfold h3SpectralVelocityHeatApplyNN
  unfold h3SpectralFinLerayApply
  change
    h3SpectralScalarHeatCLM ν hν t
        (∑ j : Fin 3,
          h3SpectralScalarLerayCoefficientApply
            i j (G j))
      =
    ∑ j : Fin 3,
      h3SpectralScalarLerayCoefficientApply
        i j
        (h3SpectralScalarHeatApplyNN ν hν t (G j))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact
    h3SpectralScalarHeatApplyNN_lerayCoefficient_commute
      ν hν t i j (G j)

/-! ## Heat time addition through finite divergence -/

/--
Adding a nonnegative heat time after a positive finite tensor
heat-divergence time equals ordinary heat evolution of the shorter-time
heat-divergence output.
-/
theorem h3SpectralFinTensorHeatDivergenceApply_add_time
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (T : H3SpectralFinTensorState) :
    h3SpectralFinTensorHeatDivergenceApply
        ν (a + b) hν
        (add_pos_of_pos_of_nonneg ha hb)
        T
      =
    h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν)
        (NNReal.mk b hb)
        (h3SpectralFinTensorHeatDivergenceApply
          ν a hν ha T) := by
  funext i
  unfold h3SpectralFinTensorHeatDivergenceApply
  unfold h3SpectralVelocityHeatApplyNN
  change
    (∑ j : Fin 3,
      h3SpectralScalarHeatDerivativeApply
        ν (a + b) hν
        (add_pos_of_pos_of_nonneg ha hb)
        j (T i j))
      =
    h3SpectralScalarHeatCLM
        ν (le_of_lt hν) (NNReal.mk b hb)
        (∑ j : Fin 3,
          h3SpectralScalarHeatDerivativeApply
            ν a hν ha j (T i j))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact
    h3SpectralScalarHeatDerivativeApply_add_time
      hν ha hb j (T i j)

/--
The same time-addition law for the fixed-input pre-Leray velocity kernel.
-/
theorem h3SpectralFinVelocityHeatDivergenceApply_add_time
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (U V : H3SpectralFinVectorState) :
    h3SpectralFinVelocityHeatDivergenceApply
        ν (a + b) hν
        (add_pos_of_pos_of_nonneg ha hb)
        U V
      =
    h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν)
        (NNReal.mk b hb)
        (h3SpectralFinVelocityHeatDivergenceApply
          ν a hν ha U V) := by
  unfold h3SpectralFinVelocityHeatDivergenceApply
  exact
    h3SpectralFinTensorHeatDivergenceApply_add_time
      hν ha hb (h3SpectralFinOuterProduct U V)

/-! ## Full heat--Leray kernel restart law -/

/--
Adding nonnegative elapsed heat time to the genuine positive-time heat--Leray
kernel is exactly ordinary heat evolution of the shorter-time heat--Leray
output:

    K_{a+b}(U,V) = H_b (K_a(U,V)).
-/
theorem h3SpectralFinHeatLerayVelocityApply_add_time
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (U V : H3SpectralFinVectorState) :
    h3SpectralFinHeatLerayVelocityApply
        ν (a + b) hν
        (add_pos_of_pos_of_nonneg ha hb)
        U V
      =
    h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν)
        (NNReal.mk b hb)
        (h3SpectralFinHeatLerayVelocityApply
          ν a hν ha U V) := by
  unfold h3SpectralFinHeatLerayVelocityApply
  rw [
    h3SpectralFinVelocityHeatDivergenceApply_add_time
      hν ha hb U V
  ]
  exact
    (h3SpectralVelocityHeatApplyNN_finLeray_commute
      ν (le_of_lt hν) (NNReal.mk b hb)
      (h3SpectralFinVelocityHeatDivergenceApply
        ν a hν ha U V)).symm

end

end Euclidean
end Bridge
end PrimeTensor

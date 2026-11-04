import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRegularizedHermitianNumeratorRecovery
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.PDE.Algebra
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Encoder
import Mathlib.Tactic

/-!
# Exact finite Leray matrix = intrinsic-axis transverse numerator

The finite-coordinate Leray symbol was built from the Fourier derivative
coefficients `2π i ξ_j`, while full-third Schwartz recovery uses the
intrinsic depth-three axis polynomial

  N_ξ(A) = |ξ|² A - ξ (ξ · A).

The bridge is algebraic and works at *every* frequency, including zero.
We first multiply the finite Leray matrix by its gradient-square denominator,
then cancel the fixed nonzero `2π i` normalization. There is no division by
|ξ|² and no need to claim a singular L² Leray image is smooth.

The final formula identifies the regularized `Fin 3` multiplier with the
smooth axis numerator divided by `|ξ|² + δ_n`. Applying it to L² classes and
transporting the exact Sobolev deweighting are the following analytic step.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology PrimeTensor.Bridge.Euclidean
open scoped BigOperators ENNReal ComplexConjugate

noncomputable section
set_option maxHeartbeats 1800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFiniteAxisNumerator244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The positive-depth axis dot is the Hilbert Fourier square radius, not a
second frequency norm. -/
theorem thirdFullAxisDot_hilbertRadiusSquare244 (ξ : V3) :
    thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) = ‖ξ‖ ^ 2 := by
  rw [h3FourierPoint3_norm_sq_eq_sum_coordinates]
  unfold thirdTriadAxisDot244
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The axis-to-Fin coordinate equivalence transports the *complex* mixed
dot, without conjugating the velocity polarization. -/
theorem thirdFullAxisMixedDot_fin3_eq244
    (ξ : V3) (z : Fin 3 → ℂ) :
    mixedDot (WithLp.ofLp ξ)
      (fun a : A3 => z (h3ClassicalizationFinOfAxis a)) =
    ∑ j : Fin 3, (ξ (h3AxisOfFin3 j) : ℂ) * z j := by
  let e : Fin 3 ≃ A3 :=
    { toFun := h3AxisOfFin3
      invFun := h3ClassicalizationFinOfAxis
      left_inv := h3ClassicalizationFinOfAxis_h3AxisOfFin3
      right_inv := h3AxisOfFin3_h3ClassicalizationFinOfAxis }
  have hSum :
      (∑ j : Fin 3, (ξ (h3AxisOfFin3 j) : ℂ) * z j) =
      ∑ a : A3, (ξ a : ℂ) * z (h3ClassicalizationFinOfAxis a) := by
    exact Fintype.sum_equiv e
      (fun j : Fin 3 => (ξ (h3AxisOfFin3 j) : ℂ) * z j)
      (fun a : A3 => (ξ a : ℂ) * z (h3ClassicalizationFinOfAxis a))
      (by
        intro j
        change
          (ξ (h3AxisOfFin3 j) : ℂ) * z j =
          (ξ (h3AxisOfFin3 j) : ℂ) *
            z (h3ClassicalizationFinOfAxis (h3AxisOfFin3 j))
        rw [h3ClassicalizationFinOfAxis_h3AxisOfFin3])
  exact hSum.symm

/-- A denominator-free identity for a *single* matrix entry. It includes
zero frequency, where both derivative symbols vanish. -/
theorem h3FullThirdLerayCoefficient_scaled244
    (ξ : V3) (i j : Fin 3) :
    (h3FourierGradientSquare ξ : ℂ) * h3LerayCoefficient ξ i j =
      (h3FourierGradientSquare ξ : ℂ) * h3LerayDelta i j -
        h3FourierDerivativeSymbol i ξ *
          star (h3FourierDerivativeSymbol j ξ) := by
  by_cases hq : h3FourierGradientSquare ξ = 0
  · have hi :=
      h3FourierDerivativeSymbol_eq_zero_of_gradientSquare_eq_zero hq i
    have hj :=
      h3FourierDerivativeSymbol_eq_zero_of_gradientSquare_eq_zero hq j
    simp [h3LerayCoefficient, h3LerayRankOneCoefficient, hq, hi, hj]
  · have hqc : (h3FourierGradientSquare ξ : ℂ) ≠ 0 := by
      exact_mod_cast hq
    simp only [h3LerayCoefficient, h3LerayRankOneCoefficient,
      dite_eq_right hq]
    field_simp [hqc]

/-- The full finite Leray action has the exact scaled numerator written in
its original derivative symbols. -/
theorem h3FullThirdLerayAction_scaled244
    (ξ : V3) (i : Fin 3) (z : Fin 3 → ℂ) :
    (h3FourierGradientSquare ξ : ℂ) *
      (∑ j : Fin 3, h3LerayCoefficient ξ i j * z j) =
    (h3FourierGradientSquare ξ : ℂ) * z i -
      h3FourierDerivativeSymbol i ξ *
        (∑ j : Fin 3,
          star (h3FourierDerivativeSymbol j ξ) * z j) := by
  calc
    (h3FourierGradientSquare ξ : ℂ) *
        (∑ j : Fin 3, h3LerayCoefficient ξ i j * z j) =
      ∑ j : Fin 3,
        ((h3FourierGradientSquare ξ : ℂ) *
          h3LerayCoefficient ξ i j) * z j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = ∑ j : Fin 3,
      ((h3FourierGradientSquare ξ : ℂ) * h3LerayDelta i j -
          h3FourierDerivativeSymbol i ξ *
            star (h3FourierDerivativeSymbol j ξ)) * z j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [h3FullThirdLerayCoefficient_scaled244]
    _ = (h3FourierGradientSquare ξ : ℂ) *
          (∑ j : Fin 3, h3LerayDelta i j * z j) -
        h3FourierDerivativeSymbol i ξ *
          (∑ j : Fin 3,
            star (h3FourierDerivativeSymbol j ξ) * z j) := by
              simp_rw [sub_mul]
              rw [Finset.sum_sub_distrib]
              congr 1
              · rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
              · rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
    _ = _ := by rw [sum_h3LerayDelta_mul]

/-- Cancel only the globally nonzero Fourier normalization `2π i`, not the
frequency radius. Consequently the result holds *at ξ=0* as well. -/
theorem h3FullThirdLerayAction_axisNumerator244
    (ξ : V3) (i : Fin 3) (z : Fin 3 → ℂ) :
    (‖ξ‖ ^ 2 : ℂ) *
      (∑ j : Fin 3, h3LerayCoefficient ξ i j * z j) =
    (‖ξ‖ ^ 2 : ℂ) * z i -
      (∑ j : Fin 3, (ξ (h3AxisOfFin3 j) : ℂ) * z j) *
        (ξ (h3AxisOfFin3 i) : ℂ) := by
  let K : ℂ := 2 * Real.pi * Complex.I
  have hK : K ≠ 0 := Complex.two_pi_I_ne_zero
  have hKsq : K ^ 2 = -(((2 * Real.pi) ^ 2 : ℝ) : ℂ) := by
    dsimp [K]
    calc
      (2 * Real.pi * Complex.I : ℂ) ^ 2 =
          (((2 * Real.pi : ℝ) : ℂ) ^ 2) * Complex.I ^ 2 := by
            push_cast
            ring
      _ = -(((2 * Real.pi) ^ 2 : ℝ) : ℂ) := by
        rw [Complex.I_sq]
        push_cast
        ring
  have hQ : (h3FourierGradientSquare ξ : ℂ) =
      (-K ^ 2) * (‖ξ‖ ^ 2 : ℂ) := by
    rw [hKsq]
    unfold h3FourierGradientSquare
    push_cast
    ring
  have hD (j : Fin 3) :
      h3FourierDerivativeSymbol j ξ =
        K * (ξ (h3AxisOfFin3 j) : ℂ) := rfl
  have hStar (j : Fin 3) :
      star (h3FourierDerivativeSymbol j ξ) =
        -K * (ξ (h3AxisOfFin3 j) : ℂ) := by
    rw [show star (h3FourierDerivativeSymbol j ξ) =
          -h3FourierDerivativeSymbol j ξ from
      conj_h3FourierDerivativeSymbol_eq_neg j ξ]
    rw [hD j]
    ring
  have hStarSum :
      (∑ j : Fin 3, star (h3FourierDerivativeSymbol j ξ) * z j) =
      -K * (∑ j : Fin 3,
        (ξ (h3AxisOfFin3 j) : ℂ) * z j) := by
    calc
      _ = ∑ j : Fin 3,
          (-K) * ((ξ (h3AxisOfFin3 j) : ℂ) * z j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hStar j]
            ring
      _ = _ := by rw [Finset.mul_sum]
  have hScaled := h3FullThirdLerayAction_scaled244 ξ i z
  have hFactor :
      (-K ^ 2) * ((‖ξ‖ ^ 2 : ℂ) *
        (∑ j : Fin 3, h3LerayCoefficient ξ i j * z j)) =
      (-K ^ 2) * ((‖ξ‖ ^ 2 : ℂ) * z i -
        (∑ j : Fin 3, (ξ (h3AxisOfFin3 j) : ℂ) * z j) *
          (ξ (h3AxisOfFin3 i) : ℂ)) := by
    calc
      _ = (h3FourierGradientSquare ξ : ℂ) *
          (∑ j : Fin 3, h3LerayCoefficient ξ i j * z j) := by
            rw [hQ]
            ring
      _ = (h3FourierGradientSquare ξ : ℂ) * z i -
          h3FourierDerivativeSymbol i ξ *
            (∑ j : Fin 3, star (h3FourierDerivativeSymbol j ξ) * z j) :=
        hScaled
      _ = _ := by
        rw [hQ, hD i, hStarSum]
        ring
  have hK2 : -K ^ 2 ≠ 0 := by
    exact neg_ne_zero.mpr (pow_ne_zero 2 hK)
  exact mul_left_cancel₀ hK2 hFactor

/-- EXACT pointwise intrinsic-axis bridge, including the origin. -/
theorem h3FullThirdFiniteLeray_eq_axisNumerator244
    (ξ : V3) (i : Fin 3) (z : Fin 3 → ℂ) :
    (‖ξ‖ ^ 2 : ℂ) *
      (∑ j : Fin 3, h3LerayCoefficient ξ i j * z j) =
    thirdFullComplexTransverseNumerator244 (WithLp.ofLp ξ)
      (fun a : A3 => z (h3ClassicalizationFinOfAxis a))
      (h3AxisOfFin3 i) := by
  have hAction := h3FullThirdLerayAction_axisNumerator244 ξ i z
  rw [hAction]
  simp only [thirdFullComplexTransverseNumerator244,
    h3ClassicalizationFinOfAxis_h3AxisOfFin3,
    thirdFullAxisDot_hilbertRadiusSquare244,
    thirdFullAxisMixedDot_fin3_eq244]
  push_cast
  ring

/-- Apply the same nonsingular radial factor used by the constructive real
Schwartz family to the exact `Fin 3` Leray multiplier. -/
theorem h3FullThirdRegularizedFiniteLeray_axisFraction244
    (n : ℕ) (ξ : V3) (i : Fin 3) (z : Fin 3 → ℂ) :
    (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) *
      (∑ j : Fin 3, h3LerayCoefficient ξ i j * z j) =
    (((thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) +
        h3FullThirdRegularizationScale244 n)⁻¹ : ℝ) : ℂ) *
      thirdFullComplexTransverseNumerator244 (WithLp.ofLp ξ)
        (fun a : A3 => z (h3ClassicalizationFinOfAxis a))
        (h3AxisOfFin3 i) := by
  have hNumerator := h3FullThirdFiniteLeray_eq_axisNumerator244 ξ i z
  rw [← hNumerator, thirdFullAxisDot_hilbertRadiusSquare244]
  unfold h3FullThirdRadialRecoveryFactor244
  rw [div_eq_mul_inv]
  push_cast
  ring

end
end PrimeTensor.FirstMonomialTriad

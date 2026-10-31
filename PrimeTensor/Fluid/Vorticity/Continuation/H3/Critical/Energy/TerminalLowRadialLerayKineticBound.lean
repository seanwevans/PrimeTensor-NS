import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalLowRadialQuadraticKineticBound
import Mathlib.Tactic

/-!
# Actual kinetic Bernstein bound for the complete low-radial Fourier Leray source

The previous result bounds the genuine raw Fourier velocity-pair convolution
and its differentiated form by the strict-time kinetic energy anchor on each
fixed radial ball. Here we carry that estimate through both finite sums in
the REAL projected Navier--Stokes nonlinear source:

  outer_k(ξ) = ∑_{j=0}² d_j(ξ) (û_k * û_j)(ξ)
  Leray_i(ξ) = ∑_{k=0}² P_{ik}(ξ) outer_k(ξ).

There are exactly three derivative-convolution terms for each outer_k,
three Leray summands, and ‖P_{ik}(ξ)‖ ≤ 2. Thus on |d(ξ)| < ρ,

  |outer_k(ξ,t)| ≤ 3 ρ E₀(b),
  |Leray_i(ξ,t)| ≤ 18 ρ E₀(b),   b < t < T.

These estimates use the actual physical kinetic anchor, without an assumed
positive terminal kinetic mass, uniform H³ ceiling, or raw Fourier L¹ bound.

This file proves pointwise Fourier inequalities only. Establishing the
finite-band Fourier L² bound, its physical inverse-Fourier counterpart,
and time-L¹ of the projected low-pass source are separate next obligations.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1000000

/-- Three scalar derivative-convolution bounds imply the exact coarse
finite outer-product divergence ceiling `3 * (ρ * E)` at one frequency. -/
theorem h3Critical_lowRadial_outerDivergence_le_of_derivativeBounds
    (U : H3SpectralVelocityState)
    (ρ E : ℝ) (ξ : H3FourierPoint3)
    (hDerivative : ∀ j k : Fin 3,
      ‖h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U k) (U j) ξ‖ ≤ ρ * E)
    (k : Fin 3) :
    ‖h3RawFinOuterProductDivergence U U k ξ‖ ≤
      3 * (ρ * E) := by
  unfold h3RawFinOuterProductDivergence
  calc
    ‖∑ j : Fin 3, h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U k) (U j) ξ‖ ≤
      ∑ j : Fin 3, ‖h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U k) (U j) ξ‖ :=
      norm_sum_le (Finset.univ : Finset (Fin 3)) _
    _ ≤ ∑ _j : Fin 3, ρ * E := by
      exact Finset.sum_le_sum (fun j _ => hDerivative j k)
    _ = 3 * (ρ * E) := by
      simp only [Fin.sum_univ_three]
      ring

/-- The full Leray projection adds only its three bounded matrix entries;
the complete nonlinear source is bounded by `18 * (ρ * E)`. -/
theorem h3Critical_lowRadial_lerayDivergence_le_of_outerBounds
    (U : H3SpectralVelocityState)
    (ρ E : ℝ) (ξ : H3FourierPoint3)
    (hOuter : ∀ k : Fin 3,
      ‖h3RawFinOuterProductDivergence U U k ξ‖ ≤ 3 * (ρ * E))
    (i : Fin 3) :
    ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ ≤
      18 * (ρ * E) := by
  unfold h3RawFinLerayOuterProductDivergence
  calc
    ‖∑ k : Fin 3, h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U U k ξ‖ ≤
      ∑ k : Fin 3, ‖h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U U k ξ‖ :=
      norm_sum_le (Finset.univ : Finset (Fin 3)) _
    _ ≤ ∑ _k : Fin 3, 2 * (3 * (ρ * E)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      calc
        ‖h3LerayCoefficient ξ i k‖ *
            ‖h3RawFinOuterProductDivergence U U k ξ‖ ≤
          2 * ‖h3RawFinOuterProductDivergence U U k ξ‖ :=
          mul_le_mul_of_nonneg_right
            (norm_h3LerayCoefficient_le_two ξ i k) (norm_nonneg _)
        _ ≤ 2 * (3 * (ρ * E)) :=
          mul_le_mul_of_nonneg_left (hOuter k) (by norm_num)
    _ = 18 * (ρ * E) := by
      simp only [Fin.sum_univ_three]
      ring

/-- The ACTUAL strict-time outer-product divergence has a uniform
fixed-radius kinetic ceiling, at all frequencies in that radial ball. -/
theorem h3Critical_actual_lowRadial_outerDivergence_le_kineticAnchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ t : ℝ, t ∈ Set.Ioo b T →
      ∀ (k : Fin 3) (ξ : H3FourierPoint3),
        ξ ∈ h3TerminalRadialFrequencyBelow ρ →
        ‖h3RawFinOuterProductDivergence
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 t) k ξ‖ ≤
          3 * (ρ * velocityH3Energy0At u b) := by
  intro t ht k ξ hξ
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  change ‖h3RawFinOuterProductDivergence U U k ξ‖ ≤ _
  apply h3Critical_lowRadial_outerDivergence_le_of_derivativeBounds
    U ρ (velocityH3Energy0At u b) ξ _ k
  intro j m
  exact h3Critical_actual_lowRadial_derivativeConvolution_le_kineticAnchor
    hH3 hClass b hb ρ hρ t ht j m j ξ hξ

/-- After the genuine finite Leray matrix, every physical-time nonlinear
Fourier-source coordinate obeys the radius-times-kinetic ceiling. -/
theorem h3Critical_actual_lowRadial_lerayDivergence_le_kineticAnchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ t : ℝ, t ∈ Set.Ioo b T →
      ∀ (i : Fin 3) (ξ : H3FourierPoint3),
        ξ ∈ h3TerminalRadialFrequencyBelow ρ →
        ‖h3RawFinLerayOuterProductDivergence
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 t) i ξ‖ ≤
          18 * (ρ * velocityH3Energy0At u b) := by
  intro t ht i ξ hξ
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  change ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ ≤ _
  apply h3Critical_lowRadial_lerayDivergence_le_of_outerBounds
    U ρ (velocityH3Energy0At u b) ξ _ i
  intro k
  exact h3Critical_actual_lowRadial_outerDivergence_le_kineticAnchor
    hH3 hClass b hb ρ hρ t ht k ξ hξ

end
end PrimeTensor.Bridge.Euclidean

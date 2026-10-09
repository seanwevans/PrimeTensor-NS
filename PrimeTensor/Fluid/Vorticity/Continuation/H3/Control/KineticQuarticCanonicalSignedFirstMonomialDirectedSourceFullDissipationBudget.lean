import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceIndexedGap

/-!
# Indexed directed H³ obstruction: full dissipation and exact balance budgets

The original source index includes one gradient-excess channel

  S₀(t) = 24 C₁ sqrt(E(t)) E₃(t) - D(t).

The previously synchronized indexed sequence has `n < S_i(τ n)/(9 E(τ n))`.
When its fixed index is zero, the exact full dissipative budget (not only its
D₃/E₃ spectral relaxation) is therefore

  9 n + D(τ n)/E(τ n)
    < 24 C₁ sqrt(E(τ n)) E₃(τ n)/E(τ n).

The exact PDE energy balance identifies its full normalized gap with
`2 D/E`, producing a second indexed strict inequality on the same times.
The other branch is still one fixed adverse ordered velocity monomial with
an indexed lower bound. All three independently proved critical terminal
clocks remain on the original time sequence.

No physical sign constraint, dissipative absorption, or unconditional
continuation theorem is inserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Full physical normalized viscous budget of an indexed gradient source.
It retains the top-energy fraction `E₃/E` and the actual full `D/E`. -/
def h3PathCanonicalGradientFullDissipationBudgetAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t R : ℝ) : Prop :=
  9 * R + velocityH3DissipationAt u t / velocityH3EnergyAt u t <
    (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) *
      velocityH3Energy3At u t) / velocityH3EnergyAt u t

/-- The indexed source condition itself implies a strict budget using the
full viscous dissipation rather than only its top-order Fourier block. -/
theorem h3PathCanonical_gradientSource_forces_fullDissipationBudget
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t R : ℝ)
    (hSource : R <
      (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        velocityH3Energy3At u t - velocityH3DissipationAt u t) /
        (9 * velocityH3EnergyAt u t)) :
    h3PathCanonicalGradientFullDissipationBudgetAt u t R := by
  let E : ℝ := velocityH3EnergyAt u t
  let D : ℝ := velocityH3DissipationAt u t
  let B : ℝ := 24 *
    (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * Real.sqrt E) *
    velocityH3Energy3At u t
  have hE : 0 < E :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hDen : 0 < 9 * E := by positivity
  have hSource' : R < (B - D) / (9 * E) := by
    simpa only [B, D, E] using hSource
  have hScaled : R * (9 * E) < B - D :=
    (lt_div_iff₀ hDen).mp hSource'
  have hRaw : 9 * R * E + D < B := by
    nlinarith only [hScaled]
  change 9 * R + D / E < B / E
  apply (lt_div_iff₀ hE).2
  have hFactor : (9 * R + D / E) * E = 9 * R * E + D := by
    field_simp [ne_of_gt hE] <;> ring
  rw [hFactor]
  exact hRaw

/-- The exact PDE gap has twice the full normalized dissipation. -/
def h3PathCanonicalGradientExactBalanceBudgetAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t R : ℝ) : Prop :=
  18 * R +
      ((- velocityH3TransportDerivativeAt u t -
          deriv (velocityH3EnergyAt u) t) / velocityH3EnergyAt u t) <
    2 * ((24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) *
      velocityH3Energy3At u t) / velocityH3EnergyAt u t)

/-- Transfer the full dissipative budget to the precise energy/transport
balance-gap channel on an admissible physical preterminal time slice. -/
theorem h3PathCanonical_gradientSource_forces_exactBalanceBudget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hBudget : h3PathCanonicalGradientFullDissipationBudgetAt u t R) :
    h3PathCanonicalGradientExactBalanceBudgetAt u t R := by
  have hBalance :=
    normalized_negativeTransport_sub_deriv_eq_two_mul_dissipation_div_energy
      hH3 hClass ht
  change 9 * R + velocityH3DissipationAt u t / velocityH3EnergyAt u t <
    (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) *
      velocityH3Energy3At u t) / velocityH3EnergyAt u t at hBudget
  change 18 * R +
      ((- velocityH3TransportDerivativeAt u t -
          deriv (velocityH3EnergyAt u) t) / velocityH3EnergyAt u t) <
    2 * ((24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) *
      velocityH3Energy3At u t) / velocityH3EnergyAt u t)
  rw [hBalance]
  linarith only [hBudget]

/-- Same original-index physical terminal times: either the gradient source
forces an actual full-dissipation budget at *every* index, with an exact
balance-gap refinement on a late tail, or one fixed ordered velocity channel
has an indexed negative ratio. The three established physical clocks persist. -/
theorem h3PathCanonical_fixedDirectedSource_fullBudget_or_indexedSignedMonomial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      (∀ n : ℕ,
        τ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3Energy3At u (τ n)) atTop atTop ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (τ n)) ∧
      ((i = 0 ∧
          (∀ n : ℕ,
            h3PathCanonicalGradientFullDissipationBudgetAt u (τ n) (n : ℝ)) ∧
          (∀ᶠ n : ℕ in atTop,
            h3PathCanonicalGradientExactBalanceBudgetAt u (τ n) (n : ℝ))) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            ∀ n : ℕ,
              (n : ℝ) <
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
                  velocityH3EnergyAt u (τ n))) := by
  obtain ⟨i, τ, hWitness, hτT, hThirdT, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_indexedGap_or_indexedSignedMonomial
      hH3 hNoExtension hClass hb
  refine ⟨i, τ, hWitness, hτT, hThirdT, hClocks, ?_⟩
  rcases hAlternative with ⟨hi, _hGap, _hShifted⟩ | ⟨hi, j, r, hOrdered⟩
  · left
    have hBudget (n : ℕ) :
        h3PathCanonicalGradientFullDissipationBudgetAt u (τ n) (n : ℝ) := by
      have hGradient : (n : ℝ) <
          (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n))) *
            velocityH3Energy3At u (τ n) - velocityH3DissipationAt u (τ n)) /
              (9 * velocityH3EnergyAt u (τ n)) := by
        simpa [hi, h3PathCanonicalJointDirectedTenSourceAt] using
          (hWitness n).2
      exact h3PathCanonical_gradientSource_forces_fullDissipationBudget
        u (τ n) (n : ℝ) hGradient
    refine ⟨hi, hBudget, ?_⟩
    have hLate : ∀ᶠ n : ℕ in atTop, b < τ n :=
      (tendsto_order.1 hτT).1 b hb.2
    filter_upwards [hLate] with n hn
    have ht : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hn, (hWitness n).1.2⟩
    exact h3PathCanonical_gradientSource_forces_exactBalanceBudget
      hH3 hClass ht (hBudget n)
  · right
    exact ⟨hi, j, r, hOrdered⟩

end
end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceFullDissipationBudget

/-!
# Directed H³ gradient obstruction: critical full dissipation clock with top-energy share

The indexed fixed-source gradient branch retains the *full* normalized
viscous budget, including the physical top-order energy fraction E₃/E:

  9 n + D/E < 24 C₁ sqrt(E) E₃/E.

On actual H³ solution slices the exact balance gap is G = 2 D/E.  The
existing third critical physical clock is

  8 <= A_b (T-t)^2 G^3,
  A_b = 3 K² (E₀(b)+1) (4+3 E₀(b))³.

Combining these two independent estimates on the SAME selected terminal
times gives the strict moving-index top-share physical clock

  8 < A_b (T-t)^2 (2*(24 C₁ sqrt(E) E₃/E - 9*n))³.

The other possible source remains one fixed ordered signed monomial with
an indexed negative normalized deficit. Both are only conditional
necessary conditions for hypothetical nonextension. The resulting
continuation theorem explicitly assumes a top-share clock ceiling and a
signed-channel ceiling; neither is asserted to follow automatically.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- The third critical physical clock after inserting the actual full
viscous gradient budget; unlike the earlier shifted clock, the numerator
retains the precise top-order energy fraction `E₃/E`. -/
def h3PathCanonicalGradientTopShareClockAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t R : ℝ) : Prop :=
  8 <
    3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (velocityH3Energy0At u b + 1) *
      (4 + 3 * velocityH3Energy0At u b) ^ 3 *
      (T - t) ^ 2 *
      (2 * ((24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        velocityH3Energy3At u t) / velocityH3EnergyAt u t - 9 * R)) ^ 3

/-- Full PDE dissipative budget plus the actual third critical clock yields
one strict top-energy-share clock at the same physical time. -/
theorem h3PathCanonical_gradientFullBudget_forces_topShareClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hCritical : h3PathCanonicalDirectedCriticalClocksAt u T b t)
    (hBudget : h3PathCanonicalGradientFullDissipationBudgetAt u t R) :
    h3PathCanonicalGradientTopShareClockAt u T b t R := by
  have hExact := h3PathCanonical_gradientSource_forces_exactBalanceBudget
    hH3 hClass ht hBudget
  have hBalance :=
    normalized_negativeTransport_sub_deriv_eq_two_mul_dissipation_div_energy
      hH3 hClass ht
  have hEnergy : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hGapNonneg :
      0 ≤ (-velocityH3TransportDerivativeAt u t -
        deriv (velocityH3EnergyAt u) t) / velocityH3EnergyAt u t := by
    rw [hBalance]
    exact mul_nonneg (by norm_num)
      (div_nonneg hD (le_of_lt hEnergy))
  have hGapStrict :
      (-velocityH3TransportDerivativeAt u t -
        deriv (velocityH3EnergyAt u) t) / velocityH3EnergyAt u t <
      2 * ((24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        velocityH3Energy3At u t) / velocityH3EnergyAt u t - 9 * R) := by
    change
      18 * R +
        ((-velocityH3TransportDerivativeAt u t -
          deriv (velocityH3EnergyAt u) t) / velocityH3EnergyAt u t) <
      2 * ((24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        velocityH3Energy3At u t) / velocityH3EnergyAt u t) at hExact
    linarith only [hExact]
  have hPower :
      ((-velocityH3TransportDerivativeAt u t -
        deriv (velocityH3EnergyAt u) t) / velocityH3EnergyAt u t) ^ 3 <
      (2 * ((24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        velocityH3Energy3At u t) / velocityH3EnergyAt u t - 9 * R)) ^ 3 :=
    pow_lt_pow_left₀ hGapStrict hGapNonneg (by norm_num)
  have hE0 : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hRic : 0 < h3PathSqrtEnergyRiccatiCoefficient :=
    h3PathSqrtEnergyRiccatiCoefficient_pos
  have hDistance : 0 < T - t := sub_pos.mpr ht.2
  have hPref :
      0 < 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        (velocityH3Energy0At u b + 1) *
        (4 + 3 * velocityH3Energy0At u b) ^ 3 * (T - t) ^ 2 := by
    positivity
  have hScaled := mul_lt_mul_of_pos_left hPower hPref
  change 8 <
    3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (velocityH3Energy0At u b + 1) *
      (4 + 3 * velocityH3Energy0At u b) ^ 3 *
      (T - t) ^ 2 *
      (2 * ((24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        velocityH3Energy3At u t) / velocityH3EnergyAt u t - 9 * R)) ^ 3
  exact lt_of_le_of_lt hCritical.2.2 hScaled

/-- The *same indexed source sequence* has either the strict full top-energy
share clock shifted by the varying index n, or an indexed deficit in one
fixed ordered signed velocity monomial. Its original three critical clocks
and top-order-energy divergence are retained. -/
theorem h3PathCanonical_fixedDirectedSource_topShareClock_or_indexedSignedMonomial
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
            h3PathCanonicalGradientTopShareClockAt u T b (τ n) (n : ℝ))) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            ∀ n : ℕ,
              (n : ℝ) <
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
                  velocityH3EnergyAt u (τ n))) := by
  obtain ⟨i, τ, hWitness, hτT, hThirdT, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_fullBudget_or_indexedSignedMonomial
      hH3 hNoExtension hClass hb
  refine ⟨i, τ, hWitness, hτT, hThirdT, hClocks, ?_⟩
  rcases hAlternative with ⟨hi, hBudget, _hExact⟩ | ⟨hi, j, r, hOrdered⟩
  · left
    refine ⟨hi, hBudget, ?_⟩
    have hLate : ∀ᶠ n : ℕ in atTop, b < τ n :=
      (tendsto_order.1 hτT).1 b hb.2
    filter_upwards [hLate, hClocks] with n hn hClock
    have ht : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hn, (hWitness n).1.2⟩
    exact h3PathCanonical_gradientFullBudget_forces_topShareClock
      hH3 hClass ht hClock (hBudget n)
  · right
    exact ⟨hi, j, r, hOrdered⟩

/-- If the zero-shift full top-energy-share clock is excluded on a strict
terminal tail, and all signed ordered monomial ratios have an upper ceiling,
then smooth continuation follows. The bounds are *extra physical premises*;
no unconditional sign or regularity theorem is asserted. -/
theorem h3PathCanonical_extension_of_topShareClockCeiling_and_signedCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hClockCeiling : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ¬ h3PathCanonicalGradientTopShareClockAt u T b t 0)
    (hSignedCeiling : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∀ j r : PrimeTensor.Axis Depth.three,
        -(2 * h3PathCanonicalFirstMonomialComponentAt u t j r) /
          velocityH3EnergyAt u t ≤ K) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨i, τ, hWitness, hτT, _hThirdT, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_topShareClock_or_indexedSignedMonomial
      hH3 hNoExtension hClass hb
  have hLate : ∀ᶠ n : ℕ in atTop, d < τ n :=
    (tendsto_order.1 hτT).1 d hd.2
  rcases hAlternative with ⟨_hi, hBudget, _hRate⟩ | ⟨_hi, j, r, hSigned⟩
  · obtain ⟨n, hnLate, hnClock⟩ := (hLate.and hClocks).exists
    have ht : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans hd.1 hnLate), (hWitness n).1.2⟩
    have hBudgetN := hBudget n
    have hBudgetZero :
        h3PathCanonicalGradientFullDissipationBudgetAt u (τ n) 0 := by
      change
        9 * (n : ℝ) +
          velocityH3DissipationAt u (τ n) / velocityH3EnergyAt u (τ n) <
          (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n))) *
            velocityH3Energy3At u (τ n)) / velocityH3EnergyAt u (τ n)
        at hBudgetN
      change
        9 * (0 : ℝ) +
          velocityH3DissipationAt u (τ n) / velocityH3EnergyAt u (τ n) <
          (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n))) *
            velocityH3Energy3At u (τ n)) / velocityH3EnergyAt u (τ n)
      have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith only [hBudgetN, hN]
    have hRate := h3PathCanonical_gradientFullBudget_forces_topShareClock
      hH3 hClass ht hnClock hBudgetZero
    exact (hClockCeiling (τ n) ⟨hnLate, (hWitness n).1.2⟩) hRate
  · have hBound : ∀ᶠ n : ℕ in atTop,
        -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
          velocityH3EnergyAt u (τ n) ≤ K := by
      filter_upwards [hLate] with n hn
      exact hSignedCeiling (τ n) ⟨hn, (hWitness n).1.2⟩ j r
    have hLarge : ∀ᶠ n : ℕ in atTop,
        K + 1 ≤
          -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
            velocityH3EnergyAt u (τ n) := by
      obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (K + 1)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hIndex : K + 1 < (n : ℝ) :=
        lt_of_lt_of_le hN (by exact_mod_cast hn)
      exact le_of_lt (lt_trans hIndex (hSigned n))
    obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
    linarith only [hnBound, hnLarge]

end
end Euclidean
end Bridge
end PrimeTensor

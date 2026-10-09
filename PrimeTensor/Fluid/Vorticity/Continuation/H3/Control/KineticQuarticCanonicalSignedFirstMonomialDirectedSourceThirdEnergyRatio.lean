import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceTopEnergy

/-!
# Fixed directed H³ obstruction forces third-order energy beyond sqrt(H³ energy)

The previous theorem synchronizes one signed directed source and the
physical top-order energy on an actual preterminal sequence. Here its
quantitative estimate

    n * sqrt(E (tau n)) < 324 * C1 * E3 (tau n)

is divided by the strictly positive sqrt(E) to prove

    E3 (tau n) / sqrt(E (tau n)) --> +infinity.

In particular an eventual upper bound E3 <= K sqrt(E), with any fixed
K >= 0, excludes nonextension. This is a sufficient continuation
criterion, not an automatic estimate or a proof of global regularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- A hypothetical nonextendible H³ path has a fixed signed directed source
and actual terminal times along which the third-order energy dominates the
square root of the full energy by an unbounded factor. -/
theorem h3PathCanonical_fixedDirectedSource_thirdEnergyOverRoot_diverges
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo
        (T - (1 : ℝ) / ((n : ℝ) + 1)) T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ =>
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          velocityH3Energy3At u (τ n) /
            Real.sqrt (velocityH3EnergyAt u (τ n))) atTop atTop := by
  obtain ⟨i, τ, hWitness, hτT, hSourceT, hRate, _hTopT⟩ :=
    h3PathCanonical_fixedDirectedSource_thirdEnergyBlowup_sameSequence
      hH3 hNoExtension hClass hb
  let C : ℝ := 324 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by norm_num)
      (le_of_lt h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos)
  have hDivRate : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) < C *
        (velocityH3Energy3At u (τ n) /
          Real.sqrt (velocityH3EnergyAt u (τ n))) := by
    filter_upwards [hRate] with n hn
    have hE : 0 < velocityH3EnergyAt u (τ n) :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u (τ n))
    have hRoot : 0 < Real.sqrt (velocityH3EnergyAt u (τ n)) :=
      Real.sqrt_pos.2 hE
    have hDiv : (n : ℝ) <
        (C * velocityH3Energy3At u (τ n)) /
          Real.sqrt (velocityH3EnergyAt u (τ n)) := by
      apply (lt_div_iff₀ hRoot).2
      simpa only [C, mul_assoc] using hn
    simpa only [mul_div_assoc] using hDiv
  have hRatioT :
      Tendsto
        (fun n : ℕ =>
          velocityH3Energy3At u (τ n) /
            Real.sqrt (velocityH3EnergyAt u (τ n))) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (C * M)
    have hNat : ∀ᶠ n : ℕ in atTop, C * M < (n : ℝ) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact lt_of_lt_of_le hN (by exact_mod_cast hn)
    filter_upwards [hDivRate, hNat] with n hLarge hn
    by_contra hFail
    have hLess :
        velocityH3Energy3At u (τ n) /
          Real.sqrt (velocityH3EnergyAt u (τ n)) ≤ M :=
      le_of_lt (lt_of_not_ge hFail)
    have hScaled := mul_le_mul_of_nonneg_left hLess hC
    exact (not_lt_of_ge hScaled) (lt_trans hn hLarge)
  exact ⟨i, τ, (fun n => (hWitness n).1), hτT, hSourceT, hRatioT⟩

/-- If the physical third-derivative energy remains below a fixed multiple
of the square root of H³ energy on one strict terminal tail, the admitted
H³ path extends smoothly. No sign assumption on the ten directed sources
and no gradient-absorption assumption are needed. -/
theorem h3PathCanonical_extension_of_eventualThirdEnergyRootCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hCeiling : ∀ t : ℝ, t ∈ Set.Ioo d T →
      velocityH3Energy3At u t ≤
        K * Real.sqrt (velocityH3EnergyAt u t)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨i, τ, hNear, hτT, _hSourceT, hRatioT⟩ :=
    h3PathCanonical_fixedDirectedSource_thirdEnergyOverRoot_diverges
      hH3 hNoExtension hClass hb
  have hLate : ∀ᶠ n : ℕ in atTop, d < τ n :=
    (tendsto_order.1 hτT).1 d hd.2
  have hBound : ∀ᶠ n : ℕ in atTop,
      velocityH3Energy3At u (τ n) /
        Real.sqrt (velocityH3EnergyAt u (τ n)) ≤ K := by
    filter_upwards [hLate] with n hn
    have ht : τ n ∈ Set.Ioo d T := ⟨hn, (hNear n).2⟩
    have hE : 0 < velocityH3EnergyAt u (τ n) :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u (τ n))
    have hRoot : 0 < Real.sqrt (velocityH3EnergyAt u (τ n)) :=
      Real.sqrt_pos.2 hE
    exact (div_le_iff₀ hRoot).2 (hCeiling (τ n) ht)
  have hLarge : ∀ᶠ n : ℕ in atTop,
      K + 1 ≤ velocityH3Energy3At u (τ n) /
        Real.sqrt (velocityH3EnergyAt u (τ n)) :=
    (tendsto_atTop.1 hRatioT) (K + 1)
  obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
  linarith only [hnBound, hnLarge]

end
end Euclidean
end Bridge
end PrimeTensor

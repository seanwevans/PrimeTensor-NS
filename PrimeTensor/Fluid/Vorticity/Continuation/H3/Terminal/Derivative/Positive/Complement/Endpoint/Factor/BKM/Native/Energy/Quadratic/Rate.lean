import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Energy.Clock.Sequence

/-!
# Quadratic H³ energy rate on the physical-clock sequence

The physical-clock sequence satisfies simultaneously

`n < (T - σ n) * velocityH3EnergyAt u (σ n)`

and

`T - σ n < 1 / (n + 1)`.

Since the H³ energy is nonnegative, the second inequality turns the first into

`n * (n + 1) < velocityH3EnergyAt u (σ n)`.

Thus hypothetical nonextension forces a terminal sequence with an explicit
quadratic lower rate for the canonical H³ energy.  This remains only a
necessary consequence conditional on failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The divergent physical-clock sequence carries a quadratic lower bound for
canonical H³ energy on the same terminal times. -/
theorem exists_h3Energy_quadraticRateSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ σ : ℕ → ℝ,
      (∀ n : ℕ,
        σ n ∈ Set.Ioo a T ∧
        σ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          (T - σ n) * velocityH3EnergyAt u (σ n) ∧
        (n : ℝ) * ((n : ℝ) + 1) <
          velocityH3EnergyAt u (σ n)) ∧
      Tendsto σ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (σ n))
        atTop atTop := by
  obtain ⟨σ, hσ, hSigmaTendsto, _hClockTendsto⟩ :=
    exists_h3EnergyPhysicalClock_blowupSequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  have hRate :
      ∀ n : ℕ,
        (n : ℝ) * ((n : ℝ) + 1) <
          velocityH3EnergyAt u (σ n) := by
    intro n

    have hGapPos : 0 < T - σ n := by
      linarith [(hσ n).2.1.2]

    have hDenPos : 0 < (n : ℝ) + 1 := by
      positivity

    have hGapUpper :
        T - σ n < 1 / ((n : ℝ) + 1) := by
      linarith [(hσ n).2.1.1]

    have hEnergyPos :
        0 < velocityH3EnergyAt u (σ n) := by
      exact lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u (σ n))

    have hClockUpper :
        (T - σ n) * velocityH3EnergyAt u (σ n) <
          (1 / ((n : ℝ) + 1)) * velocityH3EnergyAt u (σ n) :=
      mul_lt_mul_of_pos_right hGapUpper hEnergyPos

    have hRatio :
        (n : ℝ) <
          velocityH3EnergyAt u (σ n) / ((n : ℝ) + 1) := by
      have h := lt_trans (hσ n).2.2 hClockUpper
      simpa only [one_div, inv_mul_eq_div] using h

    exact
      (lt_div_iff₀ hDenPos).1 hRatio

  have hEnergyTendsto :
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (σ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (max M 0 + 1)

    filter_upwards [eventually_ge_atTop N] with n hn

    have hCast : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn

    have hNPositive : 0 < (N : ℝ) := by
      have : 0 < max M 0 + 1 := by
        linarith [le_max_right M 0]
      exact lt_trans this hN

    have hnPositive : 0 < (n : ℝ) :=
      lt_of_lt_of_le hNPositive hCast

    have hQuadraticAboveN :
        (n : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by
      nlinarith

    have hMltN : M < (n : ℝ) := by
      have hMleMax : M ≤ max M 0 := le_max_left _ _
      linarith

    exact
      le_of_lt
        (lt_trans hMltN
          (lt_trans hQuadraticAboveN (hRate n)))

  refine ⟨σ, ?_, hSigmaTendsto, hEnergyTendsto⟩
  intro n
  exact
    ⟨
      (hσ n).1,
      (hσ n).2.1,
      (hσ n).2.2,
      hRate n
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

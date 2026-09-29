import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeEnergyClockObstruction

/-!
# Terminal sequence for the H³ physical energy clock

The tail-wide obstruction says that hypothetical nonextension makes

`(T - t) * velocityH3EnergyAt u t`

unbounded on every H³ energy-class tail.  Restricting the energy class to an
arbitrarily late start therefore upgrades this to arbitrarily large physical
energy clock values arbitrarily near `T`.

Choosing the neighborhood radius `1 / (n + 1)` and threshold `n` gives a
strict preterminal sequence `σ n -> T` with

`n < (T - σ n) * velocityH3EnergyAt u (σ n)`.

Thus the physical H³ energy clock itself tends to `+∞` along a terminal
sequence.  This remains a necessary consequence conditional on hypothetical
failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Under hypothetical nonextension, the physical H³ energy clock is
arbitrarily large in every left neighborhood of the terminal time. -/
theorem h3EnergyPhysicalClock_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ ε : ℝ,
      0 < ε →
      ∀ M : ℝ,
        ∃ t : ℝ,
          t ∈ Set.Ioo (T - ε) T ∧
          t ∈ Set.Ioo a T ∧
          M < (T - t) * velocityH3EnergyAt u t := by
  intro ε hε M

  let b : ℝ := max a (T - ε)

  have hab : a ≤ b := by
    dsimp only [b]
    exact le_max_left _ _

  have hNearB : T - ε ≤ b := by
    dsimp only [b]
    exact le_max_right _ _

  have hbT : b < T := by
    dsimp only [b]
    exact max_lt hClass.terminal_start.2 (by linarith)

  have hClassB : PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left
      hClass hab hbT

  obtain ⟨t, ht, hLarge⟩ :=
    h3EnergyPhysicalClock_unbounded_on_tail_of_noH3PathExtension
      hH3 hNoExtension hClassB M

  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_of_le_of_lt hab ht.1, ht.2⟩

  have htNear : t ∈ Set.Ioo (T - ε) T :=
    ⟨lt_of_le_of_lt hNearB ht.1, ht.2⟩

  exact ⟨t, htNear, htClass, hLarge⟩

/-- There is a terminal sequence along which the dimensionless physical H³
energy clock tends to `+∞`, with the explicit lower rate `n`. -/
theorem exists_h3EnergyPhysicalClock_blowupSequence_of_noH3PathExtension
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
          (T - σ n) * velocityH3EnergyAt u (σ n)) ∧
      Tendsto σ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3EnergyAt u (σ n))
        atTop atTop := by
  have hChoice :
      ∀ n : ℕ,
        ∃ t : ℝ,
          t ∈ Set.Ioo a T ∧
          t ∈ Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
          (n : ℝ) <
            (T - t) * velocityH3EnergyAt u t := by
    intro n

    have hDen : 0 < (n : ℝ) + 1 := by
      positivity

    have hε : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      exact one_div_pos.mpr hDen

    obtain ⟨t, htNear, htClass, hLarge⟩ :=
      h3EnergyPhysicalClock_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
        hH3 hNoExtension hClass
        ((1 : ℝ) / ((n : ℝ) + 1)) hε (n : ℝ)

    exact ⟨t, htClass, htNear, hLarge⟩

  choose σ hσ using hChoice

  have hSigmaTendsto : Tendsto σ atTop (𝓝 T) := by
    rw [Metric.tendsto_atTop]
    intro ε hε

    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / ε)

    refine ⟨N, ?_⟩
    intro n hn

    have hCast : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn

    have hDenN : 0 < (N : ℝ) + 1 := by
      positivity

    have hInvN :
        (1 : ℝ) / ((n : ℝ) + 1) ≤
          1 / ((N : ℝ) + 1) := by
      exact
        one_div_le_one_div_of_le
          hDenN
          (by linarith)

    have hSmallN :
        1 / ((N : ℝ) + 1) < ε := by
      have hNPlus : 1 / ε < (N : ℝ) + 1 := by
        linarith
      have hMulRaw : 1 < ((N : ℝ) + 1) * ε :=
        (div_lt_iff₀ hε).1 hNPlus
      have hMul : 1 < ε * ((N : ℝ) + 1) := by
        simpa only [mul_comm] using hMulRaw
      exact
        (div_lt_iff₀ hDenN).2
          (by simpa only [one_mul] using hMul)

    have hSmall :
        (1 : ℝ) / ((n : ℝ) + 1) < ε :=
      lt_of_le_of_lt hInvN hSmallN

    have hLower := (hσ n).2.1.1
    have hUpper := (hσ n).2.1.2

    rw [Real.dist_eq]

    have hDiffNonpos : σ n - T ≤ 0 := by
      linarith [hUpper]

    rw [abs_of_nonpos hDiffNonpos]
    linarith

  have hClockTendsto :
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3EnergyAt u (σ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M

    filter_upwards [eventually_ge_atTop N] with n hn

    have hNat : M < (n : ℝ) := by
      exact
        lt_of_lt_of_le hN
          (by exact_mod_cast hn)

    exact
      le_of_lt
        (lt_trans hNat (hσ n).2.2)

  exact ⟨σ, hσ, hSigmaTendsto, hClockTendsto⟩

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Near.Alternative

/-!
# Sequential terminal H³ alternative

The arbitrarily-near-terminal alternative is quantified by two independent
parameters:

    ∀ ε > 0, ∀ M, ∃ t ∈ (T - ε, T), M < E_H3(t).

For later compactness and asymptotic arguments it is more useful to package
that pathology as one explicit sequence.

Choose, for each natural `n`,

    ε_n = 1 / (n + 1),
    M_n = n.

A non-extendible admissible H³ path then has times `τ n` satisfying

    T - 1/(n+1) < τ n < T
    n < E_H3(τ n).

The first pair of inequalities forces `τ n -> T`, while the second forces
`E_H3(τ n) -> +∞`.

This remains a conditional blowup alternative.  It does not assert existence
of a non-extendible solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
A hypothetical non-extendible admissible H³ path admits an explicit terminal
sequence along which the canonical normalized H³ energy tends to `+∞`.
-/
theorem exists_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ∃ τ : ℕ → ℝ,
      (
        ∀ n : ℕ,
          τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
            ∧
          (n : ℝ) < velocityH3EnergyAt u (τ n)
      )
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      Tendsto
        (fun n : ℕ =>
          velocityH3EnergyAt u (τ n))
        atTop
        atTop := by

  have hNear :=
    velocityH3EnergyAt_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
      hH3
      hNoExtension

  have hChoice :
      ∀ n : ℕ,
        ∃ t : ℝ,
          t ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
            ∧
          (n : ℝ) < velocityH3EnergyAt u t := by

    intro n

    have hDen :
        0 < (n : ℝ) + 1 := by
      positivity

    have hε :
        0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      exact one_div_pos.mpr hDen

    exact
      hNear
        ((1 : ℝ) / ((n : ℝ) + 1))
        hε
        (n : ℝ)

  choose τ hτ using hChoice

  refine
    ⟨
      τ,
      hτ,
      ?_,
      ?_
    ⟩

  · have hInv :
        Tendsto
          (fun n : ℕ =>
            (1 : ℝ) / ((n : ℝ) + 1))
          atTop
          (𝓝 0) := by

      simpa only [
        Nat.cast_add,
        Nat.cast_one
      ] using
        tendsto_one_div_add_atTop_nhds_zero_nat

    have hNormBound :
        ∀ n : ℕ,
          ‖τ n - T‖
            ≤
          (1 : ℝ) / ((n : ℝ) + 1) := by

      intro n

      have hNearN :=
        (hτ n).1

      rw [
        Real.norm_eq_abs,
        abs_of_nonpos
          (sub_nonpos.mpr
            (le_of_lt hNearN.2))
      ]

      linarith [hNearN.1]

    exact
      (tendsto_iff_norm_sub_tendsto_zero).2
        (
          squeeze_zero'
            (Filter.Eventually.of_forall
              (fun n =>
                norm_nonneg (τ n - T)))
            (Filter.Eventually.of_forall
              hNormBound)
            hInv
        )

  · refine
      tendsto_atTop.2
        ?_

    intro M

    have hNatLarge :
        ∀ᶠ n : ℕ in atTop,
          M < (n : ℝ) := by

      obtain ⟨N : ℕ, hN⟩ :=
        exists_nat_gt M

      filter_upwards [eventually_ge_atTop N] with n hn

      exact
        lt_of_lt_of_le
          hN
          (by exact_mod_cast hn)

    filter_upwards [hNatLarge] with n hn

    exact
      le_of_lt
        (lt_trans
          hn
          (hτ n).2)

/--
Neutral terminal formulation with the non-extension branch represented by one
actual asymptotic sequence.

Either the path extends smoothly through `T`, or there is a strict preterminal
sequence converging to `T` along which the canonical H³ energy tends to `+∞`;
in the latter case the exact full-dissipation transport excess is still
nonintegrable on every terminal energy-class tail.
-/
theorem h3Path_extension_or_energyBlowupSequenceAndExcessPathology
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      (
        ∃ τ : ℕ → ℝ,
          (
            ∀ n : ℕ,
              τ n <
                T
          )
            ∧
          Tendsto τ atTop (𝓝 T)
            ∧
          Tendsto
            (fun n : ℕ =>
              velocityH3EnergyAt u (τ n))
            atTop
            atTop
      )
        ∧
      (
        ∀
          (a : ℝ)
          (hClass : PreterminalH3EnergyClass u a T),
            ¬ MeasureTheory.IntegrableOn
                (h3PathFullDissipationTransportExcessRate u)
                (Set.Ioo a T)
      )
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · right

    obtain
      ⟨τ, hτ, hτTendsto, hEnergyTendsto⟩ :=
      exists_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
        hH3
        hExtension

    refine
      ⟨
        ?_,
        not_integrableFullDissipationTransportExcessRateOnEveryTail_of_noH3PathExtension
          hH3
          hExtension
      ⟩

    exact
      ⟨
        τ,
        (fun n => (hτ n).1.2),
        hτTendsto,
        hEnergyTendsto
      ⟩

end

end Euclidean
end Bridge
end PrimeTensor

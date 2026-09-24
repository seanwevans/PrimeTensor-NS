import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathTerminalDichotomy

/-!
# Arbitrarily-near-terminal H³ alternative

The neutral terminal dichotomy already shows that a non-extendible admissible
H³ path has unbounded canonical H³ energy on every terminal tail.

This file sharpens only the quantifiers.  If a particular path does not extend,
then for every terminal neighborhood width `ε > 0` and every finite level `M`,
there is a time

    T - ε < t < T

with

    M < E_H3(t).

Thus a hypothetical failure of continuation forces arbitrarily large H³-energy
spikes arbitrarily close to the terminal time.

This remains a conditional blowup alternative.  It does not assert existence
of a non-extendible path, monotone divergence of the energy, or a limit
`E_H3(t) -> +∞`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- If an admissible H³ path does not extend, then arbitrarily large values of
its canonical H³ energy occur arbitrarily close to the terminal time. -/
theorem velocityH3EnergyAt_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ∀ ε : ℝ,
      0 < ε →
      ∀ M : ℝ,
        ∃ t : ℝ,
          t ∈ Set.Ioo (T - ε) T
            ∧
          M < velocityH3EnergyAt u t := by

  obtain
    ⟨a₀, hClass⟩ :=
    h3Preterminal_energyClass_of_h3PathAdmissible
      hH3

  intro ε hε M

  let a : ℝ :=
    max
      a₀
      (T - ε / 2)

  have haPos :
      0 < a := by
    exact
      lt_of_lt_of_le
        hClass.terminal_start.1
        (le_max_left _ _)

  have hNearLtT :
      T - ε / 2 < T := by
    linarith

  have haT :
      a < T := by
    dsimp only [a]
    exact
      max_lt
        hClass.terminal_start.2
        hNearLtT

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    ⟨haPos, haT⟩

  obtain
    ⟨t, ht, hMt⟩ :=
    velocityH3EnergyAt_unboundedOnEveryTail_of_noH3PathExtension
      hH3 hNoExtension
      a ha M

  have hNear :
      T - ε < t := by

    have hHalfNear :
        T - ε < T - ε / 2 := by
      linarith

    have hBaseLe :
        T - ε / 2 ≤ a := by
      dsimp only [a]
      exact le_max_right _ _

    exact
      lt_of_lt_of_le
        hHalfNear
        (le_trans hBaseLe ht.1)

  exact
    ⟨
      t,
      ⟨hNear, ht.2⟩,
      hMt
    ⟩

/-- Exhaustive neutral formulation with the terminal pathology quantified in
actual neighborhoods of `T`.

Either the path extends smoothly, or arbitrarily large H³-energy spikes occur
inside every left neighborhood of `T` and the exact full-dissipation transport
excess rate is nonintegrable on every terminal H³ energy-class tail.
-/
theorem h3Path_extension_or_arbitrarilyNearEnergyAndExcessPathology
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
        ∀ ε : ℝ,
          0 < ε →
          ∀ M : ℝ,
            ∃ t : ℝ,
              t ∈ Set.Ioo (T - ε) T
                ∧
              M < velocityH3EnergyAt u t
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

  · exact Or.inl hExtension

  · refine Or.inr ⟨?_, ?_⟩

    · exact
        velocityH3EnergyAt_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
          hH3 hExtension

    · exact
        not_integrableFullDissipationTransportExcessRateOnEveryTail_of_noH3PathExtension
          hH3 hExtension

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathFullDissipationExcessRate

/-!
# Neutral terminal alternative for an admissible H³ path

The preceding files isolated several necessary conditions for a hypothetical
failure of continuation.  This file packages them without choosing a side.

For one fixed admissible H³ path, classical excluded middle gives two branches:

1. the path extends smoothly through `T`; or
2. the path does not extend.

The second branch now has two rigorous consequences already available from the
closed restart and exact dissipative-balance machinery:

* the canonical H³ energy is unbounded on every terminal tail;
* the exact full-dissipation transport excess rate is nonintegrable on every
  terminal H³ energy-class tail.

The first statement is deliberately quantified as

    ∀ a ∈ (0,T), ∀ M, ∃ t ∈ [a,T), M < E_H3(t).

This is a terminal `limsup = +∞` type statement.  It does **not** assert that
`E_H3(t)` tends monotonically to infinity as `t ↑ T`, and the theorem does not
assert that the non-extension branch is realized by any solution.

Thus this is an exhaustive continuation-or-pathology dichotomy, not a blowup
existence theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A uniform bound for the canonical H³ energy on one terminal tail produces
the componentwise terminal H³ control required by the closed restart theorem. -/
theorem terminalTailH3Control_of_velocityH3EnergyBoundOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ha : a ∈ Set.Ioo (0 : ℝ) T)
    (hM : 1 ≤ M)
    (hBound :
      ∀ t : ℝ,
        t ∈ Set.Ico a T →
          velocityH3EnergyAt u t ≤ M) :
    TerminalTailH3Control u T := by

  refine
    ⟨
      a,
      M,
      ha,
      ?_,
      ?_
    ⟩

  · linarith

  · intro t ht

    have htAbs :
        t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_of_lt_of_le ha.1 ht.1,
        ht.2
      ⟩

    have hInt :
        VelocityH3IntegrableAt u t :=
      hH3.velocity_h3_integrable t htAbs

    have hCanonical :
        VelocityH3BoundAt
          u t
          (velocityH3EnergyAt u t) :=
      velocityH3BoundAt_canonical
        u t hInt

    exact
      velocityH3BoundAt_mono
        hCanonical
        (hBound t ht)

/-- Consequently, one finite scalar H³-energy ceiling on one terminal tail is
already enough to continue the path smoothly through `T`. -/
theorem h3PathExtension_of_velocityH3EnergyBoundOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ha : a ∈ Set.Ioo (0 : ℝ) T)
    (hM : 1 ≤ M)
    (hBound :
      ∀ t : ℝ,
        t ∈ Set.Ico a T →
          velocityH3EnergyAt u t ≤ M) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hTail :
      TerminalTailH3Control u T :=
    terminalTailH3Control_of_velocityH3EnergyBoundOnTail
      hH3 ha hM hBound

  exact
    h3PathH3ControlProducesExtension
      u T hH3 hTail

/-- Path-specific H³ blowup alternative in the precise unbounded-tail sense.

If this admissible path does not extend, then every terminal tail contains
arbitrarily large values of the canonical normalized H³ energy.
-/
theorem velocityH3EnergyAt_unboundedOnEveryTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ∀
      (a : ℝ),
        a ∈ Set.Ioo (0 : ℝ) T →
        ∀ M : ℝ,
          ∃ t : ℝ,
            t ∈ Set.Ico a T
              ∧
            M < velocityH3EnergyAt u t := by

  intro a ha M

  by_contra hNoLarge

  let N : ℝ :=
    max 1 M

  have hN :
      1 ≤ N := by
    dsimp only [N]
    exact le_max_left _ _

  have hMN :
      M ≤ N := by
    dsimp only [N]
    exact le_max_right _ _

  have hBound :
      ∀ t : ℝ,
        t ∈ Set.Ico a T →
          velocityH3EnergyAt u t ≤ N := by

    intro t ht

    apply le_of_not_gt

    intro hLarge

    apply hNoLarge

    exact
      ⟨
        t,
        ht,
        lt_of_le_of_lt hMN hLarge
      ⟩

  exact
    hNoExtension
      (h3PathExtension_of_velocityH3EnergyBoundOnTail
        hH3 ha hN hBound)

/-- Exhaustive neutral terminal dichotomy.

Either the given H³ path extends, or both of the currently proved necessary
terminal pathologies hold: H³ energy is unbounded on every tail and the exact
full-dissipation transport excess rate is nonintegrable on every energy-class
tail.
-/
theorem h3Path_extension_or_terminalEnergyAndExcessPathology
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
        ∀
          (a : ℝ),
            a ∈ Set.Ioo (0 : ℝ) T →
            ∀ M : ℝ,
              ∃ t : ℝ,
                t ∈ Set.Ico a T
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
        velocityH3EnergyAt_unboundedOnEveryTail_of_noH3PathExtension
          hH3 hExtension

    · exact
        not_integrableFullDissipationTransportExcessRateOnEveryTail_of_noH3PathExtension
          hH3 hExtension

end

end Euclidean
end Bridge
end PrimeTensor

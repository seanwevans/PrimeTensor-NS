import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.FullEnergyNormalizedCascade

/-!
# Full-energy dissipation continuation criteria

The preceding full-energy normalized cascade proves that hypothetical
nonextension forces

    D(t) / E(t) -> +∞    as t ↑ T,

where

    E(t) = velocityH3EnergyAt u t,
    D(t) = velocityH3DissipationAt u t.

This immediately yields useful positive continuation criteria.

A uniform linear terminal bound

    D(t) ≤ C E(t)

on any sufficiently late tail rules out nonextension.

In fact, eventual boundedness is stronger than necessary.  It is enough that
for one finite constant `C` the inequality

    D(t) ≤ C E(t)

holds at arbitrarily late times.  Such a cofinal bounded-ratio sequence is
incompatible with the full limit `D/E -> +∞`.

The same statements are also recorded for the top dissipation `D₃`, since
hypothetical nonextension already forces

    D₃(t) / E(t) -> +∞.

These are contrapositives of necessary nonextension pathologies; they do not
assert that either branch occurs a priori.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Eventual full-dissipation bound -/

/--
If the full H³ dissipation is eventually bounded by a fixed multiple of the
full H³ energy along the left terminal neighborhood, then smooth continuation
exists across `T`.
-/
theorem exists_smoothContinuationExtension_of_eventually_dissipation_le_const_mul_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hBound :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        velocityH3DissipationAt u t
          ≤
        C * velocityH3EnergyAt u t) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  have hRatio :=
    velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hLower :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        C + 1
          ≤
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t :=
    hRatio.eventually
      (eventually_ge_atTop (C + 1))

  obtain
    ⟨t, hLowerT, hBoundT⟩ :=
    (hLower.and hBound).exists

  have hEnergyPos :
      0 < velocityH3EnergyAt u t := by

    have hOne :=
      one_le_velocityH3EnergyAt
        u t

    linarith

  have hUpperT :
      velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
        ≤
      C :=
    (div_le_iff₀ hEnergyPos).2
      hBoundT

  linarith

/--
Tail form: a fixed linear dissipation-to-energy bound on any strict terminal
subtail forces smooth continuation.
-/
theorem exists_smoothContinuationExtension_of_dissipation_le_const_mul_energy_on_terminalTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hBound :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
        velocityH3DissipationAt u t
          ≤
        C * velocityH3EnergyAt u t) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        velocityH3DissipationAt u t
          ≤
        C * velocityH3EnergyAt u t := by

    filter_upwards
      [
        Ioo_mem_nhdsLT hb.2
      ]
      with t ht

    exact
      hBound
        t
        ht

  exact
    exists_smoothContinuationExtension_of_eventually_dissipation_le_const_mul_energy
      hH3
      hClass
      hEventually

/-! ## Cofinal bounded-ratio criterion -/

/--
Eventual boundedness is unnecessary.  If one fixed linear bound

    D(t) ≤ C E(t)

recurs arbitrarily late in the energy-class terminal interval, smooth
continuation exists.
-/
theorem exists_smoothContinuationExtension_of_dissipation_le_const_mul_energy_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hRecurring :
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          velocityH3DissipationAt u t
            ≤
          C * velocityH3EnergyAt u t) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  have hRatio :=
    velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hLower :
      {t : ℝ |
        C + 1
          ≤
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t}
        ∈
      𝓝[<] T :=
    hRatio.eventually
      (eventually_ge_atTop (C + 1))

  obtain
    ⟨d, hdT, hdSubset⟩ :=
    (
      mem_nhdsLT_iff_exists_Ioo_subset
    ).1
      hLower

  let c : ℝ :=
    max
      d
      (h3BKMKineticTailMidpoint a T)

  have hMid :
      h3BKMKineticTailMidpoint a T
        ∈
      Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo
      hClass.terminal_start.2

  have hc :
      c ∈ Set.Ioo a T := by

    constructor

    · dsimp only [c]

      exact
        lt_of_lt_of_le
          hMid.1
          (le_max_right _ _)

    · dsimp only [c]

      exact
        max_lt
          hdT
          hMid.2

  obtain
    ⟨t, ht, hBoundT⟩ :=
    hRecurring
      c
      hc

  have hdt :
      t ∈ Set.Ioo d T := by

    constructor

    · exact
        lt_of_le_of_lt
          (le_max_left
            d
            (h3BKMKineticTailMidpoint a T))
          ht.1

    · exact
        ht.2

  have hLowerT :
      C + 1
        ≤
      velocityH3DissipationAt u t
        /
      velocityH3EnergyAt u t :=
    hdSubset
      hdt

  have hEnergyPos :
      0 < velocityH3EnergyAt u t := by

    have hOne :=
      one_le_velocityH3EnergyAt
        u t

    linarith

  have hUpperT :
      velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
        ≤
      C :=
    (div_le_iff₀ hEnergyPos).2
      hBoundT

  linarith

/-! ## Top-dissipation analogues -/

/--
An eventual bound `D₃ ≤ C E` also forces smooth continuation.
-/
theorem exists_smoothContinuationExtension_of_eventually_dissipation3_le_const_mul_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hBound :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        velocityH3Dissipation3At u t
          ≤
        C * velocityH3EnergyAt u t) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  have hRatio :=
    velocityH3Dissipation3At_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hLower :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        C + 1
          ≤
        velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t :=
    hRatio.eventually
      (eventually_ge_atTop (C + 1))

  obtain
    ⟨t, hLowerT, hBoundT⟩ :=
    (hLower.and hBound).exists

  have hEnergyPos :
      0 < velocityH3EnergyAt u t := by

    have hOne :=
      one_le_velocityH3EnergyAt
        u t

    linarith

  have hUpperT :
      velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t
        ≤
      C :=
    (div_le_iff₀ hEnergyPos).2
      hBoundT

  linarith

/--
A cofinal fixed bound `D₃ ≤ C E` is likewise sufficient for continuation.
-/
theorem exists_smoothContinuationExtension_of_dissipation3_le_const_mul_energy_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hRecurring :
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          velocityH3Dissipation3At u t
            ≤
          C * velocityH3EnergyAt u t) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  have hRatio :=
    velocityH3Dissipation3At_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hLower :
      {t : ℝ |
        C + 1
          ≤
        velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t}
        ∈
      𝓝[<] T :=
    hRatio.eventually
      (eventually_ge_atTop (C + 1))

  obtain
    ⟨d, hdT, hdSubset⟩ :=
    (
      mem_nhdsLT_iff_exists_Ioo_subset
    ).1
      hLower

  let c : ℝ :=
    max
      d
      (h3BKMKineticTailMidpoint a T)

  have hMid :
      h3BKMKineticTailMidpoint a T
        ∈
      Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo
      hClass.terminal_start.2

  have hc :
      c ∈ Set.Ioo a T := by

    constructor

    · dsimp only [c]

      exact
        lt_of_lt_of_le
          hMid.1
          (le_max_right _ _)

    · dsimp only [c]

      exact
        max_lt
          hdT
          hMid.2

  obtain
    ⟨t, ht, hBoundT⟩ :=
    hRecurring
      c
      hc

  have hdt :
      t ∈ Set.Ioo d T := by

    constructor

    · exact
        lt_of_le_of_lt
          (le_max_left
            d
            (h3BKMKineticTailMidpoint a T))
          ht.1

    · exact
        ht.2

  have hLowerT :
      C + 1
        ≤
      velocityH3Dissipation3At u t
        /
      velocityH3EnergyAt u t :=
    hdSubset
      hdt

  have hEnergyPos :
      0 < velocityH3EnergyAt u t := by

    have hOne :=
      one_le_velocityH3EnergyAt
        u t

    linarith

  have hUpperT :
      velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t
        ≤
      C :=
    (div_le_iff₀ hEnergyPos).2
      hBoundT

  linarith

/-! ## Exact contrapositive formulations -/

/--
Failure of the full terminal divergence `D/E -> +∞` forces smooth
continuation.
-/
theorem exists_smoothContinuationExtension_of_not_dissipation_div_energy_tendsto_atTop_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNotRatio :
      ¬ Tendsto
          (
            fun t : ℝ =>
              velocityH3DissipationAt u t
                /
              velocityH3EnergyAt u t
          )
          (𝓝[<] T)
          atTop) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  exact
    hNotRatio
      (
        velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
          hH3
          hNoExtension
          hClass
      )

/--
Failure of the top-dissipation normalized divergence `D₃/E -> +∞` also forces
smooth continuation.
-/
theorem exists_smoothContinuationExtension_of_not_dissipation3_div_energy_tendsto_atTop_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNotRatio :
      ¬ Tendsto
          (
            fun t : ℝ =>
              velocityH3Dissipation3At u t
                /
              velocityH3EnergyAt u t
          )
          (𝓝[<] T)
          atTop) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  exact
    hNotRatio
      (
        velocityH3Dissipation3At_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
          hH3
          hNoExtension
          hClass
      )

end

end Euclidean
end Bridge
end PrimeTensor

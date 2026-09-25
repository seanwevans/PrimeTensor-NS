import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.Integrability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Tail.Low.From.Derivative.Identities

/-!
# Terminal derivative-energy blowup sequence

The terminal Riccati argument forces the full normalized H³ energy to become
unbounded along a sequence approaching a hypothetical nonextendible terminal
time.

The exact order-zero energy identity gives more structure: the kinetic
zeroth-order block is antitone on every strict H³ energy-class tail.  Hence it
is uniformly bounded on every later tail.

Since

    E_H3(t)
      =
    1 + E₀(t) + E₁(t) + E₂(t) + E₃(t),

full H³ blowup therefore cannot be carried by the `L²` kinetic mass.  Along a
terminal blowup sequence the aggregate positive-derivative energy

    E₁ + E₂ + E₃

must itself tend to `+∞`.

This remains a necessary-condition theorem for a hypothetical nonextendible
path.  It does not assert existence of such a path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A nonextendible admissible H³ path has a terminal sequence along which the
sum of its first-, second-, and third-order spatial energy blocks tends to
`+∞`. -/
theorem exists_velocityH3PositiveDerivativeEnergy_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ τ : ℕ → ℝ,
      (
        ∀ n : ℕ,
          τ n < T
      )
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Energy1At u (τ n)
              +
            velocityH3Energy2At u (τ n)
              +
            velocityH3Energy3At u (τ n)
        )
        atTop
        atTop := by

  obtain
    ⟨τ, hτ, hτTendsto, hEnergyTendsto⟩ :=
    exists_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  have hKineticAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3
      hClass

  have hTauAbove :
      ∀ᶠ n : ℕ in atTop,
        b < τ n :=
    (tendsto_order.1 hτTendsto).1
      b
      hb.2

  have hKineticBound :
      ∀ᶠ n : ℕ in atTop,
        velocityH3Energy0At u (τ n)
          ≤
        velocityH3Energy0At u b := by

    filter_upwards [hTauAbove] with n hbn

    have hτMem :
        τ n ∈ Set.Ioo a T := by
      exact
        ⟨
          lt_trans hb.1 hbn,
          (hτ n).1.2
        ⟩

    exact
      hKineticAnti
        hb
        hτMem
        (le_of_lt hbn)

  have hHighTendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Energy1At u (τ n)
              +
            velocityH3Energy2At u (τ n)
              +
            velocityH3Energy3At u (τ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hEnergyLarge :
        ∀ᶠ n : ℕ in atTop,
          M + 1 + velocityH3Energy0At u b
            <
          velocityH3EnergyAt u (τ n) :=
      hEnergyTendsto.eventually
        (eventually_gt_atTop
          (M + 1 + velocityH3Energy0At u b))

    filter_upwards
      [hEnergyLarge, hKineticBound]
      with n hLarge hE0

    unfold velocityH3EnergyAt at hLarge

    linarith

  exact
    ⟨
      τ,
      (fun n => (hτ n).1.2),
      hτTendsto,
      hHighTendsto
    ⟩

/-- Quantified version: positive-derivative H³ energy is arbitrarily large
arbitrarily near a nonextendible terminal time. -/
theorem velocityH3PositiveDerivativeEnergy_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ ε : ℝ,
      0 < ε →
      ∀ M : ℝ,
        ∃ t : ℝ,
          t ∈ Set.Ioo (T - ε) T
            ∧
          M
            <
          velocityH3Energy1At u t
            +
          velocityH3Energy2At u t
            +
          velocityH3Energy3At u t := by

  intro ε hε M

  obtain
    ⟨τ, hτT, hτTendsto, hHighTendsto⟩ :=
    exists_velocityH3PositiveDerivativeEnergy_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hNear :
      ∀ᶠ n : ℕ in atTop,
        T - ε < τ n :=
    (tendsto_order.1 hτTendsto).1
      (T - ε)
      (by linarith)

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        M
          <
        velocityH3Energy1At u (τ n)
          +
        velocityH3Energy2At u (τ n)
          +
        velocityH3Energy3At u (τ n) :=
    hHighTendsto.eventually
      (eventually_gt_atTop M)

  obtain ⟨n, hnNear, hnLarge⟩ :=
    (hNear.and hLarge).exists

  exact
    ⟨
      τ n,
      ⟨
        hnNear,
        hτT n
      ⟩,
      hnLarge
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

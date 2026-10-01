import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Energy.Quadratic.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Sequence

/-!
# Quadratic positive-derivative H³ energy rate on the physical-clock sequence

The physical-clock extraction gives one terminal sequence with

`n * (n + 1) < velocityH3EnergyAt u (σ n)`.

The zeroth-order kinetic block is antitone on every H³ energy-class tail, hence
it is uniformly bounded after any fixed later anchor.  Removing this bounded
block from

`velocityH3EnergyAt = 1 + E₀ + E₁ + E₂ + E₃`

shows that the same terminal sequence carries a quadratic lower rate in the
positive-derivative energy, up to one fixed additive constant.

This is a necessary consequence conditional on hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- On the physical-clock quadratic sequence, the positive-derivative H³
energy has the same quadratic lower rate modulo one fixed kinetic offset. -/
theorem exists_h3PositiveDerivativeEnergy_quadraticRateSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ σ : ℕ → ℝ, ∃ C : ℝ,
      0 ≤ C ∧
      (∀ n : ℕ,
        σ n ∈ Set.Ioo a T ∧
        σ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          (T - σ n) * velocityH3EnergyAt u (σ n) ∧
        (n : ℝ) * ((n : ℝ) + 1) <
          velocityH3EnergyAt u (σ n)) ∧
      Tendsto σ atTop (𝓝 T) ∧
      (∀ᶠ n : ℕ in atTop,
        (n : ℝ) * ((n : ℝ) + 1) - C <
          velocityH3Energy1At u (σ n) +
          velocityH3Energy2At u (σ n) +
          velocityH3Energy3At u (σ n)) ∧
      Tendsto
        (fun n : ℕ =>
          velocityH3Energy1At u (σ n) +
          velocityH3Energy2At u (σ n) +
          velocityH3Energy3At u (σ n))
        atTop atTop := by
  obtain ⟨σ, hσ, hSigmaTendsto, hEnergyTendsto⟩ :=
    exists_h3Energy_quadraticRateSequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  let b : ℝ := h3BKMKineticTailMidpoint a T

  have hb : b ∈ Set.Ioo a T := by
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

  have hSigmaAbove :
      ∀ᶠ n : ℕ in atTop, b < σ n :=
    (tendsto_order.1 hSigmaTendsto).1 b hb.2

  have hKineticBound :
      ∀ᶠ n : ℕ in atTop,
        velocityH3Energy0At u (σ n) ≤ velocityH3Energy0At u b := by
    filter_upwards [hSigmaAbove] with n hbn
    exact
      hKineticAnti
        hb
        (hσ n).1
        (le_of_lt hbn)

  let C : ℝ := 1 + velocityH3Energy0At u b

  have hCNonneg : 0 ≤ C := by
    dsimp only [C]
    have hE0 : 0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg u b
    linarith

  have hPositiveRate :
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * ((n : ℝ) + 1) - C <
          velocityH3Energy1At u (σ n) +
          velocityH3Energy2At u (σ n) +
          velocityH3Energy3At u (σ n) := by
    filter_upwards [hKineticBound] with n hE0Bound
    have hFullRate := (hσ n).2.2.2
    unfold velocityH3EnergyAt at hFullRate
    dsimp only [C]
    linarith

  have hPositiveTendsto :
      Tendsto
        (fun n : ℕ =>
          velocityH3Energy1At u (σ n) +
          velocityH3Energy2At u (σ n) +
          velocityH3Energy3At u (σ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    have hEnergyLarge :
        ∀ᶠ n : ℕ in atTop,
          M + 1 + velocityH3Energy0At u b <
            velocityH3EnergyAt u (σ n) :=
      hEnergyTendsto.eventually
        (eventually_gt_atTop
          (M + 1 + velocityH3Energy0At u b))

    filter_upwards [hEnergyLarge, hKineticBound] with n hLarge hE0Bound
    unfold velocityH3EnergyAt at hLarge
    linarith

  exact
    ⟨
      σ,
      C,
      hCNonneg,
      hσ,
      hSigmaTendsto,
      hPositiveRate,
      hPositiveTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Energy.Clock.Top.Order.Rate

/-!
# Divergent top-order physical H³ energy clock

The synchronized physical-energy-clock sequence already satisfies

`n < (T - σ n) * velocityH3EnergyAt u (σ n)`

and, eventually,

`(n + 1)^2 ≤ 3 K^2 * velocityH3Energy3At u (σ n)`.

The endpoint interpolation estimate

`E ≤ 1 + 3 (E₀ + E₃)`

and antitonicity of the zeroth-order kinetic block show more.  Once the same
sequence lies beyond the fixed kinetic midpoint, `E₀(σ n)` is bounded by the
single constant `E₀(b)`.  Hence the divergent physical full-energy clock must
be carried by the third-order block itself:

`(n - C) / 3 < (T - σ n) * E₃(σ n)`

for one fixed nonnegative `C`.  Consequently the top-order physical clock tends
to `+∞` along exactly the same terminal sequence.

This remains a necessary consequence conditional on hypothetical failure of
smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The divergent physical full-energy clock transfers to the third-order H³
block on the same synchronized terminal sequence. -/
theorem exists_h3EnergyPhysicalClock_with_energy3PhysicalClockDivergenceSequence_of_noH3PathExtension
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
        ((n : ℝ) + 1) ^ 2 ≤
          3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
            velocityH3Energy3At u (σ n)) ∧
      (∀ᶠ n : ℕ in atTop,
        ((n : ℝ) - C) / 3 <
          (T - σ n) * velocityH3Energy3At u (σ n)) ∧
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3Energy3At u (σ n))
        atTop atTop := by
  obtain ⟨σ, hσ, hSigmaTendsto, hIndexedE3⟩ :=
    exists_h3EnergyPhysicalClock_with_energy3QuadraticRateSequence_of_noH3PathExtension
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

  have hSigmaAboveB :
      ∀ᶠ n : ℕ in atTop, b < σ n :=
    (tendsto_order.1 hSigmaTendsto).1 b hb.2

  let C : ℝ := 1 + 3 * velocityH3Energy0At u b

  have hCNonneg : 0 ≤ C := by
    dsimp only [C]
    have hE0 : 0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg u b
    linarith

  have hPhysicalE3Rate :
      ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) - C) / 3 <
          (T - σ n) * velocityH3Energy3At u (σ n) := by
    filter_upwards [hSigmaAboveB] with n hbn

    have hClassN : σ n ∈ Set.Ioo a T :=
      (hσ n).1

    have hNearN :
        σ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T :=
      (hσ n).2.1

    have hClockN :
        (n : ℝ) <
          (T - σ n) * velocityH3EnergyAt u (σ n) :=
      (hσ n).2.2.1

    have hE0Bound :
        velocityH3Energy0At u (σ n) ≤
          velocityH3Energy0At u b :=
      hKineticAnti
        hb
        hClassN
        (le_of_lt hbn)

    have hEndpoint :
        velocityH3EnergyAt u (σ n) ≤
          1 + 3 *
            (velocityH3Energy0At u (σ n) +
              velocityH3Energy3At u (σ n)) :=
      velocityH3EnergyAt_le_one_add_three_mul_energy0_add_energy3_on_h3Path
        hH3
        hClass
        hClassN

    have hEndpointAnchor :
        velocityH3EnergyAt u (σ n) ≤
          C + 3 * velocityH3Energy3At u (σ n) := by
      dsimp only [C]
      linarith

    have hDistancePos : 0 < T - σ n := by
      linarith [hNearN.2]

    have hScaledEndpoint :
        (T - σ n) * velocityH3EnergyAt u (σ n) ≤
          (T - σ n) *
            (C + 3 * velocityH3Energy3At u (σ n)) :=
      mul_le_mul_of_nonneg_left
        hEndpointAnchor
        (le_of_lt hDistancePos)

    have hDenPos : 0 < (n : ℝ) + 1 := by
      positivity

    have hDistanceUpper :
        T - σ n < 1 / ((n : ℝ) + 1) := by
      linarith [hNearN.1]

    have hOneLeDen :
        (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith

    have hInvLeOne :
        (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      have h :=
        one_div_le_one_div_of_le
          (by norm_num : (0 : ℝ) < 1)
          hOneLeDen
      simpa using h

    have hDistanceLeOne :
        T - σ n ≤ 1 :=
      le_trans
        (le_of_lt hDistanceUpper)
        hInvLeOne

    have hDistanceC :
        (T - σ n) * C ≤ C := by
      have h :=
        mul_le_mul_of_nonneg_right
          hDistanceLeOne
          hCNonneg
      simpa using h

    nlinarith

  have hPhysicalE3Top :
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3Energy3At u (σ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    obtain ⟨N : ℕ, hN⟩ :=
      exists_nat_gt (max (3 * M + C) 0 + 1)

    filter_upwards
      [hPhysicalE3Rate, eventually_ge_atTop N]
      with n hRateN hn

    have hCast : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn

    have hLeMax :
        3 * M + C ≤ max (3 * M + C) 0 :=
      le_max_left _ _

    have hThreshold :
        M < ((n : ℝ) - C) / 3 := by
      linarith

    exact
      le_of_lt
        (lt_trans hThreshold hRateN)

  exact
    ⟨
      σ,
      C,
      hCNonneg,
      hσ,
      hSigmaTendsto,
      hIndexedE3,
      hPhysicalE3Rate,
      hPhysicalE3Top
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Energy.Quadratic.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Top.Frequency.Cascade

/-!
# Top-order H³ rate on the divergent physical-energy-clock sequence

The physical-energy-clock extraction supplies one strict terminal sequence
`σ n -> T` with

* `n < (T - σ n) * velocityH3EnergyAt u (σ n)`, and
* `n (n + 1) < velocityH3EnergyAt u (σ n)`.

Independently, hypothetical nonextension forces the third-order block `E₃` to
obey a pointwise inverse-square terminal lower rate on every sufficiently late
H³ energy-class tail.  Applying that pointwise theorem to the same physical-
clock sequence yields, eventually,

`(n + 1)^2 ≤ 3 K^2 * velocityH3Energy3At u (σ n)`.

Thus the divergent physical H³ energy clock can be synchronized with explicit
top-order growth without changing the selected terminal times.  This remains a
necessary consequence conditional on hypothetical failure of smooth
continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The divergent physical-energy-clock sequence also carries the canonical
indexed inverse-square lower rate in the third-order H³ energy block. -/
theorem exists_h3EnergyPhysicalClock_with_energy3QuadraticRateSequence_of_noH3PathExtension
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
      (∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ 2 ≤
          3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
            velocityH3Energy3At u (σ n)) := by
  obtain ⟨σ, hσ, hSigmaTendsto, _hEnergyTendsto⟩ :=
    exists_h3Energy_quadraticRateSequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  let b : ℝ := h3BKMKineticTailMidpoint a T

  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  obtain ⟨c, hc, hLate⟩ :=
    exists_terminalTail_kineticAnchorTerm_le_three
      u T b hb.2

  have hSigmaAboveC :
      ∀ᶠ n : ℕ in atTop, c < σ n :=
    (tendsto_order.1 hSigmaTendsto).1 c hc.2

  have hIndexedE3 :
      ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ 2 ≤
          3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
            velocityH3Energy3At u (σ n) := by
    filter_upwards [hSigmaAboveC] with n hcn

    have hClassN : σ n ∈ Set.Ioo a T :=
      (hσ n).1

    have hNearN :
        σ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T :=
      (hσ n).2.1

    have hTailN : σ n ∈ Set.Ioo c T :=
      ⟨hcn, hClassN.2⟩

    have hAnchorN : σ n ∈ Set.Ioo b T :=
      ⟨lt_trans hc.1 hcn, hClassN.2⟩

    have hRate :
        1 ≤
          3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
            (T - σ n) ^ 2 *
            velocityH3Energy3At u (σ n) :=
      one_le_three_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_energy3_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hb
        hAnchorN
        (hLate (σ n) hTailN)

    have hNPos : 0 < (n : ℝ) + 1 := by
      positivity

    have hDistanceUpper :
        T - σ n < 1 / ((n : ℝ) + 1) := by
      linarith [hNearN.1]

    have hScaledDistanceRaw :
        ((n : ℝ) + 1) * (T - σ n) <
          ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) :=
      mul_lt_mul_of_pos_left
        hDistanceUpper
        hNPos

    have hCancel :
        ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by
      rw [one_div]
      exact
        mul_inv_cancel₀
          (ne_of_gt hNPos)

    have hScaledDistance :
        ((n : ℝ) + 1) * (T - σ n) < 1 :=
      lt_of_lt_of_eq
        hScaledDistanceRaw
        hCancel

    have hScaledDistanceNonneg :
        0 ≤ ((n : ℝ) + 1) * (T - σ n) := by
      have hDistancePos : 0 < T - σ n := by
        linarith [hNearN.2]
      positivity

    have hScaledDistanceSq :
        (((n : ℝ) + 1) * (T - σ n)) ^ 2 ≤ 1 := by
      have hStrict :
          (((n : ℝ) + 1) * (T - σ n)) ^ 2 < (1 : ℝ) ^ 2 :=
        pow_lt_pow_left₀
          hScaledDistance
          hScaledDistanceNonneg
          (by norm_num)
      simpa using (le_of_lt hStrict)

    have hCoeffNonneg :
        0 ≤
          3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
            velocityH3Energy3At u (σ n) := by
      have hE3 : 0 ≤ velocityH3Energy3At u (σ n) :=
        velocityH3Energy3At_nonneg u (σ n)
      positivity

    have hRateScaled :=
      mul_le_mul_of_nonneg_left
        hRate
        (by positivity : 0 ≤ ((n : ℝ) + 1) ^ 2)

    have hContract :=
      mul_le_mul_of_nonneg_right
        hScaledDistanceSq
        hCoeffNonneg

    calc
      ((n : ℝ) + 1) ^ 2 =
          ((n : ℝ) + 1) ^ 2 * 1 := by
            ring
      _ ≤
          ((n : ℝ) + 1) ^ 2 *
            (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
              (T - σ n) ^ 2 *
              velocityH3Energy3At u (σ n)) :=
        hRateScaled
      _ =
          (((n : ℝ) + 1) * (T - σ n)) ^ 2 *
            (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
              velocityH3Energy3At u (σ n)) := by
        ring
      _ ≤
          1 *
            (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
              velocityH3Energy3At u (σ n)) :=
        hContract
      _ =
          3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
            velocityH3Energy3At u (σ n) := by
        ring

  exact ⟨σ, hσ, hSigmaTendsto, hIndexedE3⟩

end

end Euclidean
end Bridge
end PrimeTensor

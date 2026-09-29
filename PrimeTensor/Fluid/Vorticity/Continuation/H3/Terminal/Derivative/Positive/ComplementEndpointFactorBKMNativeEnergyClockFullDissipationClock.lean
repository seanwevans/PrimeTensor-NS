import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeEnergyClockTopOrderDissipationClock

/-!
# Full H³ dissipation clock on the physical-energy sequence

The synchronized physical-energy witness already carries

* `D₃(σ n) / E₃(σ n) -> +∞`, and
* `(T - σ n) * D₃(σ n) -> +∞`.

Since the full H³ dissipation dominates its third-order block pointwise,

`D₃(t) ≤ D(t)`,

the same terminal sequence immediately carries the corresponding full
frequency and physical-clock divergences:

* `D(σ n) / E₃(σ n) -> +∞`, and
* `(T - σ n) * D(σ n) -> +∞`.

No new extraction and no sign condition on the H³ energy derivative is used.
These remain necessary consequences conditional on hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The physical-energy-clock sequence with top-order frequency cascade also
carries full H³ dissipation divergence relative to `E₃` and in physical time. -/
theorem exists_h3EnergyPhysicalClock_with_fullDissipationClockSequence_of_noH3PathExtension
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
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          velocityH3Dissipation3At u (σ n) /
            velocityH3Energy3At u (σ n))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3Dissipation3At u (σ n))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          velocityH3DissipationAt u (σ n) /
            velocityH3Energy3At u (σ n))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3DissipationAt u (σ n))
        atTop atTop := by
  obtain
    ⟨
      σ,
      C,
      hCNonneg,
      hσ,
      hSigmaTendsto,
      hIndexedE3,
      hPhysicalE3Rate,
      hPhysicalE3Top,
      hD3RatioTop,
      hPhysicalD3Top
    ⟩ :=
    exists_h3EnergyPhysicalClock_with_topFrequencyDissipationClockSequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  have hFullRatioTop :
      Tendsto
        (fun n : ℕ =>
          velocityH3DissipationAt u (σ n) /
            velocityH3Energy3At u (σ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    have hD3Eventually :
        ∀ᶠ n : ℕ in atTop,
          M ≤
            velocityH3Dissipation3At u (σ n) /
              velocityH3Energy3At u (σ n) :=
      hD3RatioTop.eventually
        (eventually_ge_atTop M)

    filter_upwards [hD3Eventually] with n hn

    have hE3 :
        0 ≤ velocityH3Energy3At u (σ n) :=
      velocityH3Energy3At_nonneg
        u
        (σ n)

    have hTop :
        velocityH3Dissipation3At u (σ n) ≤
          velocityH3DissipationAt u (σ n) :=
      velocityH3Dissipation3At_le_dissipationAt
        u
        (σ n)

    have hRatio :
        velocityH3Dissipation3At u (σ n) /
            velocityH3Energy3At u (σ n) ≤
          velocityH3DissipationAt u (σ n) /
            velocityH3Energy3At u (σ n) :=
      div_le_div_of_nonneg_right
        hTop
        hE3

    exact
      le_trans
        hn
        hRatio

  have hPhysicalDTop :
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3DissipationAt u (σ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    have hD3ClockEventually :
        ∀ᶠ n : ℕ in atTop,
          M ≤
            (T - σ n) * velocityH3Dissipation3At u (σ n) :=
      hPhysicalD3Top.eventually
        (eventually_ge_atTop M)

    filter_upwards [hD3ClockEventually] with n hn

    have hGapNonneg :
        0 ≤ T - σ n := by
      linarith [(hσ n).1.2]

    have hTop :
        velocityH3Dissipation3At u (σ n) ≤
          velocityH3DissipationAt u (σ n) :=
      velocityH3Dissipation3At_le_dissipationAt
        u
        (σ n)

    have hScaled :
        (T - σ n) * velocityH3Dissipation3At u (σ n) ≤
          (T - σ n) * velocityH3DissipationAt u (σ n) :=
      mul_le_mul_of_nonneg_left
        hTop
        hGapNonneg

    exact
      le_trans
        hn
        hScaled

  exact
    ⟨
      σ,
      C,
      hCNonneg,
      hσ,
      hSigmaTendsto,
      hIndexedE3,
      hPhysicalE3Rate,
      hPhysicalE3Top,
      hD3RatioTop,
      hPhysicalD3Top,
      hFullRatioTop,
      hPhysicalDTop
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.TopFrequencyCascade

/-!
# Terminal characteristic top-order frequency cascade

The intrinsic cascade proved earlier gives, along one strict positive-derivative
terminal sequence,

    D₃(σ_n) / E₃(σ_n) -> +∞.

This ratio has the dimensions of a squared frequency.  Define the canonical
top-order characteristic frequency by

    Λ₃(t) = sqrt(D₃(t) / E₃(t)).

Because `D₃/E₃` is nonnegative, its square is identified exactly:

    Λ₃(t)^2 = D₃(t) / E₃(t).

The intrinsic cascade therefore implies

    Λ₃(σ_n) -> +∞.

Its reciprocal characteristic length scale

    ℓ₃(t) = Λ₃(t)⁻¹

simultaneously satisfies

    ℓ₃(σ_n) -> 0.

This packages the previously proved `D₃/E₃` divergence as an intrinsic
high-frequency / vanishing-length-scale statement.  It remains a necessary
consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
Canonical top-order characteristic frequency extracted from the ratio of top
H³ dissipation to top H³ energy.
-/
noncomputable def h3TopCharacteristicFrequencyAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    Real.sqrt
      (
        velocityH3Dissipation3At u t
          /
        velocityH3Energy3At u t
      )

/--
Reciprocal characteristic length associated with
`h3TopCharacteristicFrequencyAt`.
-/
noncomputable def h3TopCharacteristicLengthAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    (h3TopCharacteristicFrequencyAt u t)⁻¹

/--
The characteristic top-order frequency is nonnegative.
-/
theorem h3TopCharacteristicFrequencyAt_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3TopCharacteristicFrequencyAt u t := by

  unfold h3TopCharacteristicFrequencyAt

  exact
    Real.sqrt_nonneg _

/--
The squared characteristic frequency is exactly the intrinsic dissipation to
energy ratio.
-/
theorem h3TopCharacteristicFrequencyAt_sq
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    h3TopCharacteristicFrequencyAt u t ^ 2
      =
    velocityH3Dissipation3At u t
      /
    velocityH3Energy3At u t := by

  have hD3 :
      0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg
      u t

  have hE3 :
      0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg
      u t

  have hRatio :
      0
        ≤
      velocityH3Dissipation3At u t
        /
      velocityH3Energy3At u t :=
    div_nonneg
      hD3
      hE3

  unfold h3TopCharacteristicFrequencyAt

  exact
    Real.sq_sqrt
      hRatio

/-! ## Terminal frequency and length-scale cascade -/

/--
Hypothetical nonextension forces one strict positive-derivative terminal
sequence on which

    E₃ -> +∞,
    Λ₃ -> +∞,
    ℓ₃ -> 0.

The sequence is the same intrinsic top-frequency cascade sequence.
-/
theorem exists_terminal_characteristicFrequencyCascade_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ σ : ℕ → ℝ,
      (
        ∀ n : ℕ,
          σ n ∈ Set.Ioo a T
            ∧
          σ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          (n : ℝ)
            <
          deriv (velocityH3EnergyAt u) (σ n)
      )
        ∧
      Tendsto σ atTop (𝓝 T)
        ∧
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            h3TopCharacteristicFrequencyAt u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            h3TopCharacteristicLengthAt u (σ n)
        )
        atTop
        (𝓝 0) := by

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hE3Tendsto,
      hD3RatioTendsto,
      _hFullRatioTendsto,
      _hTransportRatioTendsto
    ⟩ :=
    exists_terminal_topFrequencyCascade_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hFrequencyTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TopCharacteristicFrequencyAt u (σ n)
        )
        atTop
        atTop := by

    unfold h3TopCharacteristicFrequencyAt

    exact
      Real.tendsto_sqrt_atTop.comp
        hD3RatioTendsto

  have hLengthTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TopCharacteristicLengthAt u (σ n)
        )
        atTop
        (𝓝 0) := by

    unfold h3TopCharacteristicLengthAt

    exact
      hFrequencyTendsto.inv_tendsto_atTop

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hE3Tendsto,
      hFrequencyTendsto,
      hLengthTendsto
    ⟩

/--
Equivalent frequency-only specialization: the characteristic top-order
frequency becomes arbitrarily large arbitrarily near the terminal time.
-/
theorem h3TopCharacteristicFrequencyAt_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
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
          t ∈ Set.Ioo a T
            ∧
          M < h3TopCharacteristicFrequencyAt u t := by

  intro ε hε M

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      _hE3Tendsto,
      hFrequencyTendsto,
      _hLengthTendsto
    ⟩ :=
    exists_terminal_characteristicFrequencyCascade_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hNear :
      ∀ᶠ n : ℕ in atTop,
        T - ε < σ n :=
    (tendsto_order.1 hSigmaTendsto).1
      (T - ε)
      (by linarith)

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        M < h3TopCharacteristicFrequencyAt u (σ n) :=
    hFrequencyTendsto.eventually
      (eventually_gt_atTop M)

  obtain
    ⟨n, hnNear, hnLarge⟩ :=
    (hNear.and hLarge).exists

  exact
    ⟨
      σ n,
      ⟨
        hnNear,
        (hσ n).1.2
      ⟩,
      (hσ n).1,
      hnLarge
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

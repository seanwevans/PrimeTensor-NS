import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.JointSequence

/-!
# Adverse H³ transport above the harmonic dissipation scale

The synchronized terminal cascade gives one strict preterminal sequence
`σ_n -> T` along which

    E'(σ_n) -> +∞,
    D₃(σ_n) -> +∞,
    D(σ_n) -> +∞,
    -T_H3(σ_n) -> +∞.

The eventual top-order dissipation estimate contains more quantitative
information:

    1 / (T-t) ≤ D₃(t) ≤ D(t)

on a sufficiently late terminal tail.

Insert this into the exact balance

    -T_H3(t) = E'(t) + 2 D(t).

Along the same derivative blowup sequence, once it enters the harmonic tail,

    E'(σ_n)
      ≤
    -T_H3(σ_n) - 2 / (T-σ_n).

Since the left-hand side tends to `+∞`, the adverse transport exceeds the
minimal harmonic viscous scale by a diverging amount:

    -T_H3(σ_n) - 2 / (T-σ_n) -> +∞.

Equivalently,

    T_H3(σ_n) + 2 / (T-σ_n) -> -∞.

This remains a necessary condition for hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
A hypothetical nonextendible H³ path admits a strict preterminal sequence on
which adverse transport exceeds the harmonic scale `2 / (T-t)` by a quantity
tending to `+∞`.

The same sequence retains the previously established joint cascade.
-/
theorem exists_terminal_adverseTransport_excess_over_harmonicScale_sequence_of_noH3PathExtension
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
      )
        ∧
      Tendsto σ atTop (𝓝 T)
        ∧
      Tendsto
        (
          fun n : ℕ =>
            deriv (velocityH3EnergyAt u) (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Dissipation3At u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            velocityH3DissipationAt u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            - velocityH3TransportDerivativeAt u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            - velocityH3TransportDerivativeAt u (σ n)
              - 2 / (T - σ n)
        )
        atTop
        atTop := by

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hDerivativeTendsto,
      hD3Tendsto,
      hFullDissipationTendsto,
      hTransportTendsto
    ⟩ :=
    exists_joint_terminal_h3_cascade_sequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  obtain
    ⟨c, hc, hHarmonic⟩ :=
    exists_terminalTail_one_div_terminalDistance_le_dissipation3_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  have hSigmaAboveC :
      ∀ᶠ n : ℕ in atTop,
        c < σ n :=
    (tendsto_order.1 hSigmaTendsto).1
      c
      hc.2

  have hExcessTendsto :
      Tendsto
        (
          fun n : ℕ =>
            - velocityH3TransportDerivativeAt u (σ n)
              - 2 / (T - σ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hDerivativeEventually :
        ∀ᶠ n : ℕ in atTop,
          M
            ≤
          deriv (velocityH3EnergyAt u) (σ n) :=
      hDerivativeTendsto.eventually
        (eventually_ge_atTop M)

    filter_upwards
      [
        hDerivativeEventually,
        hSigmaAboveC
      ]
      with n hn hcn

    have hσClass :
        σ n ∈ Set.Ioo a T :=
      hσ n

    have hσTail :
        σ n ∈ Set.Ioo c T :=
      ⟨
        hcn,
        hσClass.2
      ⟩

    have hHarmonicN :
        1 / (T - σ n)
          ≤
        velocityH3Dissipation3At u (σ n) :=
      hHarmonic
        (σ n)
        hσTail

    have hTop :
        velocityH3Dissipation3At u (σ n)
          ≤
        velocityH3DissipationAt u (σ n) :=
      velocityH3Dissipation3At_le_dissipationAt
        u
        (σ n)

    have hFull :
        1 / (T - σ n)
          ≤
        velocityH3DissipationAt u (σ n) :=
      le_trans
        hHarmonicN
        hTop

    have hBalance :=
      deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
        hH3
        hClass
        hσClass

    have hTwiceHarmonic :
        2 / (T - σ n)
          ≤
        2 * velocityH3DissipationAt u (σ n) := by

      have hScaled :=
        mul_le_mul_of_nonneg_left
          hFull
          (by norm_num : (0 : ℝ) ≤ 2)

      simpa only [div_eq_mul_inv, one_mul] using
        hScaled

    have hDerivativeBelowExcess :
        deriv (velocityH3EnergyAt u) (σ n)
          ≤
        - velocityH3TransportDerivativeAt u (σ n)
          - 2 / (T - σ n) := by

      linarith [hBalance, hTwiceHarmonic]

    exact
      le_trans
        hn
        hDerivativeBelowExcess

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hDerivativeTendsto,
      hD3Tendsto,
      hFullDissipationTendsto,
      hTransportTendsto,
      hExcessTendsto
    ⟩

/--
Equivalent signed form: after adding back the harmonic scale
`2 / (T-σ_n)`, the H³ transport derivative still tends to `-∞`.
-/
theorem exists_terminal_transport_plus_harmonicScale_tendsto_atBot_sequence_of_noH3PathExtension
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
      )
        ∧
      Tendsto σ atTop (𝓝 T)
        ∧
      Tendsto
        (
          fun n : ℕ =>
            velocityH3TransportDerivativeAt u (σ n)
              + 2 / (T - σ n)
        )
        atTop
        atBot := by

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      _hDerivativeTendsto,
      _hD3Tendsto,
      _hFullDissipationTendsto,
      _hTransportTendsto,
      hExcessTendsto
    ⟩ :=
    exists_terminal_adverseTransport_excess_over_harmonicScale_sequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hSignedTendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3TransportDerivativeAt u (σ n)
              + 2 / (T - σ n)
        )
        atTop
        atBot := by

    refine
      tendsto_atBot.2
        ?_

    intro M

    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          -M
            ≤
          - velocityH3TransportDerivativeAt u (σ n)
            - 2 / (T - σ n) :=
      hExcessTendsto.eventually
        (eventually_ge_atTop (-M))

    filter_upwards
      [hEventually]
      with n hn

    linarith

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hSignedTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

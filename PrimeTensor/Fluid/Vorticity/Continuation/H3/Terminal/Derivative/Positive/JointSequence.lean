import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.TransportSequence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.Integrability

/-!
# Joint terminal H³ derivative-dissipation-transport cascade

Several preceding results isolate distinct necessary terminal pathologies under
hypothetical failure of H³ continuation:

* the raw H³-energy derivative becomes arbitrarily large along a sequence
  approaching `T`;
* the top H³ dissipation satisfies an eventual harmonic lower bound
  `1 / (T-t) ≤ D₃(t)`;
* adverse H³ transport dominates the raw energy derivative.

These can be synchronized on one and the same strict preterminal sequence.

Start with the derivative blowup sequence `σ_n -> T`.  Since the harmonic
`D₃` bound holds on a fixed sufficiently late tail, `σ_n` eventually enters
that tail.  The explicit localization

    T - 1/(n+1) < σ_n < T

then gives

    n+1 < 1/(T-σ_n) ≤ D₃(σ_n).

Thus `D₃(σ_n) -> +∞`.  Since the full dissipation dominates its top block,

    D(σ_n) -> +∞.

Exact balance and nonnegativity of dissipation also give

    E'(σ_n) ≤ -T_H3(σ_n),

so adverse transport tends to `+∞` along the same sequence.

This is a joint necessary-condition theorem on a hypothetical nonextension
branch.  It does not assert that such a branch exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
A hypothetical nonextendible H³ path admits one strict preterminal sequence on
which all of the following tend to `+∞` simultaneously:

* raw H³-energy derivative;
* top H³ dissipation `D₃`;
* full H³ dissipation `D`;
* adverse H³ transport `-T_H3`.
-/
theorem exists_joint_terminal_h3_cascade_sequence_of_noH3PathExtension
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
        atTop := by

  obtain
    ⟨σ, hσ, hSigmaTendsto, hDerivativeTendsto⟩ :=
    exists_deriv_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
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

  have hD3Tendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Dissipation3At u (σ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    obtain
      ⟨N : ℕ, hN⟩ :=
      exists_nat_gt M

    filter_upwards
      [
        hSigmaAboveC,
        eventually_ge_atTop N
      ]
      with n hcn hn

    have hClassN :
        σ n ∈ Set.Ioo a T :=
      (hσ n).1

    have hNearN :
        σ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T :=
      (hσ n).2.1

    have hTailN :
        σ n ∈ Set.Ioo c T :=
      ⟨
        hcn,
        hClassN.2
      ⟩

    have hDenNat :
        0 < (n : ℝ) + 1 := by
      positivity

    have hDistancePos :
        0 < T - σ n := by
      linarith [hNearN.2]

    have hDistanceUpper :
        T - σ n
          <
        1 / ((n : ℝ) + 1) := by
      linarith [hNearN.1]

    have hScaledDistance :
        ((n : ℝ) + 1) * (T - σ n)
          <
        1 := by

      have hMul :
          ((n : ℝ) + 1) * (T - σ n)
            <
          ((n : ℝ) + 1)
            * (1 / ((n : ℝ) + 1)) :=
        mul_lt_mul_of_pos_left
          hDistanceUpper
          hDenNat

      have hCancel :
          ((n : ℝ) + 1)
            * (1 / ((n : ℝ) + 1))
            =
          1 := by

        rw [one_div]

        exact
          mul_inv_cancel₀
            (ne_of_gt hDenNat)

      exact
        lt_of_lt_of_eq
          hMul
          hCancel

    have hReciprocalLower :
        (n : ℝ) + 1
          <
        1 / (T - σ n) := by

      exact
        (lt_div_iff₀ hDistancePos).2
          hScaledDistance

    have hHarmonicN :
        1 / (T - σ n)
          ≤
        velocityH3Dissipation3At u (σ n) :=
      hHarmonic
        (σ n)
        hTailN

    have hMN :
        M < (n : ℝ) := by

      exact
        lt_of_lt_of_le
          hN
          (by exact_mod_cast hn)

    exact
      le_of_lt
        (
          lt_trans
            hMN
            (
              lt_trans
                (by linarith : (n : ℝ) < (n : ℝ) + 1)
                (
                  lt_of_lt_of_le
                    hReciprocalLower
                    hHarmonicN
                )
            )
        )

  have hFullDissipationTendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3DissipationAt u (σ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hD3Eventually :
        ∀ᶠ n : ℕ in atTop,
          M
            ≤
          velocityH3Dissipation3At u (σ n) :=
      hD3Tendsto.eventually
        (eventually_ge_atTop M)

    filter_upwards
      [hD3Eventually]
      with n hn

    have hTop :
        velocityH3Dissipation3At u (σ n)
          ≤
        velocityH3DissipationAt u (σ n) :=
      velocityH3Dissipation3At_le_dissipationAt
        u
        (σ n)

    exact
      le_trans
        hn
        hTop

  have hTransportTendsto :
      Tendsto
        (
          fun n : ℕ =>
            - velocityH3TransportDerivativeAt u (σ n)
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
      [hDerivativeEventually]
      with n hn

    have hDom :
        deriv (velocityH3EnergyAt u) (σ n)
          ≤
        - velocityH3TransportDerivativeAt
            u
            (σ n) :=
      deriv_velocityH3EnergyAt_le_neg_transport
        hH3
        hClass
        (hσ n).1

    exact
      le_trans
        hn
        hDom

  exact
    ⟨
      σ,
      (fun n => (hσ n).1),
      hSigmaTendsto,
      hDerivativeTendsto,
      hD3Tendsto,
      hFullDissipationTendsto,
      hTransportTendsto
    ⟩

/--
Equivalent signed-transport packaging: along a joint cascade sequence the H³
transport derivative itself tends to `-∞`, while the derivative and both
dissipation quantities tend to `+∞`.
-/
theorem exists_joint_terminal_h3_cascade_with_transport_atBot_sequence_of_noH3PathExtension
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
            velocityH3TransportDerivativeAt u (σ n)
        )
        atTop
        atBot := by

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hDerivativeTendsto,
      hD3Tendsto,
      hFullDissipationTendsto,
      hNegTransportTendsto
    ⟩ :=
    exists_joint_terminal_h3_cascade_sequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hTransportTendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3TransportDerivativeAt u (σ n)
        )
        atTop
        atBot := by

    refine
      tendsto_atBot.2
        ?_

    intro M

    have hNegEventually :
        ∀ᶠ n : ℕ in atTop,
          -M
            ≤
          - velocityH3TransportDerivativeAt u (σ n) :=
      hNegTransportTendsto.eventually
        (eventually_ge_atTop (-M))

    filter_upwards
      [hNegEventually]
      with n hn

    linarith

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hDerivativeTendsto,
      hD3Tendsto,
      hFullDissipationTendsto,
      hTransportTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

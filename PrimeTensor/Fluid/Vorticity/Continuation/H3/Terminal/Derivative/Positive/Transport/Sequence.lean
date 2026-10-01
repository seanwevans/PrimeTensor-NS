import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Sequence

/-!
# Terminal adverse-transport divergence sequence

The positive H³-energy derivative blowup sequence can be transferred directly
through the exact energy balance

    E'(t) + 2 D(t) = -T_H3(t).

Since the full H³ dissipation is nonnegative,

    E'(t) ≤ -T_H3(t).

Therefore every terminal time at which the raw H³-energy derivative is large
also has at least as large an adverse transport derivative.

Under hypothetical nonextension this gives two equivalent terminal sequence
statements:

    -T_H3(σ_n) -> +∞,

and

     T_H3(σ_n) -> -∞,

for a strict preterminal sequence `σ_n -> T`.

This is still a necessary condition on a hypothetical nonextendible path; it
does not assert existence of such a path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Exact balance domination -/

/--
On every strict H³ energy-class time, the adverse transport dominates the raw
H³-energy derivative.
-/
theorem deriv_velocityH3EnergyAt_le_neg_transport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t
      ≤
    - velocityH3TransportDerivativeAt u t := by

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3
      hClass
      ht

  have hD :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg
      u t

  linarith

/-! ## Arbitrarily large adverse transport arbitrarily near T -/

/--
Hypothetical nonextension forces arbitrarily large adverse H³ transport in
every left neighborhood of the terminal time.
-/
theorem neg_velocityH3TransportDerivativeAt_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
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
        ∃ s : ℝ,
          s ∈ Set.Ioo (T - ε) T
            ∧
          s ∈ Set.Ioo a T
            ∧
          M
            <
          - velocityH3TransportDerivativeAt u s := by

  intro ε hε M

  obtain
    ⟨s, hsNear, hsClass, hDerivativeLarge⟩ :=
    deriv_velocityH3EnergyAt_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      ε
      hε
      M

  have hDom :
      deriv (velocityH3EnergyAt u) s
        ≤
      - velocityH3TransportDerivativeAt u s :=
    deriv_velocityH3EnergyAt_le_neg_transport
      hH3
      hClass
      hsClass

  exact
    ⟨
      s,
      hsNear,
      hsClass,
      lt_of_lt_of_le
        hDerivativeLarge
        hDom
    ⟩

/-! ## Sequential divergence -/

/--
There is a strict preterminal sequence converging to `T` along which the
adverse H³ transport tends to `+∞`.
-/
theorem exists_neg_velocityH3TransportDerivativeAt_blowupSequence_of_noH3PathExtension
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
            - velocityH3TransportDerivativeAt
                u
                (σ n)
        )
        atTop
        atTop := by

  obtain
    ⟨σ, hσ, hSigmaTendsto, hDerivativeTendsto⟩ :=
    exists_deriv_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hTransportTendsto :
      Tendsto
        (
          fun n : ℕ =>
            - velocityH3TransportDerivativeAt
                u
                (σ n)
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
      hTransportTendsto
    ⟩

/--
Equivalently, along the same strict preterminal sequence the signed H³
transport derivative tends to `-∞`.
-/
theorem exists_velocityH3TransportDerivativeAt_tendsto_atBot_sequence_of_noH3PathExtension
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
            velocityH3TransportDerivativeAt
              u
              (σ n)
        )
        atTop
        atBot := by

  obtain
    ⟨σ, hσ, hSigmaTendsto, hNegTransportTendsto⟩ :=
    exists_neg_velocityH3TransportDerivativeAt_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hTransportTendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3TransportDerivativeAt
              u
              (σ n)
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
          - velocityH3TransportDerivativeAt
              u
              (σ n) :=
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
      hTransportTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

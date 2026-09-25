import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.FullEnergyDissipationContinuation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.TransportDichotomy

/-!
# Full-energy normalized terminal balance dichotomy

The full-energy normalized cascade proves that hypothetical nonextension forces

    D₃(t) / E(t) -> +∞    as t ↑ T.

The exact H³ balance already supplies, at every strict energy-class time, the
pointwise alternative

    E'(t) ≤ -D₃(t)

or

    D₃(t) ≤ -T_H3(t).

Since the full normalized H³ energy satisfies `E(t) ≥ 1`, division preserves
these inequalities.  Therefore, under hypothetical nonextension, for every
prescribed threshold `M`, every sufficiently late strict time satisfies

    M ≤ -E'(t) / E(t)

or

    M ≤ -T_H3(t) / E(t).

Thus the exact balance remains neutral even after the full frequency cascade
has been established: at each sufficiently late time, either relative H³
energy decay is arbitrarily strong, or adverse transport normalized by the
full H³ energy is arbitrarily strong.

The theorem does not select one mechanism globally or pointwise in advance.

A direct positive contrapositive is also recorded.  If there is one finite
threshold `M` such that arbitrarily late times occur where *both* normalized
quantities remain below `M`, then smooth continuation across `T` must exist.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Eventual normalized exact-balance alternative -/

/--
Under hypothetical nonextension, every finite threshold is eventually exceeded
by at least one of the two normalized exact-balance channels:

* negative relative H³ energy derivative;
* negative H³ transport derivative normalized by full H³ energy.
-/
theorem eventually_normalized_energyDecay_or_transport_ge_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (M : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      (
        M
          ≤
        (
          - deriv (velocityH3EnergyAt u) t
        )
          /
        velocityH3EnergyAt u t
      )
        ∨
      (
        M
          ≤
        (
          - velocityH3TransportDerivativeAt u t
        )
          /
        velocityH3EnergyAt u t
      ) := by

  have hRatio :=
    velocityH3Dissipation3At_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hLower :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M
          ≤
        velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t :=
    hRatio.eventually
      (eventually_ge_atTop M)

  have hClassTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT
      hClass.terminal_start.2

  filter_upwards
    [
      hLower,
      hClassTail
    ]
    with t hLowerT ht

  have hEnergyPos :
      0 < velocityH3EnergyAt u t := by

    have hOne :=
      one_le_velocityH3EnergyAt
        u t

    linarith

  have hEnergyNonneg :
      0 ≤ velocityH3EnergyAt u t :=
    le_of_lt hEnergyPos

  rcases
    deriv_energy_le_neg_dissipation3_or_dissipation3_le_neg_transport
      hH3
      hClass
      ht
    with hDecay | hTransport

  · left

    have hDom :
        velocityH3Dissipation3At u t
          ≤
        - deriv (velocityH3EnergyAt u) t := by
      linarith

    have hDiv :
        velocityH3Dissipation3At u t
            /
          velocityH3EnergyAt u t
          ≤
        (
          - deriv (velocityH3EnergyAt u) t
        )
            /
          velocityH3EnergyAt u t :=
      div_le_div_of_nonneg_right
        hDom
        hEnergyNonneg

    exact
      le_trans
        hLowerT
        hDiv

  · right

    have hDiv :
        velocityH3Dissipation3At u t
            /
          velocityH3EnergyAt u t
          ≤
        (
          - velocityH3TransportDerivativeAt u t
        )
            /
          velocityH3EnergyAt u t :=
      div_le_div_of_nonneg_right
        hTransport
        hEnergyNonneg

    exact
      le_trans
        hLowerT
        hDiv

/-! ## Explicit strict-tail form -/

/--
Strict-tail version of the normalized exact-balance alternative.

For every finite threshold `M`, hypothetical nonextension supplies a strict
terminal time `c` after which every time satisfies at least one normalized
lower bound.
-/
theorem exists_terminalTail_normalized_energyDecay_or_transport_ge_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (M : ℝ) :
    ∃ c : ℝ,
      c ∈ Set.Ioo a T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        (
          M
            ≤
          (
            - deriv (velocityH3EnergyAt u) t
          )
            /
          velocityH3EnergyAt u t
        )
          ∨
        (
          M
            ≤
          (
            - velocityH3TransportDerivativeAt u t
          )
            /
          velocityH3EnergyAt u t
        ) := by

  have hEventually :=
    eventually_normalized_energyDecay_or_transport_ge_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      M

  obtain
    ⟨d, hdT, hdSubset⟩ :=
    (
      mem_nhdsLT_iff_exists_Ioo_subset
    ).1
      hEventually

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  let c : ℝ :=
    max d b

  have hc :
      c ∈ Set.Ioo a T := by

    constructor

    · dsimp only [c]

      exact
        lt_of_lt_of_le
          hb.1
          (le_max_right _ _)

    · dsimp only [c]

      exact
        max_lt
          hdT
          hb.2

  refine
    ⟨
      c,
      hc,
      ?_
    ⟩

  intro t ht

  apply
    hdSubset

  constructor

  · exact
      lt_of_le_of_lt
        (le_max_left d b)
        ht.1

  · exact
      ht.2

/-! ## Neutral terminal dichotomy package -/

/--
Neutral full-energy normalized balance package.

Either smooth continuation exists, or every finite threshold is eventually
exceeded by at least one normalized exact-balance channel.
-/
theorem smoothContinuationExtension_or_eventually_normalized_energyDecay_or_transport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∀ M : ℝ,
        ∀ᶠ t : ℝ in 𝓝[<] T,
          (
            M
              ≤
            (
              - deriv (velocityH3EnergyAt u) t
            )
              /
            velocityH3EnergyAt u t
          )
            ∨
          (
            M
              ≤
            (
              - velocityH3TransportDerivativeAt u t
            )
              /
            velocityH3EnergyAt u t
          )
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · right

    intro M

    exact
      eventually_normalized_energyDecay_or_transport_ge_of_noH3PathExtension
        hH3
        hExtension
        hClass
        M

/-! ## Positive continuation contrapositive -/

/--
Suppose one finite threshold `M` is jointly respected by both normalized
balance channels at arbitrarily late times:

    -E'(t) / E(t) < M

and

    -T_H3(t) / E(t) < M.

Then the H³ path extends smoothly across `T`.
-/
theorem exists_smoothContinuationExtension_of_normalized_decay_and_transport_jointly_bounded_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hRecurring :
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          (
            - deriv (velocityH3EnergyAt u) t
          )
            /
          velocityH3EnergyAt u t
            <
          M
            ∧
          (
            - velocityH3TransportDerivativeAt u t
          )
            /
          velocityH3EnergyAt u t
            <
          M) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  obtain
    ⟨c, hc, hAlternative⟩ :=
    exists_terminalTail_normalized_energyDecay_or_transport_ge_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      M

  obtain
    ⟨t, ht, hDecayUpper, hTransportUpper⟩ :=
    hRecurring
      c
      hc

  rcases
    hAlternative
      t
      ht
    with hDecayLower | hTransportLower

  · exact
      (not_lt_of_ge hDecayLower)
        hDecayUpper

  · exact
      (not_lt_of_ge hTransportLower)
        hTransportUpper

end

end Euclidean
end Bridge
end PrimeTensor

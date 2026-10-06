import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.SecondQ.Escape.StateMass.Primitive.Classify
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Close the lower-temporal scalar amplitude branch

The fixed-channel scalar frontier has already been reduced to two possible
unresolved channel amplitudes:

* lower temporal;
* top dissipation.

For the lower-temporal Hilbert state

    X₁,j = d/dt(q û_j),

the strict PDE identity is

    X₁,j = -q² û_j - q F_j.

Hence lower-temporal amplitude escape freezes either

* the square norm of one fourth-radial velocity component, which is dominated
  by the canonical top-dissipation scalar; or
* the canonical second-q forcing mass.

The second-q forcing-mass branch was completely closed in the preceding
checkpoint.  Therefore lower-temporal scalar amplitude escape reduces to

    top dissipation
      ∨ H³ energy
      ∨ fixed nonzero extended higher radial.

Substituting this into the global fixed-channel amplitude frontier leaves
top dissipation as the only unresolved scalar channel.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2800000

/--
Strict-time lower-temporal Hilbert-state balance:

    X₁,j = -q² û_j - q F_j.
-/
theorem h3TerminalResolvedLowerTemporalHilbertState_eq_neg_fourthRadial_sub_forcingSecondQ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalResolvedLowerTemporalHilbertState
        hH3 hClass j t
      =
    -
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j t
      -
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
      hH3 hClass j t := by

  have hDerivative :=
    h3TerminalPhysicalLowerWeightedHilbertDerivativeAtEndpoint_closed
      hH3 hClass

  have hDeriv :=
    deriv_h3TerminalPhysicalLowerWeightedVelocityFourierL2Path_eq_lowerWeightedPDERHS
      hH3 hClass hDerivative ht j

  unfold h3TerminalResolvedLowerTemporalHilbertState

  rw [hDeriv]

  unfold h3TerminalPhysicalLowerWeightedPDERHSFourierL2At

  rw [
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
      hH3 hClass ht j,
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_eq
      hH3 hClass ht j
  ]

/-- Triangle inequality for the lower-temporal strict PDE balance. -/
theorem norm_h3TerminalResolvedLowerTemporalHilbertState_le_fourthRadial_add_forcingSecondQ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ‖h3TerminalResolvedLowerTemporalHilbertState
        hH3 hClass j t‖
      ≤
    ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j t‖
      +
    ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
        hH3 hClass j t‖ := by

  rw [
    h3TerminalResolvedLowerTemporalHilbertState_eq_neg_fourthRadial_sub_forcingSecondQ
      hH3 hClass ht j
  ]

  calc
    ‖-
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j t
        -
      h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
        hH3 hClass j t‖
        ≤
      ‖-
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j t‖
        +
      ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
          hH3 hClass j t‖ :=
      norm_sub_le _ _
    _ =
      ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j t‖
        +
      ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
          hH3 hClass j t‖ := by
      rw [norm_neg]

/--
Lower-temporal scalar amplitude escape freezes either the canonical
top-dissipation amplitude or the canonical second-q forcing mass.
-/
theorem lowerTemporal_amplitude_escape_topDissipation_or_forcingSecondQMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hAmplitudeTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelAmplitude
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
              (τ n)
        )
        atTop
        atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalResolvedPhysicalPDEChannelAmplitude
                hH3 hClass j
                H3TerminalResolvedPhysicalPDEChannel.topDissipation
                (τ (s n))
          )
          atTop
          atTop
    )
      ∨
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalPhysicalTopDissipationForcingSecondQMassPath
                hH3 hClass j (τ (s n))
          )
          atTop
          atTop
    ) := by

  classical

  let diffusion : ℕ → ℝ :=
    fun n =>
      ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j (τ n)‖

  let forcing : ℕ → ℝ :=
    fun n =>
      ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
          hH3 hClass j (τ n)‖

  have hMaxTop :
      Tendsto
        (
          fun n : ℕ =>
            max
              ((diffusion n) ^ 2)
              ((forcing n) ^ 2)
        )
        atTop
        atTop := by

    refine tendsto_atTop.2 ?_

    intro M

    let R : ℝ := max M 0

    have hMLeR :
        M ≤ R := by
      dsimp only [R]
      exact le_max_left M 0

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          4 * R
            <
          h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
            (τ n) :=
      hAmplitudeTop.eventually
        (eventually_gt_atTop (4 * R))

    filter_upwards [hLarge] with n hn

    have hTriangle :=
      norm_h3TerminalResolvedLowerTemporalHilbertState_le_fourthRadial_add_forcingSecondQ
        hH3 hClass (hτ n) j

    have hStateSq :
        h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
            (τ n)
          ≤
        (diffusion n + forcing n) ^ 2 := by

      rw [
        resolvedLowerTemporalChannelAmplitude_eq_norm_sq_hilbertState
      ]

      exact
        pow_le_pow_left₀
          (norm_nonneg _)
          (by
            simpa only [diffusion, forcing] using hTriangle)
          2

    have hSumSq :
        (diffusion n + forcing n) ^ 2
          ≤
        2 *
          (
            (diffusion n) ^ 2
              +
            (forcing n) ^ 2
          ) := by

      nlinarith
        [
          sq_nonneg
            (diffusion n - forcing n)
        ]

    have hDiffusionMax :
        (diffusion n) ^ 2
          ≤
        max
          ((diffusion n) ^ 2)
          ((forcing n) ^ 2) :=
      le_max_left _ _

    have hForcingMax :
        (forcing n) ^ 2
          ≤
        max
          ((diffusion n) ^ 2)
          ((forcing n) ^ 2) :=
      le_max_right _ _

    have hStateMax :
        h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
            (τ n)
          ≤
        4 *
          max
            ((diffusion n) ^ 2)
            ((forcing n) ^ 2) := by

      nlinarith

    have hRLt :
        R
          <
        max
          ((diffusion n) ^ 2)
          ((forcing n) ^ 2) := by

      nlinarith

    exact
      hMLeR.trans
        (le_of_lt hRLt)

  let channel : ℕ → Bool :=
    fun n =>
      decide
        (
          (forcing n) ^ 2
            ≤
          (diffusion n) ^ 2
        )

  let selected : ℕ → ℝ :=
    fun n =>
      if channel n = true then
        (diffusion n) ^ 2
      else
        (forcing n) ^ 2

  have hSelectedEqMax :
      ∀ n : ℕ,
        selected n
          =
        max
          ((diffusion n) ^ 2)
          ((forcing n) ^ 2) := by

    intro n

    by_cases h :
        (forcing n) ^ 2
          ≤
        (diffusion n) ^ 2

    · have hc :
          channel n = true := by
        simp [channel, h]

      simp [
        selected,
        hc,
        max_eq_left h
      ]

    · have hle :
          (diffusion n) ^ 2
            ≤
          (forcing n) ^ 2 :=
        le_of_lt
          (lt_of_not_ge h)

      have hc :
          channel n = false := by
        simp [channel, h]

      simp [
        selected,
        hc,
        max_eq_right hle
      ]

  have hSelectedTop :
      Tendsto selected atTop atTop := by

    have hEq :
        selected
          =
        (
          fun n : ℕ =>
            max
              ((diffusion n) ^ 2)
              ((forcing n) ^ 2)
        ) :=
      funext hSelectedEqMax

    rw [hEq]

    exact hMaxTop

  have hFrequentlySomeChannel :
      ∃ᶠ n : ℕ in atTop,
        ∃ q : Bool,
          channel n = q :=
    Frequently.of_forall
      (fun n =>
        ⟨channel n, rfl⟩)

  obtain
    ⟨q, hChannelFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySomeChannel

  obtain
    ⟨s, hMono, hChannel⟩ :=
    extraction_of_frequently_atTop
      hChannelFrequently

  have hs :
      ∀ n : ℕ,
        n ≤ s n := by
    intro n
    exact hMono.le_apply

  have hsTop :
      Tendsto s atTop atTop :=
    hMono.tendsto_atTop

  have hTauSub :
      Tendsto
        (fun n : ℕ => τ (s n))
        atTop
        (𝓝 T) :=
    hTauTendsto.comp
      hsTop

  have hSelectedSubTop :
      Tendsto
        (fun n : ℕ =>
          selected (s n))
        atTop
        atTop := by

    change
      Tendsto
        (selected ∘ s)
        atTop
        atTop

    exact
      hSelectedTop.comp
        hsTop

  cases q with

  | false =>

      right

      have hEq :
          (fun n : ℕ =>
            selected (s n))
            =
          (fun n : ℕ =>
            (forcing (s n)) ^ 2) := by

        funext n

        simp [
          selected,
          hChannel n
        ]

      have hForcingSub :
          Tendsto
            (fun n : ℕ =>
              (forcing (s n)) ^ 2)
            atTop
            atTop := by

        rw [← hEq]

        exact hSelectedSubTop

      have hMassEq :
          (fun n : ℕ =>
            h3TerminalPhysicalTopDissipationForcingSecondQMassPath
              hH3 hClass j (τ (s n)))
            =
          (fun n : ℕ =>
            (forcing (s n)) ^ 2) := by

        funext n

        rw [
          h3TerminalPhysicalTopDissipationForcingSecondQMassPath_eq_norm_sq_secondQFourierL2Path
            hH3 hClass (hτ (s n)) j
        ]

      refine
        ⟨
          s,
          hs,
          hsTop,
          hTauSub,
          ?_
        ⟩

      rw [hMassEq]

      exact hForcingSub

  | true =>

      left

      have hEq :
          (fun n : ℕ =>
            selected (s n))
            =
          (fun n : ℕ =>
            (diffusion (s n)) ^ 2) := by

        funext n

        simp [
          selected,
          hChannel n
        ]

      have hDiffusionSub :
          Tendsto
            (fun n : ℕ =>
              (diffusion (s n)) ^ 2)
            atTop
            atTop := by

        rw [← hEq]

        exact hSelectedSubTop

      have hTopSub :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalResolvedPhysicalPDEChannelAmplitude
                  hH3 hClass j
                  H3TerminalResolvedPhysicalPDEChannel.topDissipation
                  (τ (s n))
            )
            atTop
            atTop := by

        change
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalTopDissipation3Path
                  hClass (τ (s n))
            )
            atTop
            atTop

        refine tendsto_atTop.2 ?_

        intro M

        have hLarge :
            ∀ᶠ n : ℕ in atTop,
              M < (diffusion (s n)) ^ 2 :=
          hDiffusionSub.eventually
            (eventually_gt_atTop M)

        filter_upwards [hLarge] with n hn

        have hLeAt :=
          norm_sq_h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_le_velocityH3Dissipation3At
            hH3 hClass (hτ (s n)) j

        have hLePath :
            (
              ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j (τ (s n))‖ : ℝ
            ) ^ 2
              ≤
            h3TerminalPhysicalTopDissipation3Path
              hClass (τ (s n)) := by

          rw [
            h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
              hH3 hClass (hτ (s n)) j,
            h3TerminalPhysicalTopDissipation3Path_eq
              hClass (hτ (s n))
          ]

          exact hLeAt

        have hLe :
            (diffusion (s n)) ^ 2
              ≤
            h3TerminalPhysicalTopDissipation3Path
              hClass (τ (s n)) := by

          simpa only [diffusion] using hLePath

        exact
          (le_of_lt hn).trans
            hLe

      exact
        ⟨
          s,
          hs,
          hsTop,
          hTauSub,
          hTopSub
        ⟩

/--
Lower-temporal scalar amplitude escape is completely reduced to canonical top
dissipation, physical H³-energy escape, or one fixed nonzero extended
higher-radial moment.
-/
theorem lowerTemporal_amplitude_escape_topDissipation_or_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hAmplitudeTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelAmplitude
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
              (τ n)
        )
        atTop
        atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalResolvedPhysicalPDEChannelAmplitude
                hH3 hClass j
                H3TerminalResolvedPhysicalPDEChannel.topDissipation
                (τ (s n))
          )
          atTop
          atTop
    )
      ∨
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              velocityH3EnergyAt u (τ (s n))
          )
          atTop
          atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0
          ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n)
            ∧
          Tendsto s atTop atTop
            ∧
          Tendsto
            (fun n : ℕ => τ (s n))
            atTop
            (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalExtendedHigherRadialMomentAt
                  hH3 hClass m
                  (τ (s n))
                  (hτ (s n))
            )
            atTop
            (𝓝 ∞)
    ) := by

  rcases
    lowerTemporal_amplitude_escape_topDissipation_or_forcingSecondQMass
      hH3 hClass j τ hτ hTauTendsto hAmplitudeTop
  with
    hTop
    |
    hForcing

  · exact
      Or.inl hTop

  · rcases hForcing with
      ⟨s, hs, hsTop, hTauSub, hForcingTop⟩

    rcases
      h3TerminalForcingSecondQMassPath_escape_energy_or_fixedExtendedHigherRadial
        hH3
        hClass
        j
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hTauSub
        hForcingTop
    with
      hEnergy
      |
      hHigher

    · rcases hEnergy with
        ⟨v, hv, hvTop, hTauFinal, hEnergyTop⟩

      refine
        Or.inr
          (
            Or.inl
              ⟨
                (fun n : ℕ => s (v n)),
                ?_,
                hsTop.comp hvTop,
                hTauFinal,
                hEnergyTop
              ⟩
          )

      intro n

      exact
        le_trans
          (hv n)
          (hs (v n))

    · rcases hHigher with
        ⟨m, hm, v, hv, hvTop, hTauFinal, hHigherTop⟩

      refine
        Or.inr
          (
            Or.inr
              ⟨
                m,
                hm,
                (fun n : ℕ => s (v n)),
                ?_,
                hsTop.comp hvTop,
                hTauFinal,
                hHigherTop
              ⟩
          )

      intro n

      exact
        le_trans
          (hv n)
          (hs (v n))

/--
After closing the lower-temporal scalar amplitude, top dissipation is the only
remaining unresolved scalar channel under hypothetical nonextension.
-/
theorem exists_fixed_topDissipationAmplitude_or_energy_or_fixedExtendedHigherRadial_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T) :
    ∃ j₀ : Fin 3,
      ∃ τ : ℕ → ℝ,
        ∃ hτ :
          ∀ n : ℕ,
            τ n ∈ Set.Ioo a T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T,
          Tendsto τ atTop (𝓝 T)
            ∧
          (
            (
              ∃ s : ℕ → ℕ,
                (∀ n : ℕ, n ≤ s n)
                  ∧
                Tendsto s atTop atTop
                  ∧
                Tendsto
                  (fun n : ℕ => τ (s n))
                  atTop
                  (𝓝 T)
                  ∧
                Tendsto
                  (
                    fun n : ℕ =>
                      h3TerminalResolvedPhysicalPDEChannelAmplitude
                        hH3 hClass j₀
                        H3TerminalResolvedPhysicalPDEChannel.topDissipation
                        (τ (s n))
                  )
                  atTop
                  atTop
            )
              ∨
            (
              ∃ s : ℕ → ℕ,
                (∀ n : ℕ, n ≤ s n)
                  ∧
                Tendsto s atTop atTop
                  ∧
                Tendsto
                  (fun n : ℕ => τ (s n))
                  atTop
                  (𝓝 T)
                  ∧
                Tendsto
                  (
                    fun n : ℕ =>
                      velocityH3EnergyAt u (τ (s n))
                  )
                  atTop
                  atTop
            )
              ∨
            (
              ∃ m : ℕ,
                m ≠ 0
                  ∧
                ∃ s : ℕ → ℕ,
                  (∀ n : ℕ, n ≤ s n)
                    ∧
                  Tendsto s atTop atTop
                    ∧
                  Tendsto
                    (fun n : ℕ => τ (s n))
                    atTop
                    (𝓝 T)
                    ∧
                  Tendsto
                    (
                      fun n : ℕ =>
                        h3TerminalPhysicalExtendedHigherRadialMomentAt
                          hH3 hClass m
                          (τ (s n))
                          ((hτ (s n)).1)
                    )
                    atTop
                    (𝓝 ∞)
            )
          ) := by

  obtain
    ⟨j₀, channel, τ, hτ, hTauTendsto, hBranch⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_lowerTopAmplitude_or_energy_or_fixedExtendedHigherRadial_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  refine
    ⟨
      j₀,
      τ,
      hτ,
      hTauTendsto,
      ?_
    ⟩

  rcases hBranch with
    hAmplitude
    |
    hEnergy
    |
    hHigher

  · rcases hAmplitude with
      ⟨hChannel, k, hk, hkTop, hTauK, hAmplitudeTop⟩

    rcases hChannel with
      hLower
      |
      hTop

    · subst channel

      rcases
        lowerTemporal_amplitude_escape_topDissipation_or_energy_or_fixedExtendedHigherRadial
          hH3
          hClass
          j₀
          (fun n : ℕ => τ (k n))
          (fun n : ℕ => (hτ (k n)).1)
          hTauK
          hAmplitudeTop
      with
        hTopAmplitude
        |
        hEnergyLower
        |
        hHigherLower

      · rcases hTopAmplitude with
          ⟨s, hs, hsTop, hTauFinal, hTopAmplitudeTop⟩

        refine
          Or.inl
            ⟨
              (fun n : ℕ => k (s n)),
              ?_,
              hkTop.comp hsTop,
              hTauFinal,
              hTopAmplitudeTop
            ⟩

        intro n

        exact
          le_trans
            (hs n)
            (hk (s n))

      · rcases hEnergyLower with
          ⟨s, hs, hsTop, hTauFinal, hEnergyTop⟩

        refine
          Or.inr
            (
              Or.inl
                ⟨
                  (fun n : ℕ => k (s n)),
                  ?_,
                  hkTop.comp hsTop,
                  hTauFinal,
                  hEnergyTop
                ⟩
            )

        intro n

        exact
          le_trans
            (hs n)
            (hk (s n))

      · rcases hHigherLower with
          ⟨m, hm, s, hs, hsTop, hTauFinal, hHigherTop⟩

        refine
          Or.inr
            (
              Or.inr
                ⟨
                  m,
                  hm,
                  (fun n : ℕ => k (s n)),
                  ?_,
                  hkTop.comp hsTop,
                  hTauFinal,
                  hHigherTop
                ⟩
            )

        intro n

        exact
          le_trans
            (hs n)
            (hk (s n))

    · subst channel

      exact
        Or.inl
          ⟨
            k,
            hk,
            hkTop,
            hTauK,
            hAmplitudeTop
          ⟩

  · exact
      Or.inr
        (
          Or.inl hEnergy
        )

  · exact
      Or.inr
        (
          Or.inr hHigher
        )

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Balance
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Split fourth-temporal state-amplitude escape

The only unresolved lower-temporal branch is escape of the fourth-temporal
state amplitude

    ‖X₂,j(t)‖²,

where

    X₂,j = d/dt (q² û_j).

The exact strict-time PDE balance is

    X₂,j = -V₃,j - F₂,j,

with

    V₃,j = q³ û_j,
    F₂,j = q² F_j.

Hence

    ‖X₂,j‖²
      ≤ (‖V₃,j‖ + ‖F₂,j‖)²
      ≤ 4 max(‖V₃,j‖², ‖F₂,j‖²).

Therefore fourth-temporal amplitude escape freezes, on a cofinal subsequence,
either the sixth-diffusion state amplitude or the canonical fourth-q forcing
mass.  No branch is discarded.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1400000

/--
Strict-time state form of the fourth-radial PDE balance:

    X₂,j = -V₃,j - F₂,j.
-/
theorem h3TerminalResolvedFourthTemporalHilbertState_eq_neg_velocityThirdQ_sub_forcingFourthQ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalResolvedFourthTemporalHilbertState
        hH3 hClass j t
      =
    -
      h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
        hH3 hClass j t
      -
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
      hH3 hClass j t := by

  rw [
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_eq
      hH3 hClass ht j,
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_eq
      hH3 hClass ht j
  ]

  have hBalance :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_eq_neg_deriv_sub_velocityThirdQ
      hH3 hClass ht j

  unfold h3TerminalResolvedFourthTemporalHilbertState

  rw [hBalance]

  abel

/-- Triangle inequality for the fourth-temporal state PDE balance. -/
theorem norm_h3TerminalResolvedFourthTemporalHilbertState_le_velocityThirdQ_add_forcingFourthQ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ‖h3TerminalResolvedFourthTemporalHilbertState
        hH3 hClass j t‖
      ≤
    ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
        hH3 hClass j t‖
      +
    ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t‖ := by

  rw [
    h3TerminalResolvedFourthTemporalHilbertState_eq_neg_velocityThirdQ_sub_forcingFourthQ
      hH3 hClass ht j
  ]

  calc
    ‖-
        h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
          hH3 hClass j t
        -
      h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t‖
        ≤
      ‖-
        h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
          hH3 hClass j t‖
        +
      ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j t‖ :=
      norm_sub_le _ _
    _ =
      ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
          hH3 hClass j t‖
        +
      ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j t‖ := by
      rw [norm_neg]

/--
Fourth-temporal state-amplitude escape freezes one of its two strict PDE state
factors:

* the sixth-diffusion amplitude `‖q³ û_j‖²`, or
* the fourth-q forcing mass `‖q² F_j‖²`.
-/
theorem fourthTemporal_amplitude_escape_sixthDiffusionAmplitude_or_forcingFourthQMass
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
        (fun n : ℕ =>
          h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
            (τ n))
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelAmplitude
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
              (τ (s n)))
          atTop
          atTop
    )
      ∨
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalPhysicalTopDissipationForcingFourthQMassPath
              hH3 hClass j (τ (s n)))
          atTop
          atTop
    ) := by

  classical

  let diffusion : ℕ → ℝ :=
    fun n =>
      ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
          hH3 hClass j (τ n)‖

  let forcing : ℕ → ℝ :=
    fun n =>
      ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j (τ n)‖

  have hMaxTop :
      Tendsto
        (fun n : ℕ =>
          max
            ((diffusion n) ^ 2)
            ((forcing n) ^ 2))
        atTop
        atTop := by

    refine tendsto_atTop.2 ?_

    intro M

    let R : ℝ := max M 0

    have hMLER :
        M ≤ R := by
      dsimp only [R]
      exact le_max_left M 0

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          4 * R
            <
          h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
            (τ n) :=
      hAmplitudeTop.eventually
        (eventually_gt_atTop (4 * R))

    filter_upwards [hLarge] with n hn

    have hTriangle :=
      norm_h3TerminalResolvedFourthTemporalHilbertState_le_velocityThirdQ_add_forcingFourthQ
        hH3 hClass (hτ n) j

    have hStateSq :
        h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
            (τ n)
          ≤
        (diffusion n + forcing n) ^ 2 := by

      rw [
        resolvedFourthTemporalChannelAmplitude_eq_norm_sq_hilbertState
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
            H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
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
      hMLER.trans
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
        (fun n : ℕ =>
          max
            ((diffusion n) ^ 2)
            ((forcing n) ^ 2)) :=
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
            h3TerminalPhysicalTopDissipationForcingFourthQMassPath
              hH3 hClass j (τ (s n)))
            =
          (fun n : ℕ =>
            (forcing (s n)) ^ 2) := by

        funext n

        rw [
          h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq_norm_sq_fourthQFourierL2Path
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

      refine
        ⟨
          s,
          hs,
          hsTop,
          hTauSub,
          ?_
        ⟩

      simpa only [
        diffusion,
        resolvedSixthDiffusionChannelAmplitude_eq_norm_sq_hilbertState,
        h3TerminalResolvedSixthDiffusionHilbertState
      ] using hDiffusionSub

end

end Euclidean
end Bridge
end PrimeTensor

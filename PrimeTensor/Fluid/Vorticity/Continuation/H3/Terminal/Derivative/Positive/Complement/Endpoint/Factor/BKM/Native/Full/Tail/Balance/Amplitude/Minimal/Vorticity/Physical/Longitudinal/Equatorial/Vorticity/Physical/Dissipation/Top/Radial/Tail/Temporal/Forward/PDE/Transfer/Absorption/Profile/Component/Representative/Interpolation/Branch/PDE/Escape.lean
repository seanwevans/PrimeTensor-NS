import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Balance
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Resolve the fourth-order forcing branch into physical PDE channels

The adjacent-order branch has already been frozen.  Its fourth-order branch is

    ‖B_j(t_n)‖² -> +∞,

where

    B_j = q² F_j.

The exact physical PDE balance gives

    ‖B_j‖ ≤ ‖W_j‖ + ‖A_j‖,

with

    W_j = d/dt (q² û_j),
    A_j = q³ û_j.

Squaring and using

    (x + y)² ≤ 2(x² + y²)
              ≤ 4 max(x²,y²)

gives

    ‖B_j‖²
      ≤
    4 max(‖W_j‖², ‖A_j‖²).

Hence the maximum of the two physical PDE channels tends to `+∞`.  A finite
`Bool` extraction freezes one channel on a cofinal subsequence.

The full alternative therefore remains exhaustive:

* second square-gradient forcing mass escapes; or
* the fourth-radial temporal derivative norm-square escapes; or
* the sixth-radial diffusion norm-square escapes.

No branch is discarded.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailForcingPDEEscape
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1400000

/--
Under the retained endpoint hypotheses and hypothetical nonextension, one fixed
physical forcing coordinate admits a strict terminal sequence on which exactly
one of the following three alternatives survives:

1. lower neighboring forcing mass `M₂ -> +∞`;
2. fourth-radial temporal derivative norm-square `-> +∞`;
3. sixth-radial diffusion norm-square `-> +∞`.

The theorem is an exhaustive refinement of the frozen adjacent-order forcing
alternative.
-/
theorem exists_fixed_thirdRadialForcing_PDEChannel_blowupSubsequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
        (
          ∀ n : ℕ,
            τ n ∈ Set.Ioo a T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
        )
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        (
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalTopDissipationForcingSecondQMassPath
                  hH3 hClass j₀ (τ n)
            )
            atTop
            atTop
          ∨
          Tendsto
            (
              fun n : ℕ =>
                (
                  ‖deriv
                      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                        hH3 hClass j₀)
                      (τ n)‖ : ℝ
                ) ^ 2
            )
            atTop
            atTop
          ∨
          Tendsto
            (
              fun n : ℕ =>
                (
                  ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
                      hH3 hClass j₀ (τ n)‖ : ℝ
                ) ^ 2
            )
            atTop
            atTop
        ) := by

  obtain
    ⟨
      j₀,
      σ,
      hSigmaData,
      hSigmaTendsto,
      hBranch
    ⟩ :=
    exists_fixed_thirdRadialForcing_adjacentQOrder_or_fourthQPDEFactor_blowupSubsequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  rcases hBranch with hSecond | hFourth

  · exact
      ⟨
        j₀,
        σ,
        hSigmaData,
        hSigmaTendsto,
        Or.inl hSecond
      ⟩

  · let temporal : ℕ → ℝ :=
      fun n =>
        ‖deriv
            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass j₀)
            (σ n)‖

    let diffusion : ℕ → ℝ :=
      fun n =>
        ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
            hH3 hClass j₀ (σ n)‖

    have hMaxTop :
        Tendsto
          (
            fun n : ℕ =>
              max
                ((temporal n) ^ 2)
                ((diffusion n) ^ 2)
          )
          atTop
          atTop := by

      refine
        tendsto_atTop.2
          ?_

      intro M

      let R : ℝ :=
        max M 0

      have hBLarge :
          ∀ᶠ n : ℕ in atTop,
            4 * R
              <
            (
              ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
                  hH3 hClass j₀ (σ n)‖ : ℝ
            ) ^ 2 :=
        hFourth.eventually
          (
            eventually_gt_atTop
              (4 * R)
          )

      filter_upwards [hBLarge] with n hn

      have ht :
          σ n ∈ Set.Ioo a T :=
        (hSigmaData n).1

      have hTriangle :=
        norm_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_le_deriv_add_velocityThirdQPath
          hH3
          hClass
          ht
          j₀

      have hBsq :
          (
            ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
                hH3 hClass j₀ (σ n)‖ : ℝ
          ) ^ 2
            ≤
          (temporal n + diffusion n) ^ 2 := by

        exact
          pow_le_pow_left₀
            (norm_nonneg _)
            (by
              simpa only [temporal, diffusion] using hTriangle)
            2

      have hSumSq :
          (temporal n + diffusion n) ^ 2
            ≤
          2 *
            (
              (temporal n) ^ 2
                +
              (diffusion n) ^ 2
            ) := by

        nlinarith
          [
            sq_nonneg
              (temporal n - diffusion n)
          ]

      have hTemporalMax :
          (temporal n) ^ 2
            ≤
          max
            ((temporal n) ^ 2)
            ((diffusion n) ^ 2) :=
        le_max_left _ _

      have hDiffusionMax :
          (diffusion n) ^ 2
            ≤
          max
            ((temporal n) ^ 2)
            ((diffusion n) ^ 2) :=
        le_max_right _ _

      have hBMax :
          (
            ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
                hH3 hClass j₀ (σ n)‖ : ℝ
          ) ^ 2
            ≤
          4 *
            max
              ((temporal n) ^ 2)
              ((diffusion n) ^ 2) := by

        nlinarith

      have hRlt :
          R
            <
          max
            ((temporal n) ^ 2)
            ((diffusion n) ^ 2) := by

        nlinarith

      exact
        le_trans
          (le_max_left M 0)
          (le_of_lt hRlt)

    let channel : ℕ → Bool :=
      fun n =>
        decide
          (
            (diffusion n) ^ 2
              ≤
            (temporal n) ^ 2
          )

    let selected : ℕ → ℝ :=
      fun n =>
        if channel n = true then
          (temporal n) ^ 2
        else
          (diffusion n) ^ 2

    have hSelectedEqMax :
        ∀ n : ℕ,
          selected n
            =
          max
            ((temporal n) ^ 2)
            ((diffusion n) ^ 2) := by

      intro n

      by_cases h :
          (diffusion n) ^ 2
            ≤
          (temporal n) ^ 2

      · have hc :
            channel n = true := by
          simp [channel, h]

        simp [
          selected,
          hc,
          max_eq_left h
        ]

      · have hle :
            (temporal n) ^ 2
              ≤
            (diffusion n) ^ 2 :=
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
                ((temporal n) ^ 2)
                ((diffusion n) ^ 2)
          ) :=
        funext hSelectedEqMax

      rw [hEq]

      exact hMaxTop

    have hFrequentlySomeChannel :
        ∃ᶠ n : ℕ in atTop,
          ∃ q : Bool,
            channel n = q :=
      Frequently.of_forall
        (
          fun n =>
            ⟨
              channel n,
              rfl
            ⟩
        )

    obtain
      ⟨q, hChannelFrequently⟩ :=
      (Filter.frequently_exists).1
        hFrequentlySomeChannel

    obtain
      ⟨φ, hPhiMono, hChannel⟩ :=
      extraction_of_frequently_atTop
        hChannelFrequently

    have hPhiTendsto :
        Tendsto φ atTop atTop :=
      hPhiMono.tendsto_atTop

    let τ : ℕ → ℝ :=
      fun n =>
        σ (φ n)

    have hTauData :
        ∀ n : ℕ,
          τ n ∈ Set.Ioo a T
            ∧
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T := by

      intro n

      have hOld :=
        hSigmaData (φ n)

      have hIndexLeNat :
          n ≤ φ n :=
        hPhiMono.le_apply

      have hDenPos :
          0 < (n : ℝ) + 1 := by
        positivity

      have hDenLe :
          (n : ℝ) + 1
            ≤
          (φ n : ℝ) + 1 := by

        have hIndexLe :
            (n : ℝ) ≤ (φ n : ℝ) := by
          exact_mod_cast hIndexLeNat

        linarith

      have hInv :
          (1 : ℝ) / ((φ n : ℝ) + 1)
            ≤
          1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le
          hDenPos
          hDenLe

      have hNear :
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T := by

        constructor

        · dsimp only [τ]

          have hOldLower :=
            hOld.2.1

          linarith

        · dsimp only [τ]

          exact
            hOld.2.2

      exact
        ⟨
          by
            dsimp only [τ]
            exact hOld.1,
          hNear
        ⟩

    have hTauTendsto :
        Tendsto τ atTop (𝓝 T) := by

      dsimp only [τ]

      exact
        hSigmaTendsto.comp
          hPhiTendsto

    have hSelectedSubTop :
        Tendsto
          (
            fun n : ℕ =>
              selected (φ n)
          )
          atTop
          atTop := by

      change
        Tendsto
          (selected ∘ φ)
          atTop
          atTop

      exact
        hSelectedTop.comp
          hPhiTendsto

    have hResolved :
        Tendsto
          (
            fun n : ℕ =>
              (
                ‖deriv
                    (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                      hH3 hClass j₀)
                    (τ n)‖ : ℝ
              ) ^ 2
          )
          atTop
          atTop
        ∨
        Tendsto
          (
            fun n : ℕ =>
              (
                ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
                    hH3 hClass j₀ (τ n)‖ : ℝ
              ) ^ 2
          )
          atTop
          atTop := by

      cases q with

      | false =>

          right

          have hEq :
              (
                fun n : ℕ =>
                  selected (φ n)
              )
                =
              (
                fun n : ℕ =>
                  (diffusion (φ n)) ^ 2
              ) := by

            funext n

            simp [
              selected,
              hChannel n
            ]

          have hDiffusionSub :
              Tendsto
                (
                  fun n : ℕ =>
                    (diffusion (φ n)) ^ 2
                )
                atTop
                atTop := by

            rw [← hEq]

            exact hSelectedSubTop

          dsimp only [diffusion, τ] at hDiffusionSub ⊢

          exact hDiffusionSub

      | true =>

          left

          have hEq :
              (
                fun n : ℕ =>
                  selected (φ n)
              )
                =
              (
                fun n : ℕ =>
                  (temporal (φ n)) ^ 2
              ) := by

            funext n

            simp [
              selected,
              hChannel n
            ]

          have hTemporalSub :
              Tendsto
                (
                  fun n : ℕ =>
                    (temporal (φ n)) ^ 2
                )
                atTop
                atTop := by

            rw [← hEq]

            exact hSelectedSubTop

          dsimp only [temporal, τ] at hTemporalSub ⊢

          exact hTemporalSub

    refine
      ⟨
        j₀,
        τ,
        hTauData,
        hTauTendsto,
        ?_
      ⟩

    rcases hResolved with hTemporal | hDiffusion

    · exact
        Or.inr
          (Or.inl hTemporal)

    · exact
        Or.inr
          (Or.inr hDiffusion)

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Freeze the adjacent radial forcing branch

The previous checkpoint proves, for one fixed forcing coordinate,

    M₃(t) ≤ M₂(t) + M₄(t),

where `M₃` is the cubic square-gradient mass already known to diverge along a
strict terminal sequence.

Because the Euclidean raw third-radial mass and `M₃` differ only by the fixed
positive factor `(2π)^6`, the maximum of `M₂` and `M₄` also tends to `+∞`
along that sequence.

At every index choose whichever adjacent order is larger.  There are only two
orders, so the usual finite-channel extraction freezes one branch on a cofinal
subsequence.

Thus hypothetical nonextension forces, for one fixed physical forcing
coordinate, either

* second square-gradient forcing mass `M₂ -> +∞`, or
* fourth square-gradient forcing mass `M₄ -> +∞`.

The theorem does not discard the lower-order branch.  On the fourth-order
branch the divergent quantity is exactly the squared `L²` size of the `q² F_j`
forcing factor entering the already-closed fourth-radial PDE representative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailForcingAdjacentBranch
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Zero-extended neighboring mass paths -/

noncomputable def h3TerminalPhysicalTopDissipationForcingSecondQMassPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    ℝ :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationForcingSecondQMassAt
      hH3 hClass ht j
  else
    0

noncomputable def h3TerminalPhysicalTopDissipationForcingFourthQMassPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    ℝ :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationForcingFourthQMassAt
      hH3 hClass ht j
  else
    0

theorem h3TerminalPhysicalTopDissipationForcingSecondQMassPath_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingSecondQMassPath
        hH3 hClass j t
      =
    h3TerminalPhysicalTopDissipationForcingSecondQMassAt
      hH3 hClass ht j := by

  simp [
    h3TerminalPhysicalTopDissipationForcingSecondQMassPath,
    ht
  ]

theorem h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingFourthQMassPath
        hH3 hClass j t
      =
    h3TerminalPhysicalTopDissipationForcingFourthQMassAt
      hH3 hClass ht j := by

  simp [
    h3TerminalPhysicalTopDissipationForcingFourthQMassPath,
    ht
  ]

/-! ## Freeze the adjacent radial order -/

/--
Under the retained endpoint hypotheses and hypothetical nonextension, one fixed
physical forcing coordinate admits a strict terminal subsequence on which one
fixed adjacent radial mass diverges.

The alternative is exhaustive and neutral: the theorem does not choose between
the second- and fourth-order branches.
-/
theorem exists_fixed_thirdRadialForcing_adjacentQOrder_blowupSubsequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
                h3TerminalPhysicalTopDissipationForcingFourthQMassPath
                  hH3 hClass j₀ (τ n)
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
      hRawTop
    ⟩ :=
    exists_fixed_thirdRadialForcingRawFourierMass_blowupSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  let secondMass : ℕ → ℝ :=
    fun n =>
      h3TerminalPhysicalTopDissipationForcingSecondQMassPath
        hH3 hClass j₀ (σ n)

  let fourthMass : ℕ → ℝ :=
    fun n =>
      h3TerminalPhysicalTopDissipationForcingFourthQMassPath
        hH3 hClass j₀ (σ n)

  have hC :
      0 < (2 * Real.pi) ^ 6 := by
    positivity

  have hMaxTop :
      Tendsto
        (fun n : ℕ => max (secondMass n) (fourthMass n))
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hRawLarge :
        ∀ᶠ n : ℕ in atTop,
          (2 * M) / ((2 * Real.pi) ^ 6)
            <
          h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
            hH3 hClass j₀ (σ n) :=
      hRawTop.eventually
        (
          eventually_gt_atTop
            ((2 * M) / ((2 * Real.pi) ^ 6))
        )

    filter_upwards [hRawLarge] with n hn

    have ht :
        σ n ∈ Set.Ioo a T :=
      (hSigmaData n).1

    rw [
      h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq
        hH3 hClass ht j₀
    ] at hn

    have hScaled :
        2 * M
          <
        (2 * Real.pi) ^ 6
          *
        h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt
          hH3 hClass ht j₀ := by

      have h :=
        (div_lt_iff₀ hC).1
          hn

      simpa only [mul_comm] using h

    have hCubicLarge :
        2 * M
          <
        ∫ ξ : H3FourierPoint3,
          h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
            hH3 hClass ht j₀ ξ
          ∂(volume : Measure H3FourierPoint3) := by

      rw [
        integral_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt_eq_two_pi_six_mul_rawThirdRadialMass
          hH3 hClass ht j₀
      ]

      exact hScaled

    have hEither :=
      h3TerminalPhysicalTopDissipationForcingSecondQMassAt_or_fourthQMassAt_gt_of_two_mul_lt_cubic
        hH3
        hClass
        ht
        j₀
        hCubicLarge

    dsimp only [secondMass, fourthMass]

    rw [
      h3TerminalPhysicalTopDissipationForcingSecondQMassPath_eq
        hH3 hClass ht j₀,
      h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq
        hH3 hClass ht j₀
    ]

    rcases hEither with hSecond | hFourth

    · exact
        le_trans
          (le_of_lt hSecond)
          (le_max_left _ _)

    · exact
        le_trans
          (le_of_lt hFourth)
          (le_max_right _ _)

  let channel : ℕ → Bool :=
    fun n =>
      decide
        (fourthMass n ≤ secondMass n)

  let selected : ℕ → ℝ :=
    fun n =>
      if channel n = true then
        secondMass n
      else
        fourthMass n

  have hSelectedEqMax :
      ∀ n : ℕ,
        selected n
          =
        max (secondMass n) (fourthMass n) := by

    intro n

    by_cases h :
        fourthMass n ≤ secondMass n

    · have hc :
          channel n = true := by
        simp [channel, h]

      simp [
        selected,
        hc,
        max_eq_left h
      ]

    · have hle :
          secondMass n ≤ fourthMass n :=
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
          max (secondMass n) (fourthMass n)) :=
      funext hSelectedEqMax

    rw [hEq]

    exact hMaxTop

  have hFrequentlySomeChannel :
      ∃ᶠ n : ℕ in atTop,
        ∃ q : Bool,
          channel n = q :=
    Frequently.of_forall
      (fun n =>
        ⟨
          channel n,
          rfl
        ⟩)

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
          hOld.2.1.1

        linarith

      · dsimp only [τ]

        exact
          hOld.2.1.2

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
        (fun n : ℕ =>
          selected (φ n))
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

  have hFixedBranch :
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
            h3TerminalPhysicalTopDissipationForcingFourthQMassPath
              hH3 hClass j₀ (τ n)
        )
        atTop
        atTop := by

    cases q with

    | false =>

        right

        have hEq :
            (fun n : ℕ =>
              selected (φ n))
              =
            (fun n : ℕ =>
              fourthMass (φ n)) := by

          funext n

          simp [
            selected,
            hChannel n
          ]

        have hFourthSub :
            Tendsto
              (fun n : ℕ =>
                fourthMass (φ n))
              atTop
              atTop := by

          rw [← hEq]

          exact hSelectedSubTop

        dsimp only [fourthMass, τ] at hFourthSub ⊢

        exact hFourthSub

    | true =>

        left

        have hEq :
            (fun n : ℕ =>
              selected (φ n))
              =
            (fun n : ℕ =>
              secondMass (φ n)) := by

          funext n

          simp [
            selected,
            hChannel n
          ]

        have hSecondSub :
            Tendsto
              (fun n : ℕ =>
                secondMass (φ n))
              atTop
              atTop := by

          rw [← hEq]

          exact hSelectedSubTop

        dsimp only [secondMass, τ] at hSecondSub ⊢

        exact hSecondSub

  exact
    ⟨
      j₀,
      τ,
      hTauData,
      hTauTendsto,
      hFixedBranch
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

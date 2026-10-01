import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Energy.Clock.Balance.Channel.Subsequence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Full.Energy.Normalized.Cascade

/-!
# Fixed physical and normalized balance channel on the H³ clock witness

The preceding finite-channel extraction freezes one of the two exact-balance
channels on a cofinal physical-energy-clock subsequence.  The full-tail H³
cascade also gives

    D(t) / E(t) -> +∞.

At every selected time the exact balance identity is

    E'(t) + 2 D(t) = -T_H3(t).

Whichever of the two physical balance clocks is larger must therefore dominate
one copy of the full dissipation clock.  Because both balance channels are
normalized by the same positive energy, the same choice also dominates
`D(t) / E(t)`.

A finite extraction can thus freeze one channel which diverges simultaneously
in both senses:

* physical terminal clock;
* full-energy normalized rate.

The result remains neutral: it does not decide whether the frozen channel is
rapid energy decay or adverse transport.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Hypothetical nonextension supplies a cofinal physical-energy-clock
subsequence on which one fixed exact-balance channel diverges both in physical
clock units and after normalization by the full H³ energy. -/
theorem exists_h3EnergyPhysicalClock_fixedBalanceChannelPhysicalAndNormalizedSubsequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ,
        τ n ∈ Set.Ioo a T ∧
        τ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          (T - τ n) * velocityH3EnergyAt u (τ n)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3Energy3At u (τ n))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3Dissipation3At u (τ n))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3DissipationAt u (τ n))
        atTop atTop ∧
      (
        (
          Tendsto
            (fun n : ℕ =>
              (T - τ n) *
                (- deriv (velocityH3EnergyAt u) (τ n)))
            atTop atTop
          ∧
          Tendsto
            (fun n : ℕ =>
              (- deriv (velocityH3EnergyAt u) (τ n)) /
                velocityH3EnergyAt u (τ n))
            atTop atTop
        )
        ∨
        (
          Tendsto
            (fun n : ℕ =>
              (T - τ n) *
                (- velocityH3TransportDerivativeAt u (τ n)))
            atTop atTop
          ∧
          Tendsto
            (fun n : ℕ =>
              (- velocityH3TransportDerivativeAt u (τ n)) /
                velocityH3EnergyAt u (τ n))
            atTop atTop
        )
      ) := by
  obtain
    ⟨
      σ,
      _C,
      _hCNonneg,
      hσ,
      hSigmaTendsto,
      hPhysicalE3Top,
      hPhysicalD3Top,
      hPhysicalDTop,
      hBalanceClock
    ⟩ :=
    exists_h3EnergyPhysicalClock_with_balanceChannelPhysicalClockDichotomySequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  have hSigmaLT :
      Tendsto σ atTop (𝓝[<] T) := by
    refine tendsto_nhdsWithin_iff.mpr ?_
    constructor
    · exact hSigmaTendsto
    · exact
        Eventually.of_forall
          (fun n => (hσ n).1.2)

  have hFullRatioTop :
      Tendsto
        (fun n : ℕ =>
          velocityH3DissipationAt u (σ n) /
            velocityH3EnergyAt u (σ n))
        atTop atTop :=
    (
      velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3 hNoExtension hClass
    ).comp hSigmaLT

  let decayClock : ℕ → ℝ :=
    fun n =>
      (T - σ n) *
        (- deriv (velocityH3EnergyAt u) (σ n))

  let transportClock : ℕ → ℝ :=
    fun n =>
      (T - σ n) *
        (- velocityH3TransportDerivativeAt u (σ n))

  let decayNorm : ℕ → ℝ :=
    fun n =>
      (- deriv (velocityH3EnergyAt u) (σ n)) /
        velocityH3EnergyAt u (σ n)

  let transportNorm : ℕ → ℝ :=
    fun n =>
      (- velocityH3TransportDerivativeAt u (σ n)) /
        velocityH3EnergyAt u (σ n)

  have hMaxTop :
      Tendsto
        (fun n : ℕ => max (decayClock n) (transportClock n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    filter_upwards [hBalanceClock M] with n hn
    rcases hn with hDecay | hTransport
    · exact le_trans hDecay (le_max_left _ _)
    · exact le_trans hTransport (le_max_right _ _)

  let channel : ℕ → Bool :=
    fun n => decide (transportClock n ≤ decayClock n)

  let selected : ℕ → ℝ :=
    fun n =>
      if channel n = true then decayClock n else transportClock n

  let selectedNorm : ℕ → ℝ :=
    fun n =>
      if channel n = true then decayNorm n else transportNorm n

  have hSelectedEqMax :
      ∀ n : ℕ,
        selected n = max (decayClock n) (transportClock n) := by
    intro n
    by_cases h : transportClock n ≤ decayClock n
    · have hc : channel n = true := by
        simp [channel, h]
      simp [selected, hc, max_eq_left h]
    · have hle : decayClock n ≤ transportClock n :=
        le_of_lt (lt_of_not_ge h)
      have hc : channel n = false := by
        simp [channel, h]
      simp [selected, hc, max_eq_right hle]

  have hSelectedTop :
      Tendsto selected atTop atTop := by
    have hEq :
        selected =
          (fun n : ℕ => max (decayClock n) (transportClock n)) :=
      funext hSelectedEqMax
    rw [hEq]
    exact hMaxTop

  have hSelectedNormTop :
      Tendsto selectedNorm atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    have hRatioEventually :
        ∀ᶠ n : ℕ in atTop,
          M ≤
            velocityH3DissipationAt u (σ n) /
              velocityH3EnergyAt u (σ n) :=
      hFullRatioTop.eventually
        (eventually_ge_atTop M)

    filter_upwards [hRatioEventually] with n hRatioN

    have hClassN : σ n ∈ Set.Ioo a T :=
      (hσ n).1

    have hGapPos : 0 < T - σ n := by
      linarith [hClassN.2]

    have hEnergyPos : 0 < velocityH3EnergyAt u (σ n) := by
      have hOne := one_le_velocityH3EnergyAt u (σ n)
      linarith

    have hBalance :=
      deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
        hH3 hClass hClassN

    by_cases h : transportClock n ≤ decayClock n
    · have hc : channel n = true := by
        simp [channel, h]

      have hRawOrder :
          - velocityH3TransportDerivativeAt u (σ n) ≤
            - deriv (velocityH3EnergyAt u) (σ n) := by
        have hScaled :
            (T - σ n) *
                (- velocityH3TransportDerivativeAt u (σ n)) ≤
              (T - σ n) *
                (- deriv (velocityH3EnergyAt u) (σ n)) := by
          simpa only [transportClock, decayClock] using h
        by_contra hNot
        have hStrict :
            - deriv (velocityH3EnergyAt u) (σ n) <
              - velocityH3TransportDerivativeAt u (σ n) :=
          lt_of_not_ge hNot
        have hScaledStrict :=
          mul_lt_mul_of_pos_left hStrict hGapPos
        exact (not_lt_of_ge hScaled) hScaledStrict

      have hDLeDecay :
          velocityH3DissipationAt u (σ n) ≤
            - deriv (velocityH3EnergyAt u) (σ n) := by
        linarith

      have hNormDom :
          velocityH3DissipationAt u (σ n) /
              velocityH3EnergyAt u (σ n) ≤
            (- deriv (velocityH3EnergyAt u) (σ n)) /
              velocityH3EnergyAt u (σ n) :=
        div_le_div_of_nonneg_right
          hDLeDecay
          (le_of_lt hEnergyPos)

      have hLower := le_trans hRatioN hNormDom

      simpa [selectedNorm, hc, decayNorm] using hLower

    · have hle : decayClock n ≤ transportClock n :=
        le_of_lt (lt_of_not_ge h)

      have hc : channel n = false := by
        simp [channel, h]

      have hRawOrder :
          - deriv (velocityH3EnergyAt u) (σ n) ≤
            - velocityH3TransportDerivativeAt u (σ n) := by
        have hScaled :
            (T - σ n) *
                (- deriv (velocityH3EnergyAt u) (σ n)) ≤
              (T - σ n) *
                (- velocityH3TransportDerivativeAt u (σ n)) := by
          simpa only [decayClock, transportClock] using hle
        by_contra hNot
        have hStrict :
            - velocityH3TransportDerivativeAt u (σ n) <
              - deriv (velocityH3EnergyAt u) (σ n) :=
          lt_of_not_ge hNot
        have hScaledStrict :=
          mul_lt_mul_of_pos_left hStrict hGapPos
        exact (not_lt_of_ge hScaled) hScaledStrict

      have hDLeTransport :
          velocityH3DissipationAt u (σ n) ≤
            - velocityH3TransportDerivativeAt u (σ n) := by
        linarith

      have hNormDom :
          velocityH3DissipationAt u (σ n) /
              velocityH3EnergyAt u (σ n) ≤
            (- velocityH3TransportDerivativeAt u (σ n)) /
              velocityH3EnergyAt u (σ n) :=
        div_le_div_of_nonneg_right
          hDLeTransport
          (le_of_lt hEnergyPos)

      have hLower := le_trans hRatioN hNormDom

      simpa [selectedNorm, hc, transportNorm] using hLower

  have hFrequentlySomeChannel :
      ∃ᶠ n : ℕ in atTop,
        ∃ q : Bool, channel n = q :=
    Frequently.of_forall
      (fun n => ⟨channel n, rfl⟩)

  obtain ⟨q, hChannelFrequently⟩ :=
    (Filter.frequently_exists).1 hFrequentlySomeChannel

  obtain ⟨φ, hPhiMono, hChannel⟩ :=
    extraction_of_frequently_atTop hChannelFrequently

  have hPhiTendsto :
      Tendsto φ atTop atTop :=
    hPhiMono.tendsto_atTop

  let τ : ℕ → ℝ :=
    fun n => σ (φ n)

  have hTauData :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T ∧
        τ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          (T - τ n) * velocityH3EnergyAt u (τ n) := by
    intro n
    have hOld := hσ (φ n)

    have hIndexLeNat : n ≤ φ n :=
      hPhiMono.le_apply

    have hIndexLe : (n : ℝ) ≤ (φ n : ℝ) := by
      exact_mod_cast hIndexLeNat

    have hDenPos : 0 < (n : ℝ) + 1 := by
      positivity

    have hDenLe :
        (n : ℝ) + 1 ≤ (φ n : ℝ) + 1 := by
      linarith

    have hInv :
        (1 : ℝ) / ((φ n : ℝ) + 1) ≤
          1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le
        hDenPos
        hDenLe

    have hNear :
        τ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T := by
      constructor
      · dsimp only [τ]
        have hOldLower := hOld.2.1.1
        linarith
      · dsimp only [τ]
        exact hOld.2.1.2

    have hClock :
        (n : ℝ) <
          (T - τ n) * velocityH3EnergyAt u (τ n) := by
      dsimp only [τ]
      exact
        lt_of_le_of_lt
          hIndexLe
          hOld.2.2.1

    exact
      ⟨
        by
          dsimp only [τ]
          exact hOld.1,
        hNear,
        hClock
      ⟩

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) := by
    dsimp only [τ]
    exact hSigmaTendsto.comp hPhiTendsto

  have hE3ClockSub :
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3Energy3At u (τ n))
        atTop atTop := by
    dsimp only [τ]
    change
      Tendsto
        ((fun n : ℕ =>
          (T - σ n) * velocityH3Energy3At u (σ n)) ∘ φ)
        atTop atTop
    exact hPhysicalE3Top.comp hPhiTendsto

  have hD3ClockSub :
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3Dissipation3At u (τ n))
        atTop atTop := by
    dsimp only [τ]
    change
      Tendsto
        ((fun n : ℕ =>
          (T - σ n) * velocityH3Dissipation3At u (σ n)) ∘ φ)
        atTop atTop
    exact hPhysicalD3Top.comp hPhiTendsto

  have hDClockSub :
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3DissipationAt u (τ n))
        atTop atTop := by
    dsimp only [τ]
    change
      Tendsto
        ((fun n : ℕ =>
          (T - σ n) * velocityH3DissipationAt u (σ n)) ∘ φ)
        atTop atTop
    exact hPhysicalDTop.comp hPhiTendsto

  have hSelectedSubTop :
      Tendsto
        (fun n : ℕ => selected (φ n))
        atTop atTop := by
    change Tendsto (selected ∘ φ) atTop atTop
    exact hSelectedTop.comp hPhiTendsto

  have hSelectedNormSubTop :
      Tendsto
        (fun n : ℕ => selectedNorm (φ n))
        atTop atTop := by
    change Tendsto (selectedNorm ∘ φ) atTop atTop
    exact hSelectedNormTop.comp hPhiTendsto

  have hFixedChannel :
      (
        Tendsto
          (fun n : ℕ =>
            (T - τ n) *
              (- deriv (velocityH3EnergyAt u) (τ n)))
          atTop atTop
        ∧
        Tendsto
          (fun n : ℕ =>
            (- deriv (velocityH3EnergyAt u) (τ n)) /
              velocityH3EnergyAt u (τ n))
          atTop atTop
      )
      ∨
      (
        Tendsto
          (fun n : ℕ =>
            (T - τ n) *
              (- velocityH3TransportDerivativeAt u (τ n)))
          atTop atTop
        ∧
        Tendsto
          (fun n : ℕ =>
            (- velocityH3TransportDerivativeAt u (τ n)) /
              velocityH3EnergyAt u (τ n))
          atTop atTop
      ) := by
    cases q with
    | false =>
        right

        have hPhysicalEq :
            (fun n : ℕ => selected (φ n)) =
              (fun n : ℕ => transportClock (φ n)) := by
          funext n
          simp [selected, hChannel n]

        have hNormEq :
            (fun n : ℕ => selectedNorm (φ n)) =
              (fun n : ℕ => transportNorm (φ n)) := by
          funext n
          simp [selectedNorm, hChannel n]

        have hPhysical :
            Tendsto
              (fun n : ℕ => transportClock (φ n))
              atTop atTop := by
          rw [← hPhysicalEq]
          exact hSelectedSubTop

        have hNorm :
            Tendsto
              (fun n : ℕ => transportNorm (φ n))
              atTop atTop := by
          rw [← hNormEq]
          exact hSelectedNormSubTop

        constructor
        · dsimp only [transportClock, τ] at hPhysical ⊢
          exact hPhysical
        · dsimp only [transportNorm, τ] at hNorm ⊢
          exact hNorm

    | true =>
        left

        have hPhysicalEq :
            (fun n : ℕ => selected (φ n)) =
              (fun n : ℕ => decayClock (φ n)) := by
          funext n
          simp [selected, hChannel n]

        have hNormEq :
            (fun n : ℕ => selectedNorm (φ n)) =
              (fun n : ℕ => decayNorm (φ n)) := by
          funext n
          simp [selectedNorm, hChannel n]

        have hPhysical :
            Tendsto
              (fun n : ℕ => decayClock (φ n))
              atTop atTop := by
          rw [← hPhysicalEq]
          exact hSelectedSubTop

        have hNorm :
            Tendsto
              (fun n : ℕ => decayNorm (φ n))
              atTop atTop := by
          rw [← hNormEq]
          exact hSelectedNormSubTop

        constructor
        · dsimp only [decayClock, τ] at hPhysical ⊢
          exact hPhysical
        · dsimp only [decayNorm, τ] at hNorm ⊢
          exact hNorm

  exact
    ⟨
      τ,
      hTauData,
      hTauTendsto,
      hE3ClockSub,
      hD3ClockSub,
      hDClockSub,
      hFixedChannel
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

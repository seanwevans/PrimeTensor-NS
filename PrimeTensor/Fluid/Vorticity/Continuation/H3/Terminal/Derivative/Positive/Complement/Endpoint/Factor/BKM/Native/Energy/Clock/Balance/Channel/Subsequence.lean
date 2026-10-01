import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Energy.Clock.Balance.Channel.Dichotomy
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Fixed divergent balance channel on the physical-energy-clock witness

The preceding physical-clock theorem gives one terminal sequence `σ n -> T`
for which the top and full dissipation clocks diverge, while exact balance says
that every sufficiently large threshold is paid by at least one of

* `(T - σ n) * (-E'(σ n))`, or
* `(T - σ n) * (-T_H3(σ n))`.

Thus the maximum of these two balance clocks tends to `+∞`.  At each index we
select a channel attaining that maximum.  Since there are only two channels,
one occurs frequently; a strictly increasing extraction freezes that channel.
All terminal localization and physical energy/dissipation clock limits survive
composition with the cofinal extraction.

Consequently hypothetical nonextension forces a cofinal subsequence on which
one fixed physical balance mechanism diverges: either rapid H³ energy decay or
adverse H³ transport.  The theorem does not decide which alternative occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A cofinal subsequence of the synchronized physical-energy-clock witness has
one fixed balance channel whose physical terminal clock tends to `+∞`. -/
theorem exists_h3EnergyPhysicalClock_fixedBalanceChannelSubsequence_of_noH3PathExtension
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
        Tendsto
          (fun n : ℕ =>
            (T - τ n) *
              (- deriv (velocityH3EnergyAt u) (τ n)))
          atTop atTop
        ∨
        Tendsto
          (fun n : ℕ =>
            (T - τ n) *
              (- velocityH3TransportDerivativeAt u (τ n)))
          atTop atTop
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

  let decayClock : ℕ → ℝ :=
    fun n =>
      (T - σ n) *
        (- deriv (velocityH3EnergyAt u) (σ n))

  let transportClock : ℕ → ℝ :=
    fun n =>
      (T - σ n) *
        (- velocityH3TransportDerivativeAt u (σ n))

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

  have hSelectedEqMax :
      ∀ n : ℕ,
        selected n = max (decayClock n) (transportClock n) := by
    intro n
    by_cases h : transportClock n ≤ decayClock n
    · have hc : channel n = true := by
        simp [channel, h]
      simp [selected, hc, max_eq_left h]
    · have hle : decayClock n ≤ transportClock n := by
        exact le_of_lt (lt_of_not_ge h)
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

  have hFixedChannel :
      Tendsto
          (fun n : ℕ =>
            (T - τ n) *
              (- deriv (velocityH3EnergyAt u) (τ n)))
          atTop atTop
        ∨
      Tendsto
          (fun n : ℕ =>
            (T - τ n) *
              (- velocityH3TransportDerivativeAt u (τ n)))
          atTop atTop := by
    cases q with
    | false =>
        right
        have hEq :
            (fun n : ℕ => selected (φ n)) =
              (fun n : ℕ => transportClock (φ n)) := by
          funext n
          simp [selected, hChannel n]
        have hTransportSub :
            Tendsto
              (fun n : ℕ => transportClock (φ n))
              atTop atTop := by
          rw [← hEq]
          exact hSelectedSubTop
        dsimp only [transportClock, τ] at hTransportSub ⊢
        exact hTransportSub
    | true =>
        left
        have hEq :
            (fun n : ℕ => selected (φ n)) =
              (fun n : ℕ => decayClock (φ n)) := by
          funext n
          simp [selected, hChannel n]
        have hDecaySub :
            Tendsto
              (fun n : ℕ => decayClock (φ n))
              atTop atTop := by
          rw [← hEq]
          exact hSelectedSubTop
        dsimp only [decayClock, τ] at hDecaySub ⊢
        exact hDecaySub

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

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Fixed.Balance.Channel.Polynomial.Frequency

/-!
# Explicit terminal sequence for a fixed polynomial balance channel

The preceding theorem proves that, under hypothetical nonextension, one of the
following fixed mechanisms occurs frequently in the physical left-neighborhood
filter `𝓝[<] T`:

* rapid H³ energy decay, or
* adverse H³ transport.

Whichever mechanism is cofinal carries all three established polynomial rates:
raw inverse-`8/3`, physical-clock inverse-`5/3`, and full-energy normalized
inverse-`2/3`.

This file extracts that filter-level statement into an explicit physical-time
sequence.  The sequence is chosen directly inside

`(T - 1/(n+1), T)`,

so convergence to `T` is built into the witness and no reindex-dependent rate
is introduced.  The same fixed mechanism carries all three polynomial rates at
every selected time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Local extraction utilities -/

private theorem exists_point_of_frequently_and_mem
    {α : Type*}
    {l : Filter α}
    {P : α → Prop}
    {s : Set α}
    (hP : ∃ᶠ x : α in l, P x)
    (hs : s ∈ l) :
    ∃ x : α, x ∈ s ∧ P x := by
  classical
  by_contra hNo
  have hEventuallyNotP :
      ∀ᶠ x : α in l, ¬ P x := by
    filter_upwards [hs] with x hx
    intro hPx
    apply hNo
    exact ⟨x, hx, hPx⟩
  exact ((not_frequently).2 hEventuallyNotP) hP

private theorem tendsto_terminal_of_one_div_natSucc_localization_fixedChannel
    {T : ℝ}
    {τ : ℕ → ℝ}
    (hτ :
      ∀ n : ℕ,
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T) :
    Tendsto τ atTop (𝓝 T) := by
  rw [Metric.tendsto_atTop]
  intro ε hε

  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_gt (1 / ε)

  refine ⟨N, ?_⟩
  intro n hn

  have hCast :
      (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hDenN :
      0 < (N : ℝ) + 1 := by
    positivity

  have hInvN :
      (1 : ℝ) / ((n : ℝ) + 1)
        ≤
      1 / ((N : ℝ) + 1) := by
    exact
      one_div_le_one_div_of_le
        hDenN
        (by linarith)

  have hSmallN :
      1 / ((N : ℝ) + 1) < ε := by
    have hεPos : 0 < ε := hε
    have hInvEps : 1 / ε < (N : ℝ) := hN
    have hNPlus : 1 / ε < (N : ℝ) + 1 := by
      linarith
    have hMulRaw : 1 < ((N : ℝ) + 1) * ε :=
      (div_lt_iff₀ hεPos).1 hNPlus
    have hMul : 1 < ε * ((N : ℝ) + 1) := by
      simpa only [mul_comm] using hMulRaw
    exact
      (div_lt_iff₀ hDenN).2
        (by simpa only [one_mul] using hMul)

  have hSmall :
      (1 : ℝ) / ((n : ℝ) + 1) < ε :=
    lt_of_le_of_lt hInvN hSmallN

  have hLower := (hτ n).1
  have hUpper := (hτ n).2

  rw [Real.dist_eq]

  have hDiffNonpos :
      τ n - T ≤ 0 := by
    linarith [hUpper]

  rw [abs_of_nonpos hDiffNonpos]
  linarith

private theorem exists_terminalSequence_of_frequently_fixedChannel
    {T b : ℝ}
    {P : ℝ → Prop}
    (hbT : b < T)
    (hP : ∃ᶠ t : ℝ in 𝓝[<] T, P t) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ,
        τ n ∈ Set.Ioo b T
          ∧
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T
          ∧
        P (τ n))
        ∧
      Tendsto τ atTop (𝓝 T) := by
  classical

  have hChoice :
      ∀ n : ℕ,
        ∃ t : ℝ,
          t ∈ Set.Ioo b T
            ∧
          t ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          P t := by
    intro n

    let ε : ℝ :=
      (1 : ℝ) / ((n : ℝ) + 1)

    have hε : 0 < ε := by
      dsimp only [ε]
      positivity

    let l : ℝ :=
      max b (T - ε)

    have hlT : l < T := by
      dsimp only [l]
      exact max_lt hbT (by linarith)

    have hNeighborhood :
        Set.Ioo l T ∈ 𝓝[<] T :=
      Ioo_mem_nhdsLT hlT

    obtain ⟨t, ht, hPt⟩ :=
      exists_point_of_frequently_and_mem
        hP
        hNeighborhood

    have htAnchor : t ∈ Set.Ioo b T := by
      constructor
      · exact
          lt_of_le_of_lt
            (le_max_left b (T - ε))
            ht.1
      · exact ht.2

    have htNear :
        t ∈ Set.Ioo (T - ε) T := by
      constructor
      · exact
          lt_of_le_of_lt
            (le_max_right b (T - ε))
            ht.1
      · exact ht.2

    exact
      ⟨
        t,
        htAnchor,
        by simpa only [ε] using htNear,
        hPt
      ⟩

  choose τ hτ using hChoice

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) :=
    tendsto_terminal_of_one_div_natSucc_localization_fixedChannel
      (fun n => (hτ n).2.1)

  exact ⟨τ, hτ, hTauTendsto⟩

/-! ## Fixed polynomial balance-channel sequence -/

/-- Under hypothetical nonextension, one fixed balance mechanism admits an
explicit sequence of physical times converging to `T`.  At every selected time
that same mechanism carries all three polynomial terminal rates. -/
theorem exists_fixedBalanceChannel_polynomialRateSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃ τ : ℕ → ℝ,
        (∀ n : ℕ,
          τ n ∈ Set.Ioo b T
            ∧
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          H3TerminalDecayPolynomialRatesAt u T b (τ n))
          ∧
        Tendsto τ atTop (𝓝 T)
    )
      ∨
    (
      ∃ τ : ℕ → ℝ,
        (∀ n : ℕ,
          τ n ∈ Set.Ioo b T
            ∧
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          H3TerminalTransportPolynomialRatesAt u T b (τ n))
          ∧
        Tendsto τ atTop (𝓝 T)
    ) := by
  rcases
    frequently_fixedBalanceChannel_polynomialRates_of_noH3PathExtension
      hH3 hNoExtension hClass hb
    with hDecay | hTransport

  · left
    exact
      exists_terminalSequence_of_frequently_fixedChannel
        hb.2
        hDecay

  · right
    exact
      exists_terminalSequence_of_frequently_fixedChannel
        hb.2
        hTransport

/-- Neutral positive form: either smooth continuation exists, or a fixed decay
or transport channel carries all three polynomial rates along an explicit
terminal sequence. -/
theorem smoothContinuationExtension_or_exists_fixedBalanceChannel_polynomialRateSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      (
        ∃ τ : ℕ → ℝ,
          (∀ n : ℕ,
            τ n ∈ Set.Ioo b T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
              ∧
            H3TerminalDecayPolynomialRatesAt u T b (τ n))
            ∧
          Tendsto τ atTop (𝓝 T)
      )
        ∨
      (
        ∃ τ : ℕ → ℝ,
          (∀ n : ℕ,
            τ n ∈ Set.Ioo b T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
              ∧
            H3TerminalTransportPolynomialRatesAt u T b (τ n))
            ∧
          Tendsto τ atTop (𝓝 T)
      )
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (exists_fixedBalanceChannel_polynomialRateSequence_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Canonical midpoint-anchor specialization of the fixed polynomial
balance-channel terminal sequence. -/
theorem exists_fixedBalanceChannel_polynomialRateSequence_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ τ : ℕ → ℝ,
        (∀ n : ℕ,
          τ n ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T
            ∧
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          H3TerminalDecayPolynomialRatesAt
            u T (h3BKMKineticTailMidpoint a T) (τ n))
          ∧
        Tendsto τ atTop (𝓝 T)
    )
      ∨
    (
      ∃ τ : ℕ → ℝ,
        (∀ n : ℕ,
          τ n ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T
            ∧
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          H3TerminalTransportPolynomialRatesAt
            u T (h3BKMKineticTailMidpoint a T) (τ n))
          ∧
        Tendsto τ atTop (𝓝 T)
    ) := by
  exact
    exists_fixedBalanceChannel_polynomialRateSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor

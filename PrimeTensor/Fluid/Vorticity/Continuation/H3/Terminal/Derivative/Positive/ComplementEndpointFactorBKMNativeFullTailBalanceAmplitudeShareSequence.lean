import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeShareDichotomy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailFixedBalanceChannelIntrinsicCascade

/-!
# Explicit terminal sequence for the balance-amplitude share dichotomy

The branch-free balance amplitude satisfies the exact decomposition

`2 B = 2 D + I`,

where `D` is full H³ dissipation and `I` is the absolute imbalance of the two
signed balance channels.  The preceding file showed that, under hypothetical
nonextension, one of two structural regimes occurs cofinally while the
canonical amplitude retains all three polynomial rates:

* dissipation-scale: `B ≤ 2 D`;
* imbalance-scale: `B ≤ I`.

This file extracts the cofinal regime into an explicit physical-time sequence
chosen directly inside `(T - 1/(n+1), T)`.  On the same sequence we retain

* all three quantitative amplitude rates;
* raw amplitude divergence;
* physical-clock amplitude divergence;
* normalized amplitude divergence; and
* the entire intrinsic H³ cascade.

No new asymptotic hypothesis and no index-dependent rate are introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Local extraction utilities -/

private theorem exists_point_of_frequently_and_mem_balanceShare
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

private theorem tendsto_terminal_of_one_div_natSucc_localization_balanceShare
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

private theorem exists_terminalSequence_of_frequently_balanceShare
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
      exists_point_of_frequently_and_mem_balanceShare
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
    tendsto_terminal_of_one_div_natSucc_localization_balanceShare
      (fun n => (hτ n).2.1)

  exact ⟨τ, hτ, hTauTendsto⟩

/-! ## Amplitude and intrinsic cascade on an arbitrary terminal sequence -/

/-- The branch-free amplitude cascade and the intrinsic H³ cascade evaluated
along one explicit physical-time sequence. -/
def H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto τ atTop (𝓝 T)
    ∧
  Tendsto
    (fun n : ℕ => h3TerminalBalanceAmplitudeAt u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ =>
      (T - τ n) * h3TerminalBalanceAmplitudeAt u (τ n))
    atTop atTop
    ∧
  Tendsto
    (fun n : ℕ =>
      h3TerminalBalanceAmplitudeAt u (τ n) /
        velocityH3EnergyAt u (τ n))
    atTop atTop
    ∧
  H3TerminalIntrinsicCascadeAlong u T τ

/-- Any sequence converging to `T` from below inherits both the branch-free
amplitude cascade and the full intrinsic H³ cascade under hypothetical
nonextension. -/
theorem h3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTau : Tendsto τ atTop (𝓝 T))
    (hBelow : ∀ n : ℕ, τ n < T) :
    H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ := by
  have hTauLT :
      Tendsto τ atTop (𝓝[<] T) := by
    exact
      tendsto_nhdsWithin_iff.mpr
        ⟨
          hTau,
          Eventually.of_forall hBelow
        ⟩

  have hAmplitude :
      Tendsto
        (fun n : ℕ => h3TerminalBalanceAmplitudeAt u (τ n))
        atTop atTop :=
    (h3TerminalBalanceAmplitudeAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hPhysical :
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * h3TerminalBalanceAmplitudeAt u (τ n))
        atTop atTop :=
    (h3TerminalBalanceAmplitudePhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hNormalized :
      Tendsto
        (fun n : ℕ =>
          h3TerminalBalanceAmplitudeAt u (τ n) /
            velocityH3EnergyAt u (τ n))
        atTop atTop :=
    (h3TerminalBalanceAmplitudeNormalizedRate_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hIntrinsic :
      H3TerminalIntrinsicCascadeAlong u T τ :=
    h3TerminalIntrinsicCascadeAlong_of_noH3PathExtension
      hH3 hNoExtension hClass hTau hBelow

  exact
    ⟨
      hTau,
      hAmplitude,
      hPhysical,
      hNormalized,
      hIntrinsic
    ⟩

/-! ## Fixed share regime on one explicit terminal sequence -/

/-- Under hypothetical nonextension, one fixed balance-amplitude share regime
admits an explicit physical-time sequence converging to `T`.  At every selected
time the canonical amplitude carries all three polynomial rates, and the same
sequence carries the branch-free amplitude divergences and the full intrinsic
H³ cascade. -/
theorem exists_fixed_balanceAmplitudeShare_withCascade_of_noH3PathExtension
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
          H3TerminalBalanceAmplitudePolynomialRatesAt u T b (τ n)
            ∧
          H3TerminalBalanceAmplitudeDissipationScaleAt u (τ n))
          ∧
        H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ
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
          H3TerminalBalanceAmplitudePolynomialRatesAt u T b (τ n)
            ∧
          H3TerminalBalanceAmplitudeImbalanceScaleAt u (τ n))
          ∧
        H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ
    ) := by
  rcases
    frequently_fixed_balanceAmplitudeShare_polynomialRates_of_noH3PathExtension
      hH3 hNoExtension hClass hb
    with hDissipation | hImbalance

  · left
    obtain ⟨τ, hData, hTau⟩ :=
      exists_terminalSequence_of_frequently_balanceShare
        hb.2
        hDissipation

    have hCascade :
        H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ :=
      h3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hTau
        (fun n => (hData n).1.2)

    exact
      ⟨
        τ,
        (fun n =>
          ⟨
            (hData n).1,
            (hData n).2.1,
            (hData n).2.2.1,
            (hData n).2.2.2
          ⟩),
        hCascade
      ⟩

  · right
    obtain ⟨τ, hData, hTau⟩ :=
      exists_terminalSequence_of_frequently_balanceShare
        hb.2
        hImbalance

    have hCascade :
        H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ :=
      h3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hTau
        (fun n => (hData n).1.2)

    exact
      ⟨
        τ,
        (fun n =>
          ⟨
            (hData n).1,
            (hData n).2.1,
            (hData n).2.2.1,
            (hData n).2.2.2
          ⟩),
        hCascade
      ⟩

/-- Neutral positive form: either smooth continuation exists, or one fixed
balance-amplitude share regime is realized on an explicit terminal sequence
carrying the quantitative amplitude rates and the full intrinsic cascade. -/
theorem smoothContinuationExtension_or_exists_fixed_balanceAmplitudeShare_withCascade
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
            H3TerminalBalanceAmplitudePolynomialRatesAt u T b (τ n)
              ∧
            H3TerminalBalanceAmplitudeDissipationScaleAt u (τ n))
            ∧
          H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ
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
            H3TerminalBalanceAmplitudePolynomialRatesAt u T b (τ n)
              ∧
            H3TerminalBalanceAmplitudeImbalanceScaleAt u (τ n))
            ∧
          H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ
      )
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (exists_fixed_balanceAmplitudeShare_withCascade_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Canonical midpoint-anchor specialization of the fixed share-regime terminal
sequence. -/
theorem exists_fixed_balanceAmplitudeShare_withCascade_midpoint_of_noH3PathExtension
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
          H3TerminalBalanceAmplitudePolynomialRatesAt
              u T (h3BKMKineticTailMidpoint a T) (τ n)
            ∧
          H3TerminalBalanceAmplitudeDissipationScaleAt u (τ n))
          ∧
        H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ
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
          H3TerminalBalanceAmplitudePolynomialRatesAt
              u T (h3BKMKineticTailMidpoint a T) (τ n)
            ∧
          H3TerminalBalanceAmplitudeImbalanceScaleAt u (τ n))
          ∧
        H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ
    ) := by
  exact
    exists_fixed_balanceAmplitudeShare_withCascade_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor

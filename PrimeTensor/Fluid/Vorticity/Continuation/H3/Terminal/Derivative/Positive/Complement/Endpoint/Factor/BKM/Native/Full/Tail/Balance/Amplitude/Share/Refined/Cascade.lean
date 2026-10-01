import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Share.Sequence

/-!
# Refining the balance-amplitude share sequence

The canonical balance amplitude satisfies the exact identity

`2 B = 2 D + I`,

where `D` is full H³ dissipation and `I` is the absolute imbalance of the two
signed balance channels.

The preceding terminal-sequence dichotomy freezes one of two cofinal regimes:

* dissipation-scale: `B ≤ 2D`;
* imbalance-scale: `B ≤ I`.

The exact identity sharpens these into complementary half-share corridors:

* dissipation-scale gives `B/2 ≤ D ≤ B` and `I ≤ B`;
* imbalance-scale gives `2D ≤ B` and `B ≤ I ≤ 2B`.

In the imbalance-scale branch, `I` is therefore comparable to `B` from both
sides.  It inherits all three canonical polynomial rates, together with raw,
physical-clock, and full-energy-normalized divergence on the same explicit
physical-time sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- In the dissipation-scale regime, full dissipation occupies at least half of
the canonical amplitude, while imbalance is at most the amplitude. -/
theorem h3TerminalBalanceAmplitude_dissipationShare_half_corridor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hScale : H3TerminalBalanceAmplitudeDissipationScaleAt u t) :
    h3TerminalBalanceAmplitudeAt u t / 2
        ≤ velocityH3DissipationAt u t
      ∧
    velocityH3DissipationAt u t
        ≤ h3TerminalBalanceAmplitudeAt u t
      ∧
    h3TerminalBalanceImbalanceAt u t
        ≤ h3TerminalBalanceAmplitudeAt u t := by
  have hExact :=
    two_mul_h3TerminalBalanceAmplitudeAt_eq_two_mul_dissipation_add_imbalance
      hH3 hClass ht

  have hDLeB :=
    velocityH3DissipationAt_le_h3TerminalBalanceAmplitudeAt
      hH3 hClass ht

  have hScale' :
      h3TerminalBalanceAmplitudeAt u t
        ≤ 2 * velocityH3DissipationAt u t := by
    exact hScale

  have hHalf :
      h3TerminalBalanceAmplitudeAt u t / 2
        ≤ velocityH3DissipationAt u t := by
    linarith

  have hILeB :
      h3TerminalBalanceImbalanceAt u t
        ≤ h3TerminalBalanceAmplitudeAt u t := by
    linarith

  exact ⟨hHalf, hDLeB, hILeB⟩

/-- In the imbalance-scale regime, full dissipation occupies at most half of
`B`, while imbalance lies between one and two copies of `B`. -/
theorem h3TerminalBalanceAmplitude_imbalanceShare_half_corridor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hScale : H3TerminalBalanceAmplitudeImbalanceScaleAt u t) :
    2 * velocityH3DissipationAt u t
        ≤ h3TerminalBalanceAmplitudeAt u t
      ∧
    h3TerminalBalanceAmplitudeAt u t
        ≤ h3TerminalBalanceImbalanceAt u t
      ∧
    h3TerminalBalanceImbalanceAt u t
        ≤ 2 * h3TerminalBalanceAmplitudeAt u t := by
  have hExact :=
    two_mul_h3TerminalBalanceAmplitudeAt_eq_two_mul_dissipation_add_imbalance
      hH3 hClass ht

  have hDNonneg :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t

  have hScale' :
      h3TerminalBalanceAmplitudeAt u t
        ≤ h3TerminalBalanceImbalanceAt u t := by
    exact hScale

  have hTwoDLeB :
      2 * velocityH3DissipationAt u t
        ≤ h3TerminalBalanceAmplitudeAt u t := by
    linarith

  have hILeTwoB :
      h3TerminalBalanceImbalanceAt u t
        ≤ 2 * h3TerminalBalanceAmplitudeAt u t := by
    linarith

  exact ⟨hTwoDLeB, hScale', hILeTwoB⟩

/-- The three polynomial terminal rates transferred from the canonical balance
amplitude to the absolute balance imbalance. -/
def H3TerminalBalanceImbalancePolynomialRatesAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t : ℝ) : Prop :=
  1 ≤
      81
        * h3PathSqrtEnergyRiccatiCoefficient ^ 8
        * (T - t) ^ 8
        * velocityH3Energy0At u b
        * h3TerminalBalanceImbalanceAt u t ^ 3
    ∧
  1 ≤
      81
        * h3PathSqrtEnergyRiccatiCoefficient ^ 8
        * velocityH3Energy0At u b
        * (T - t) ^ 5
        * ((T - t) * h3TerminalBalanceImbalanceAt u t) ^ 3
    ∧
  1 ≤
      3
        * h3PathSqrtEnergyRiccatiCoefficient ^ 2
        * (velocityH3Energy0At u b + 1)
        * (4 + 3 * velocityH3Energy0At u b) ^ 3
        * (T - t) ^ 2
        *
          (h3TerminalBalanceImbalanceAt u t /
            velocityH3EnergyAt u t) ^ 3

/-- On an imbalance-scale time, every canonical amplitude polynomial rate
transfers directly to the absolute balance imbalance. -/
theorem h3TerminalBalanceImbalance_polynomialRates_of_imbalanceScale
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hRates : H3TerminalBalanceAmplitudePolynomialRatesAt u T b t)
    (hScale : H3TerminalBalanceAmplitudeImbalanceScaleAt u t) :
    H3TerminalBalanceImbalancePolynomialRatesAt u T b t := by
  have hDNonneg :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t

  have hDLeB :=
    velocityH3DissipationAt_le_h3TerminalBalanceAmplitudeAt
      hH3 hClass ht

  have hBNonneg :
      0 ≤ h3TerminalBalanceAmplitudeAt u t :=
    le_trans hDNonneg hDLeB

  have hINonneg :
      0 ≤ h3TerminalBalanceImbalanceAt u t :=
    h3TerminalBalanceImbalanceAt_nonneg u t

  have hBI :
      h3TerminalBalanceAmplitudeAt u t
        ≤ h3TerminalBalanceImbalanceAt u t :=
    hScale

  have hRawPow :
      h3TerminalBalanceAmplitudeAt u t ^ 3
        ≤ h3TerminalBalanceImbalanceAt u t ^ 3 :=
    pow_le_pow_left₀ hBNonneg hBI 3

  have hE0Nonneg :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b

  have hRawPrefNonneg :
      0 ≤
        81
          * h3PathSqrtEnergyRiccatiCoefficient ^ 8
          * (T - t) ^ 8
          * velocityH3Energy0At u b := by
    positivity

  have hRaw :
      1 ≤
        81
          * h3PathSqrtEnergyRiccatiCoefficient ^ 8
          * (T - t) ^ 8
          * velocityH3Energy0At u b
          * h3TerminalBalanceImbalanceAt u t ^ 3 := by
    exact
      le_trans
        hRates.1
        (mul_le_mul_of_nonneg_left hRawPow hRawPrefNonneg)

  have hDtNonneg :
      0 ≤ T - t := by
    linarith [ht.2]

  have hClockLe :
      (T - t) * h3TerminalBalanceAmplitudeAt u t
        ≤
      (T - t) * h3TerminalBalanceImbalanceAt u t :=
    mul_le_mul_of_nonneg_left hBI hDtNonneg

  have hClockBNonneg :
      0 ≤ (T - t) * h3TerminalBalanceAmplitudeAt u t :=
    mul_nonneg hDtNonneg hBNonneg

  have hClockPow :
      ((T - t) * h3TerminalBalanceAmplitudeAt u t) ^ 3
        ≤
      ((T - t) * h3TerminalBalanceImbalanceAt u t) ^ 3 :=
    pow_le_pow_left₀ hClockBNonneg hClockLe 3

  have hPhysicalPrefNonneg :
      0 ≤
        81
          * h3PathSqrtEnergyRiccatiCoefficient ^ 8
          * velocityH3Energy0At u b
          * (T - t) ^ 5 := by
    positivity

  have hPhysical :
      1 ≤
        81
          * h3PathSqrtEnergyRiccatiCoefficient ^ 8
          * velocityH3Energy0At u b
          * (T - t) ^ 5
          * ((T - t) * h3TerminalBalanceImbalanceAt u t) ^ 3 := by
    exact
      le_trans
        hRates.2.1
        (mul_le_mul_of_nonneg_left hClockPow hPhysicalPrefNonneg)

  have hEnergyOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEnergyNonneg :
      0 ≤ velocityH3EnergyAt u t := by
    linarith

  have hDivLe :
      h3TerminalBalanceAmplitudeAt u t /
          velocityH3EnergyAt u t
        ≤
      h3TerminalBalanceImbalanceAt u t /
          velocityH3EnergyAt u t :=
    div_le_div_of_nonneg_right hBI hEnergyNonneg

  have hBDivNonneg :
      0 ≤
        h3TerminalBalanceAmplitudeAt u t /
          velocityH3EnergyAt u t :=
    div_nonneg hBNonneg hEnergyNonneg

  have hDivPow :
      (h3TerminalBalanceAmplitudeAt u t /
          velocityH3EnergyAt u t) ^ 3
        ≤
      (h3TerminalBalanceImbalanceAt u t /
          velocityH3EnergyAt u t) ^ 3 :=
    pow_le_pow_left₀ hBDivNonneg hDivLe 3

  have hNormalizedPrefNonneg :
      0 ≤
        3
          * h3PathSqrtEnergyRiccatiCoefficient ^ 2
          * (velocityH3Energy0At u b + 1)
          * (4 + 3 * velocityH3Energy0At u b) ^ 3
          * (T - t) ^ 2 := by
    positivity

  have hNormalized :
      1 ≤
        3
          * h3PathSqrtEnergyRiccatiCoefficient ^ 2
          * (velocityH3Energy0At u b + 1)
          * (4 + 3 * velocityH3Energy0At u b) ^ 3
          * (T - t) ^ 2
          *
            (h3TerminalBalanceImbalanceAt u t /
              velocityH3EnergyAt u t) ^ 3 := by
    exact
      le_trans
        hRates.2.2
        (mul_le_mul_of_nonneg_left hDivPow hNormalizedPrefNonneg)

  exact ⟨hRaw, hPhysical, hNormalized⟩

/-- Raw, physical-clock, and normalized imbalance divergence along one explicit
terminal sequence. -/
def H3TerminalBalanceImbalanceCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ => h3TerminalBalanceImbalanceAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (T - τ n) * h3TerminalBalanceImbalanceAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceImbalanceAt u (τ n) /
          velocityH3EnergyAt u (τ n))
      atTop atTop

/-- If every point of an amplitude-cascade sequence is imbalance-scale, the
imbalance itself diverges in raw, physical-clock, and normalized forms. -/
theorem h3TerminalBalanceImbalanceCascadeAlong_of_imbalanceScale
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {τ : ℕ → ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hScale :
      ∀ n : ℕ,
        H3TerminalBalanceAmplitudeImbalanceScaleAt u (τ n))
    (hCascade :
      H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ) :
    H3TerminalBalanceImbalanceCascadeAlong u T τ := by
  have hRaw :
      Tendsto
        (fun n : ℕ => h3TerminalBalanceImbalanceAt u (τ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    have hEventually :=
      hCascade.2.1.eventually
        (eventually_ge_atTop M)
    filter_upwards [hEventually] with n hn
    exact le_trans hn (hScale n)

  have hPhysical :
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * h3TerminalBalanceImbalanceAt u (τ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    have hEventually :=
      hCascade.2.2.1.eventually
        (eventually_ge_atTop M)
    filter_upwards [hEventually] with n hn
    have hDt : 0 ≤ T - τ n := by
      linarith [(hAt n).2]
    have hDom :=
      mul_le_mul_of_nonneg_left (hScale n) hDt
    exact le_trans hn hDom

  have hNormalized :
      Tendsto
        (fun n : ℕ =>
          h3TerminalBalanceImbalanceAt u (τ n) /
            velocityH3EnergyAt u (τ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    have hEventually :=
      hCascade.2.2.2.1.eventually
        (eventually_ge_atTop M)
    filter_upwards [hEventually] with n hn
    have hEnergyNonneg :
        0 ≤ velocityH3EnergyAt u (τ n) := by
      have hOne : 1 ≤ velocityH3EnergyAt u (τ n) :=
        one_le_velocityH3EnergyAt u (τ n)
      linarith
    have hDom :=
      div_le_div_of_nonneg_right
        (hScale n)
        hEnergyNonneg
    exact le_trans hn hDom

  exact ⟨hRaw, hPhysical, hNormalized⟩

/-- Refined consequence package for the fixed balance-amplitude share sequence.
The dissipation branch gains the exact half-share corridor.  The imbalance
branch gains the complementary half-share corridor, all three imbalance
polynomial rates, and all three imbalance divergences on the same sequence. -/
theorem exists_fixed_balanceAmplitudeShare_refinedCascade_of_noH3PathExtension
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
          ∧
        (∀ n : ℕ,
          h3TerminalBalanceAmplitudeAt u (τ n) / 2
              ≤ velocityH3DissipationAt u (τ n)
            ∧
          velocityH3DissipationAt u (τ n)
              ≤ h3TerminalBalanceAmplitudeAt u (τ n)
            ∧
          h3TerminalBalanceImbalanceAt u (τ n)
              ≤ h3TerminalBalanceAmplitudeAt u (τ n))
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
          ∧
        (∀ n : ℕ,
          2 * velocityH3DissipationAt u (τ n)
              ≤ h3TerminalBalanceAmplitudeAt u (τ n)
            ∧
          h3TerminalBalanceAmplitudeAt u (τ n)
              ≤ h3TerminalBalanceImbalanceAt u (τ n)
            ∧
          h3TerminalBalanceImbalanceAt u (τ n)
              ≤ 2 * h3TerminalBalanceAmplitudeAt u (τ n)
            ∧
          H3TerminalBalanceImbalancePolynomialRatesAt u T b (τ n))
          ∧
        H3TerminalBalanceImbalanceCascadeAlong u T τ
    ) := by
  rcases
    exists_fixed_balanceAmplitudeShare_withCascade_of_noH3PathExtension
      hH3 hNoExtension hClass hb
    with hDissipation | hImbalance

  · left
    rcases hDissipation with ⟨τ, hData, hCascade⟩

    have hCorridor :
        ∀ n : ℕ,
          h3TerminalBalanceAmplitudeAt u (τ n) / 2
              ≤ velocityH3DissipationAt u (τ n)
            ∧
          velocityH3DissipationAt u (τ n)
              ≤ h3TerminalBalanceAmplitudeAt u (τ n)
            ∧
          h3TerminalBalanceImbalanceAt u (τ n)
              ≤ h3TerminalBalanceAmplitudeAt u (τ n) := by
      intro n
      have htClass : τ n ∈ Set.Ioo a T :=
        ⟨
          lt_trans hb.1 (hData n).1.1,
          (hData n).1.2
        ⟩
      exact
        h3TerminalBalanceAmplitude_dissipationShare_half_corridor
          hH3
          hClass
          htClass
          (hData n).2.2.2

    exact ⟨τ, hData, hCascade, hCorridor⟩

  · right
    rcases hImbalance with ⟨τ, hData, hCascade⟩

    have hAt :
        ∀ n : ℕ,
          τ n ∈ Set.Ioo a T := by
      intro n
      exact
        ⟨
          lt_trans hb.1 (hData n).1.1,
          (hData n).1.2
        ⟩

    have hRefined :
        ∀ n : ℕ,
          2 * velocityH3DissipationAt u (τ n)
              ≤ h3TerminalBalanceAmplitudeAt u (τ n)
            ∧
          h3TerminalBalanceAmplitudeAt u (τ n)
              ≤ h3TerminalBalanceImbalanceAt u (τ n)
            ∧
          h3TerminalBalanceImbalanceAt u (τ n)
              ≤ 2 * h3TerminalBalanceAmplitudeAt u (τ n)
            ∧
          H3TerminalBalanceImbalancePolynomialRatesAt u T b (τ n) := by
      intro n
      have hCorridor :=
        h3TerminalBalanceAmplitude_imbalanceShare_half_corridor
          hH3
          hClass
          (hAt n)
          (hData n).2.2.2

      have hRates :=
        h3TerminalBalanceImbalance_polynomialRates_of_imbalanceScale
          hH3
          hClass
          (hAt n)
          (hData n).2.2.1
          (hData n).2.2.2

      exact
        ⟨
          hCorridor.1,
          hCorridor.2.1,
          hCorridor.2.2,
          hRates
        ⟩

    have hImbalanceCascade :
        H3TerminalBalanceImbalanceCascadeAlong u T τ :=
      h3TerminalBalanceImbalanceCascadeAlong_of_imbalanceScale
        hClass
        hAt
        (fun n => (hData n).2.2.2)
        hCascade

    exact
      ⟨
        τ,
        hData,
        hCascade,
        hRefined,
        hImbalanceCascade
      ⟩

/-- Neutral positive form of the refined balance-amplitude share cascade. -/
theorem smoothContinuationExtension_or_exists_fixed_balanceAmplitudeShare_refinedCascade
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
            ∧
          (∀ n : ℕ,
            h3TerminalBalanceAmplitudeAt u (τ n) / 2
                ≤ velocityH3DissipationAt u (τ n)
              ∧
            velocityH3DissipationAt u (τ n)
                ≤ h3TerminalBalanceAmplitudeAt u (τ n)
              ∧
            h3TerminalBalanceImbalanceAt u (τ n)
                ≤ h3TerminalBalanceAmplitudeAt u (τ n))
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
            ∧
          (∀ n : ℕ,
            2 * velocityH3DissipationAt u (τ n)
                ≤ h3TerminalBalanceAmplitudeAt u (τ n)
              ∧
            h3TerminalBalanceAmplitudeAt u (τ n)
                ≤ h3TerminalBalanceImbalanceAt u (τ n)
              ∧
            h3TerminalBalanceImbalanceAt u (τ n)
                ≤ 2 * h3TerminalBalanceAmplitudeAt u (τ n)
              ∧
            H3TerminalBalanceImbalancePolynomialRatesAt u T b (τ n))
            ∧
          H3TerminalBalanceImbalanceCascadeAlong u T τ
      )
    ) := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact
      Or.inr
        (exists_fixed_balanceAmplitudeShare_refinedCascade_of_noH3PathExtension
          hH3 hExtension hClass hb)

end

end Euclidean
end Bridge
end PrimeTensor

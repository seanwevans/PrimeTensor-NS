import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeDecomposition

/-!
# Dissipation versus imbalance share of the canonical H³ balance amplitude

The exact identity

`2 B(t) = 2 D(t) + I(t)`

with `I(t) ≥ 0` gives the universal corridor

`D(t) ≤ B(t)`,
`I(t) ≤ 2 B(t)`.

It also yields a branch-free pointwise alternative:

* `B(t) ≤ 2 D(t)`, so the canonical amplitude is within a factor two of full
  dissipation; or
* `B(t) ≤ I(t)`, so the channel imbalance is at least as large as the
  canonical amplitude.

Under hypothetical nonextension the canonical amplitude already carries raw,
physical-clock, and normalized cubic terminal rates on one full tail.  Hence
one of these two structural regimes occurs cofinally while retaining all three
quantitative amplitude rates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The three quantitative polynomial rates carried by the branch-free
canonical balance amplitude. -/
def H3TerminalBalanceAmplitudePolynomialRatesAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t : ℝ) : Prop :=
  1 ≤
      81
        * h3PathSqrtEnergyRiccatiCoefficient ^ 8
        * (T - t) ^ 8
        * velocityH3Energy0At u b
        * h3TerminalBalanceAmplitudeAt u t ^ 3
    ∧
  1 ≤
      81
        * h3PathSqrtEnergyRiccatiCoefficient ^ 8
        * velocityH3Energy0At u b
        * (T - t) ^ 5
        * ((T - t) * h3TerminalBalanceAmplitudeAt u t) ^ 3
    ∧
  1 ≤
      3
        * h3PathSqrtEnergyRiccatiCoefficient ^ 2
        * (velocityH3Energy0At u b + 1)
        * (4 + 3 * velocityH3Energy0At u b) ^ 3
        * (T - t) ^ 2
        *
          (h3TerminalBalanceAmplitudeAt u t /
            velocityH3EnergyAt u t) ^ 3

/-- The canonical amplitude is dissipation-scale when it is at most twice the
full H³ dissipation. -/
def H3TerminalBalanceAmplitudeDissipationScaleAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  h3TerminalBalanceAmplitudeAt u t
    ≤
  2 * velocityH3DissipationAt u t

/-- The canonical amplitude is imbalance-scale when the absolute channel
imbalance is at least the amplitude itself. -/
def H3TerminalBalanceAmplitudeImbalanceScaleAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  h3TerminalBalanceAmplitudeAt u t
    ≤
  h3TerminalBalanceImbalanceAt u t

/-- Exact pointwise corridor for the canonical balance amplitude.  Full
+dissipation never exceeds the amplitude, imbalance never exceeds twice the
+amplitude, and at least one of the two quantities captures at least half of the
+amplitude scale. -/
theorem h3TerminalBalanceAmplitude_dissipation_imbalance_corridor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3DissipationAt u t
        ≤ h3TerminalBalanceAmplitudeAt u t
      ∧
    h3TerminalBalanceImbalanceAt u t
        ≤ 2 * h3TerminalBalanceAmplitudeAt u t
      ∧
    (
      H3TerminalBalanceAmplitudeDissipationScaleAt u t
        ∨
      H3TerminalBalanceAmplitudeImbalanceScaleAt u t
    ) := by
  have hDLeB :
      velocityH3DissipationAt u t
        ≤
      h3TerminalBalanceAmplitudeAt u t :=
    velocityH3DissipationAt_le_h3TerminalBalanceAmplitudeAt
      hH3 hClass ht

  have hExact :=
    two_mul_h3TerminalBalanceAmplitudeAt_eq_two_mul_dissipation_add_imbalance
      hH3 hClass ht

  have hDNonneg :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t

  have hILe :
      h3TerminalBalanceImbalanceAt u t
        ≤
      2 * h3TerminalBalanceAmplitudeAt u t := by
    linarith

  refine ⟨hDLeB, hILe, ?_⟩

  by_cases hDissipationScale :
      h3TerminalBalanceAmplitudeAt u t
        ≤
      2 * velocityH3DissipationAt u t

  · exact Or.inl hDissipationScale

  · right
    have hStrict :
        2 * velocityH3DissipationAt u t
          <
        h3TerminalBalanceAmplitudeAt u t :=
      lt_of_not_ge hDissipationScale

    unfold H3TerminalBalanceAmplitudeImbalanceScaleAt
    linarith

/-- Under hypothetical nonextension, all three branch-free amplitude rates hold
simultaneously on one strict terminal tail. -/
theorem exists_terminalTail_balanceAmplitude_polynomialRates_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        H3TerminalBalanceAmplitudePolynomialRatesAt u T b t := by
  obtain ⟨cRaw, hcRaw, hRaw⟩ :=
    exists_terminalTail_balanceAmplitude_raw_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  obtain ⟨cPhysical, hcPhysical, hPhysical⟩ :=
    exists_terminalTail_balanceAmplitude_physicalClock_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  obtain ⟨cNormalized, hcNormalized, hNormalized⟩ :=
    exists_terminalTail_balanceAmplitude_div_energy_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  let c : ℝ :=
    max cRaw (max cPhysical cNormalized)

  have hcLower : b < c := by
    dsimp only [c]
    exact
      lt_of_lt_of_le
        hcRaw.1
        (le_max_left cRaw (max cPhysical cNormalized))

  have hcUpper : c < T := by
    dsimp only [c]
    exact
      max_lt
        hcRaw.2
        (max_lt hcPhysical.2 hcNormalized.2)

  refine ⟨c, ⟨hcLower, hcUpper⟩, ?_⟩

  intro t ht

  have htRaw : t ∈ Set.Ioo cRaw T :=
    ⟨
      lt_of_le_of_lt
        (le_max_left cRaw (max cPhysical cNormalized))
        ht.1,
      ht.2
    ⟩

  have htPhysical : t ∈ Set.Ioo cPhysical T :=
    ⟨
      lt_of_le_of_lt
        (le_trans
          (le_max_left cPhysical cNormalized)
          (le_max_right cRaw (max cPhysical cNormalized)))
        ht.1,
      ht.2
    ⟩

  have htNormalized : t ∈ Set.Ioo cNormalized T :=
    ⟨
      lt_of_le_of_lt
        (le_trans
          (le_max_right cPhysical cNormalized)
          (le_max_right cRaw (max cPhysical cNormalized)))
        ht.1,
      ht.2
    ⟩

  exact
    ⟨
      hRaw t htRaw,
      hPhysical t htPhysical,
      hNormalized t htNormalized
    ⟩

/-- Under hypothetical nonextension, one fixed amplitude-share regime occurs
arbitrarily close to `T` while retaining all three quantitative canonical
amplitude rates. -/
theorem frequently_fixed_balanceAmplitudeShare_polynomialRates_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalBalanceAmplitudePolynomialRatesAt u T b t
          ∧
        H3TerminalBalanceAmplitudeDissipationScaleAt u t
    )
      ∨
    (
      ∃ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalBalanceAmplitudePolynomialRatesAt u T b t
          ∧
        H3TerminalBalanceAmplitudeImbalanceScaleAt u t
    ) := by
  obtain ⟨c, hc, hRates⟩ :=
    exists_terminalTail_balanceAmplitude_polynomialRates_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  have hEventuallyOr :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        (
          H3TerminalBalanceAmplitudePolynomialRatesAt u T b t
            ∧
          H3TerminalBalanceAmplitudeDissipationScaleAt u t
        )
          ∨
        (
          H3TerminalBalanceAmplitudePolynomialRatesAt u T b t
            ∧
          H3TerminalBalanceAmplitudeImbalanceScaleAt u t
        ) := by
    filter_upwards [Ioo_mem_nhdsLT hc.2] with t ht

    have htClass : t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hb.1 (lt_trans hc.1 ht.1),
        ht.2
      ⟩

    have hCorridor :=
      h3TerminalBalanceAmplitude_dissipation_imbalance_corridor
        hH3 hClass htClass

    rcases hCorridor.2.2 with hDissipation | hImbalance

    · exact Or.inl ⟨hRates t ht, hDissipation⟩
    · exact Or.inr ⟨hRates t ht, hImbalance⟩

  by_cases hDissipationFrequently :
      ∃ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalBalanceAmplitudePolynomialRatesAt u T b t
          ∧
        H3TerminalBalanceAmplitudeDissipationScaleAt u t

  · exact Or.inl hDissipationFrequently

  · right

    have hEventuallyNotDissipation :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          ¬ (
            H3TerminalBalanceAmplitudePolynomialRatesAt u T b t
              ∧
            H3TerminalBalanceAmplitudeDissipationScaleAt u t
          ) :=
      (not_frequently).1 hDissipationFrequently

    have hEventuallyImbalance :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          H3TerminalBalanceAmplitudePolynomialRatesAt u T b t
            ∧
          H3TerminalBalanceAmplitudeImbalanceScaleAt u t := by
      filter_upwards [hEventuallyOr, hEventuallyNotDissipation]
        with t hEither hNotDissipation
      exact hEither.resolve_left hNotDissipation

    exact hEventuallyImbalance.frequently

/-- Neutral positive form of the cofinal amplitude-share classification. -/
theorem smoothContinuationExtension_or_frequently_fixed_balanceAmplitudeShare_polynomialRates
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
        ∃ᶠ t : ℝ in 𝓝[<] T,
          H3TerminalBalanceAmplitudePolynomialRatesAt u T b t
            ∧
          H3TerminalBalanceAmplitudeDissipationScaleAt u t
      )
        ∨
      (
        ∃ᶠ t : ℝ in 𝓝[<] T,
          H3TerminalBalanceAmplitudePolynomialRatesAt u T b t
            ∧
          H3TerminalBalanceAmplitudeImbalanceScaleAt u t
      )
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (frequently_fixed_balanceAmplitudeShare_polynomialRates_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Canonical midpoint-anchor specialization of the cofinal amplitude-share
classification. -/
theorem frequently_fixed_balanceAmplitudeShare_polynomialRates_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalBalanceAmplitudePolynomialRatesAt
            u T (h3BKMKineticTailMidpoint a T) t
          ∧
        H3TerminalBalanceAmplitudeDissipationScaleAt u t
    )
      ∨
    (
      ∃ᶠ t : ℝ in 𝓝[<] T,
        H3TerminalBalanceAmplitudePolynomialRatesAt
            u T (h3BKMKineticTailMidpoint a T) t
          ∧
        H3TerminalBalanceAmplitudeImbalanceScaleAt u t
    ) := by
  exact
    frequently_fixed_balanceAmplitudeShare_polynomialRates_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor

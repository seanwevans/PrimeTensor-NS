import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailFixedBalanceChannelPolynomialSequence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailPhysicalClocks

/-!
# Divergent fixed balance channel along the polynomial terminal sequence

The fixed-channel sequence extracted previously carries, at every index, the
raw inverse-`8/3`, physical-clock inverse-`5/3`, and full-energy normalized
inverse-`2/3` polynomial rates for one fixed H³ balance mechanism.

This file converts those polynomial inequalities into actual asymptotic limits
along the same physical-time sequence.  The normalized cubic rate gives

`X(τₙ) / E(τₙ) -> +∞`,

where `X` is either `-E'` or `-T_H3`.  Since the full H³ energy is at least one,
this forces the raw channel itself to diverge.  Combining the normalized
channel with the already-proved full-tail physical energy clock

`(T-t) E(t) -> +∞`

then yields

`(T-τₙ) X(τₙ) -> +∞`.

Thus one fixed balance mechanism carries all three qualitative divergences and
all three polynomial rates on one explicit terminal sequence.  The theorem is
neutral between rapid energy decay and adverse transport.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## A cubic terminal-rate limit lemma -/

private theorem tendsto_atTop_of_cubic_terminalRate
    {T C : ℝ}
    {τ R : ℕ → ℝ}
    (hC : 0 < C)
    (hTau : Tendsto τ atTop (𝓝 T))
    (hBelow : ∀ n : ℕ, τ n < T)
    (hRate :
      ∀ n : ℕ,
        1 ≤ C * (T - τ n) ^ 2 * (R n) ^ 3) :
    Tendsto R atTop atTop := by

  have hDistanceRaw :
      Tendsto
        (fun n : ℕ => T - τ n)
        atTop
        (𝓝 (T - T)) :=
    tendsto_const_nhds.sub hTau

  have hDistance :
      Tendsto
        (fun n : ℕ => T - τ n)
        atTop
        (𝓝 0) := by
    simpa only [sub_self] using hDistanceRaw

  have hDistanceSqRaw :
      Tendsto
        (fun n : ℕ => (T - τ n) * (T - τ n))
        atTop
        (𝓝 ((0 : ℝ) * 0)) :=
    hDistance.mul hDistance

  have hDistanceSq :
      Tendsto
        (fun n : ℕ => (T - τ n) ^ 2)
        atTop
        (𝓝 0) := by
    simpa only [pow_two, zero_mul] using hDistanceSqRaw

  have hRPos :
      ∀ n : ℕ, 0 < R n := by
    intro n

    have hGapPos :
        0 < T - τ n :=
      sub_pos.mpr (hBelow n)

    have hCoeffPos :
        0 < C * (T - τ n) ^ 2 :=
      mul_pos hC (pow_pos hGapPos 2)

    have hRateN := hRate n

    by_contra hNot

    have hRNonpos :
        R n ≤ 0 :=
      le_of_not_gt hNot

    have hCubeNonpos :
        R n ^ 3 ≤ 0 := by
      calc
        R n ^ 3 = R n * (R n) ^ 2 := by ring
        _ ≤ 0 * (R n) ^ 2 :=
          mul_le_mul_of_nonneg_right
            hRNonpos
            (sq_nonneg (R n))
        _ = 0 := by ring

    have hProductNonpos :
        C * (T - τ n) ^ 2 * (R n) ^ 3 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt hCoeffPos)
        hCubeNonpos

    linarith

  refine tendsto_atTop.2 ?_
  intro M

  by_cases hM : M ≤ 0

  · exact
      Eventually.of_forall
        (fun n =>
          le_trans hM (le_of_lt (hRPos n)))

  · have hMPos : 0 < M :=
      lt_of_not_ge hM

    let D : ℝ :=
      C * M ^ 3

    have hDConst :
        Tendsto
          (fun _ : ℕ => D)
          atTop
          (𝓝 D) :=
      tendsto_const_nhds

    have hSmallTendsto :
        Tendsto
          (fun n : ℕ => D * (T - τ n) ^ 2)
          atTop
          (𝓝 0) := by
      simpa only [mul_zero] using
        hDConst.mul hDistanceSq

    have hSmall :
        ∀ᶠ n : ℕ in atTop,
          D * (T - τ n) ^ 2 < 1 :=
      (tendsto_order.1 hSmallTendsto).2
        1
        (by norm_num)

    filter_upwards [hSmall] with n hnSmall

    by_contra hNot

    have hRLt :
        R n < M :=
      lt_of_not_ge hNot

    have hCubeLt :
        R n ^ 3 < M ^ 3 :=
      pow_lt_pow_left₀
        hRLt
        (le_of_lt (hRPos n))
        (by norm_num)

    have hGapPos :
        0 < T - τ n :=
      sub_pos.mpr (hBelow n)

    have hCoeffPos :
        0 < C * (T - τ n) ^ 2 :=
      mul_pos hC (pow_pos hGapPos 2)

    have hScaledLt :
        C * (T - τ n) ^ 2 * (R n) ^ 3
          <
        C * (T - τ n) ^ 2 * M ^ 3 :=
      mul_lt_mul_of_pos_left
        hCubeLt
        hCoeffPos

    have hOneLt :
        1 < C * (T - τ n) ^ 2 * M ^ 3 :=
      lt_of_le_of_lt
        (hRate n)
        hScaledLt

    have hReorder :
        C * (T - τ n) ^ 2 * M ^ 3
          =
        D * (T - τ n) ^ 2 := by
      dsimp only [D]
      ring

    rw [hReorder] at hOneLt

    linarith

/-! ## Raw and physical limits from a normalized channel limit -/

private theorem fixedChannel_raw_and_physical_tendsto_atTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    {τ X : ℕ → ℝ}
    (hRatioTop :
      Tendsto
        (fun n : ℕ =>
          X n / velocityH3EnergyAt u (τ n))
        atTop
        atTop)
    (hEnergyClockTop :
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3EnergyAt u (τ n))
        atTop
        atTop) :
    Tendsto X atTop atTop
      ∧
    Tendsto
      (fun n : ℕ => (T - τ n) * X n)
      atTop
      atTop := by

  have hRawTop :
      Tendsto X atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    have hRatioEventually :
        ∀ᶠ n : ℕ in atTop,
          max M 1 ≤
            X n / velocityH3EnergyAt u (τ n) :=
      hRatioTop.eventually
        (eventually_ge_atTop (max M 1))

    filter_upwards [hRatioEventually] with n hRatio

    have hEnergyOne :
        1 ≤ velocityH3EnergyAt u (τ n) :=
      one_le_velocityH3EnergyAt u (τ n)

    have hEnergyPos :
        0 < velocityH3EnergyAt u (τ n) := by
      linarith

    have hRatioNonneg :
        0 ≤ X n / velocityH3EnergyAt u (τ n) := by
      exact
        le_trans
          (by norm_num : (0 : ℝ) ≤ 1)
          (le_trans
            (le_max_right M 1)
            hRatio)

    have hRecover :
        X n =
          (X n / velocityH3EnergyAt u (τ n))
            * velocityH3EnergyAt u (τ n) := by
      field_simp [ne_of_gt hEnergyPos]

    calc
      M ≤ max M 1 := le_max_left _ _
      _ ≤ X n / velocityH3EnergyAt u (τ n) := hRatio
      _ =
          (X n / velocityH3EnergyAt u (τ n)) * 1 := by
            ring
      _ ≤
          (X n / velocityH3EnergyAt u (τ n))
            * velocityH3EnergyAt u (τ n) :=
        mul_le_mul_of_nonneg_left
          hEnergyOne
          hRatioNonneg
      _ = X n := hRecover.symm

  have hPhysicalTop :
      Tendsto
        (fun n : ℕ => (T - τ n) * X n)
        atTop
        atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    have hRatioEventually :
        ∀ᶠ n : ℕ in atTop,
          max M 1 ≤
            X n / velocityH3EnergyAt u (τ n) :=
      hRatioTop.eventually
        (eventually_ge_atTop (max M 1))

    have hClockEventually :
        ∀ᶠ n : ℕ in atTop,
          1 ≤
            (T - τ n) * velocityH3EnergyAt u (τ n) :=
      hEnergyClockTop.eventually
        (eventually_ge_atTop 1)

    filter_upwards
      [hRatioEventually, hClockEventually]
      with n hRatio hClock

    have hEnergyOne :
        1 ≤ velocityH3EnergyAt u (τ n) :=
      one_le_velocityH3EnergyAt u (τ n)

    have hEnergyPos :
        0 < velocityH3EnergyAt u (τ n) := by
      linarith

    have hRatioNonneg :
        0 ≤ X n / velocityH3EnergyAt u (τ n) := by
      exact
        le_trans
          (by norm_num : (0 : ℝ) ≤ 1)
          (le_trans
            (le_max_right M 1)
            hRatio)

    have hRecover :
        (T - τ n) * X n
          =
        (X n / velocityH3EnergyAt u (τ n))
          * ((T - τ n) * velocityH3EnergyAt u (τ n)) := by
      field_simp [ne_of_gt hEnergyPos]

    calc
      M ≤ max M 1 := le_max_left _ _
      _ ≤ X n / velocityH3EnergyAt u (τ n) := hRatio
      _ =
          (X n / velocityH3EnergyAt u (τ n)) * 1 := by
            ring
      _ ≤
          (X n / velocityH3EnergyAt u (τ n))
            * ((T - τ n) * velocityH3EnergyAt u (τ n)) :=
        mul_le_mul_of_nonneg_left
          hClock
          hRatioNonneg
      _ = (T - τ n) * X n := hRecover.symm

  exact ⟨hRawTop, hPhysicalTop⟩

/-! ## Fixed-channel divergence sequence -/

/-- Under hypothetical nonextension, one fixed H³ balance mechanism carries
all three polynomial rates and all three corresponding divergences along one
explicit physical-time sequence converging to `T`. -/
theorem exists_fixedBalanceChannel_polynomialAndDivergenceSequence_of_noH3PathExtension
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
          ∧
        Tendsto
          (fun n : ℕ =>
            - deriv (velocityH3EnergyAt u) (τ n))
          atTop atTop
          ∧
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
          ∧
        Tendsto
          (fun n : ℕ =>
            - velocityH3TransportDerivativeAt u (τ n))
          atTop atTop
          ∧
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

  rcases
    exists_fixedBalanceChannel_polynomialRateSequence_of_noH3PathExtension
      hH3 hNoExtension hClass hb
    with hDecay | hTransport

  · rcases hDecay with ⟨τ, hData, hTau⟩

    let C : ℝ :=
      3
        * h3PathSqrtEnergyRiccatiCoefficient ^ 2
        * (velocityH3Energy0At u b + 1)
        * (4 + 3 * velocityH3Energy0At u b) ^ 3

    have hE0Nonneg :
        0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg u b

    have hCPos : 0 < C := by
      have hE0OnePos :
          0 < velocityH3Energy0At u b + 1 := by
        linarith
      have hFourPos :
          0 < 4 + 3 * velocityH3Energy0At u b := by
        linarith
      have hKsqPos :
          0 < h3PathSqrtEnergyRiccatiCoefficient ^ 2 :=
        pow_pos h3PathSqrtEnergyRiccatiCoefficient_pos 2
      have hFourCubePos :
          0 < (4 + 3 * velocityH3Energy0At u b) ^ 3 :=
        pow_pos hFourPos 3
      dsimp only [C]
      exact
        mul_pos
          (mul_pos
            (mul_pos
              (by norm_num : (0 : ℝ) < 3)
              hKsqPos)
            hE0OnePos)
          hFourCubePos

    have hRate :
        ∀ n : ℕ,
          1 ≤
            C * (T - τ n) ^ 2 *
              ((- deriv (velocityH3EnergyAt u) (τ n)) /
                velocityH3EnergyAt u (τ n)) ^ 3 := by
      intro n
      have hRates := (hData n).2.2
      dsimp only [H3TerminalDecayPolynomialRatesAt] at hRates
      dsimp only [C]
      exact hRates.2.2

    have hRatioTop :
        Tendsto
          (fun n : ℕ =>
            (- deriv (velocityH3EnergyAt u) (τ n)) /
              velocityH3EnergyAt u (τ n))
          atTop
          atTop :=
      tendsto_atTop_of_cubic_terminalRate
        hCPos
        hTau
        (fun n => (hData n).1.2)
        hRate

    have hTauLT :
        Tendsto τ atTop (𝓝[<] T) := by
      exact
        tendsto_nhdsWithin_iff.mpr
          ⟨
            hTau,
            Eventually.of_forall
              (fun n => (hData n).1.2)
          ⟩

    have hEnergyClockTop :
        Tendsto
          (fun n : ℕ =>
            (T - τ n) * velocityH3EnergyAt u (τ n))
          atTop
          atTop :=
      (velocityH3EnergyPhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3 hNoExtension hClass).comp hTauLT

    obtain ⟨hRawTop, hPhysicalTop⟩ :=
      fixedChannel_raw_and_physical_tendsto_atTop
        (u := u)
        (T := T)
        (τ := τ)
        (X := fun n : ℕ =>
          - deriv (velocityH3EnergyAt u) (τ n))
        hRatioTop
        hEnergyClockTop

    exact
      Or.inl
        ⟨
          τ,
          hData,
          hTau,
          hRawTop,
          hPhysicalTop,
          hRatioTop
        ⟩

  · rcases hTransport with ⟨τ, hData, hTau⟩

    let C : ℝ :=
      3
        * h3PathSqrtEnergyRiccatiCoefficient ^ 2
        * (velocityH3Energy0At u b + 1)
        * (4 + 3 * velocityH3Energy0At u b) ^ 3

    have hE0Nonneg :
        0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg u b

    have hCPos : 0 < C := by
      have hE0OnePos :
          0 < velocityH3Energy0At u b + 1 := by
        linarith
      have hFourPos :
          0 < 4 + 3 * velocityH3Energy0At u b := by
        linarith
      have hKsqPos :
          0 < h3PathSqrtEnergyRiccatiCoefficient ^ 2 :=
        pow_pos h3PathSqrtEnergyRiccatiCoefficient_pos 2
      have hFourCubePos :
          0 < (4 + 3 * velocityH3Energy0At u b) ^ 3 :=
        pow_pos hFourPos 3
      dsimp only [C]
      exact
        mul_pos
          (mul_pos
            (mul_pos
              (by norm_num : (0 : ℝ) < 3)
              hKsqPos)
            hE0OnePos)
          hFourCubePos

    have hRate :
        ∀ n : ℕ,
          1 ≤
            C * (T - τ n) ^ 2 *
              ((- velocityH3TransportDerivativeAt u (τ n)) /
                velocityH3EnergyAt u (τ n)) ^ 3 := by
      intro n
      have hRates := (hData n).2.2
      dsimp only [H3TerminalTransportPolynomialRatesAt] at hRates
      dsimp only [C]
      exact hRates.2.2

    have hRatioTop :
        Tendsto
          (fun n : ℕ =>
            (- velocityH3TransportDerivativeAt u (τ n)) /
              velocityH3EnergyAt u (τ n))
          atTop
          atTop :=
      tendsto_atTop_of_cubic_terminalRate
        hCPos
        hTau
        (fun n => (hData n).1.2)
        hRate

    have hTauLT :
        Tendsto τ atTop (𝓝[<] T) := by
      exact
        tendsto_nhdsWithin_iff.mpr
          ⟨
            hTau,
            Eventually.of_forall
              (fun n => (hData n).1.2)
          ⟩

    have hEnergyClockTop :
        Tendsto
          (fun n : ℕ =>
            (T - τ n) * velocityH3EnergyAt u (τ n))
          atTop
          atTop :=
      (velocityH3EnergyPhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3 hNoExtension hClass).comp hTauLT

    obtain ⟨hRawTop, hPhysicalTop⟩ :=
      fixedChannel_raw_and_physical_tendsto_atTop
        (u := u)
        (T := T)
        (τ := τ)
        (X := fun n : ℕ =>
          - velocityH3TransportDerivativeAt u (τ n))
        hRatioTop
        hEnergyClockTop

    exact
      Or.inr
        ⟨
          τ,
          hData,
          hTau,
          hRawTop,
          hPhysicalTop,
          hRatioTop
        ⟩

/-- Canonical midpoint-anchor specialization of the fixed-channel divergence
sequence. -/
theorem exists_fixedBalanceChannel_polynomialAndDivergenceSequence_midpoint_of_noH3PathExtension
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
          ∧
        Tendsto
          (fun n : ℕ =>
            - deriv (velocityH3EnergyAt u) (τ n))
          atTop atTop
          ∧
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
          ∧
        Tendsto
          (fun n : ℕ =>
            - velocityH3TransportDerivativeAt u (τ n))
          atTop atTop
          ∧
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
  exact
    exists_fixedBalanceChannel_polynomialAndDivergenceSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor

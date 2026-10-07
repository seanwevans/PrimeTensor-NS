import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Second.Moment10
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher

/-!
# Quantitative order-fourteen moment to higher-radial transfer

The order-fourteen forcing moment is controlled by neighboring order-fourteen
and order-sixteen radial square masses through the standard inverse-Bessel
factor.

This preserves an arbitrary quantitative lower-rate function, freezes one
radial square channel, and simultaneously lifts that channel into extended
higher-radial shift `10` or `12`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

theorem exists_fixed_h3TerminalForcingThirdQMoment14RadialSquareChannel_rate_subsequence
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
    (rate : ℕ → ℝ)
    (K : ℝ)
    (hK0 : 0 ≤ K)
    (hRate :
      ∀ n : ℕ,
        rate n
          <
        K
          *
        (
          h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) j
        ) ^ 4)
    (hMomentTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMoment14MassAt
              hH3 hClass (hτ n) j
        )
        atTop
        atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        StrictMono s
          ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T)
          ∧
        (
          ∀ n : ℕ,
            rate (s n)
              <
            K
              *
            (
              h3StandardInverseBesselWeightL2Factor
                *
              (
                2
                  *
                Real.sqrt
                  (
                    h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                      hH3 hClass (hτ (s n)) j q
                  )
              )
            ) ^ 4
        )
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                hH3 hClass (hτ (s n)) j q
          )
          atTop
          atTop
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass
                (h3TerminalForcingThirdQHigherRadialShift q)
                (τ (s n))
                (hτ (s n))
          )
          atTop
          (𝓝 ∞) := by

  classical

  let channel : ℕ → Fin 2 :=
    fun n =>
      if
        h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 16 j
          ≤
        h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass (hτ n) 14 j
      then 0
      else 1

  have hChosen :
      ∀ n : ℕ,
        h3TerminalForcingThirdQMoment14RadialSquareChannelAt
            hH3 hClass (hτ n) j (channel n)
          =
        max
          (
            h3TerminalForcingThirdQRawRadialSquareMassAt
              hH3 hClass (hτ n) 14 j
          )
          (
            h3TerminalForcingThirdQRawRadialSquareMassAt
              hH3 hClass (hτ n) 16 j
          ) := by

    intro n

    dsimp only [channel]

    by_cases h :
        h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 16 j
          ≤
        h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass (hτ n) 14 j

    · simp only [if_pos h]
      unfold h3TerminalForcingThirdQMoment14RadialSquareChannelAt
      simp only [if_pos]
      exact
        (max_eq_left h).symm

    · simp only [if_neg h]

      have hReverse :
          h3TerminalForcingThirdQRawRadialSquareMassAt
              hH3 hClass (hτ n) 14 j
            ≤
          h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 16 j :=
        le_of_lt
          (lt_of_not_ge h)

      unfold h3TerminalForcingThirdQMoment14RadialSquareChannelAt
      simp only [one_ne_zero]

      exact
        (max_eq_right hReverse).symm

  have hMaxTop :=
    h3TerminalForcingThirdQRawRadialSquareMassMax_tendstoAtTop_of_moment14_tendstoAtTop
      hH3 hClass j τ hτ hMomentTop

  have hChosenTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMoment14RadialSquareChannelAt
              hH3 hClass (hτ n) j (channel n)
        )
        atTop
        atTop := by

    simpa only [hChosen] using
      hMaxTop

  have hRateChosen :
      ∀ n : ℕ,
        rate n
          <
        K
          *
        (
          h3StandardInverseBesselWeightL2Factor
            *
          (
            2
              *
            Real.sqrt
              (
                h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                  hH3 hClass (hτ n) j (channel n)
              )
          )
        ) ^ 4 := by

    intro n

    let A : ℝ :=
      h3TerminalForcingThirdQRawRadialSquareMassAt
        hH3 hClass (hτ n) 14 j

    let B : ℝ :=
      h3TerminalForcingThirdQRawRadialSquareMassAt
        hH3 hClass (hτ n) 16 j

    let H : ℝ :=
      max A B

    let C : ℝ :=
      h3StandardInverseBesselWeightL2Factor

    let M : ℝ :=
      h3TerminalForcingThirdQMoment14MassAt
        hH3 hClass (hτ n) j

    have hA0 :
        0 ≤ A := by
      dsimp only [A]
      exact
        h3TerminalForcingThirdQRawRadialSquareMassAt_nonneg
          hH3 hClass (hτ n) 14 j

    have hB0 :
        0 ≤ B := by
      dsimp only [B]
      exact
        h3TerminalForcingThirdQRawRadialSquareMassAt_nonneg
          hH3 hClass (hτ n) 16 j

    have hH0 :
        0 ≤ H := by
      dsimp only [H]
      exact
        hA0.trans
          (le_max_left A B)

    have hC0 :
        0 ≤ C := by
      dsimp only [C]
      exact
        h3StandardInverseBesselWeightL2Factor_nonneg

    have hM0 :
        0 ≤ M := by
      dsimp only [M]
      exact
        h3TerminalForcingThirdQMoment14MassAt_nonneg
          hH3 hClass (hτ n) j

    have hAH :
        A ≤ H := by
      dsimp only [H]
      exact
        le_max_left A B

    have hBH :
        B ≤ H := by
      dsimp only [H]
      exact
        le_max_right A B

    have hSqrtA :
        Real.sqrt A ≤ Real.sqrt H :=
      Real.sqrt_le_sqrt
        hAH

    have hSqrtB :
        Real.sqrt B ≤ Real.sqrt H :=
      Real.sqrt_le_sqrt
        hBH

    have hSum :
        Real.sqrt A + Real.sqrt B
          ≤
        2 * Real.sqrt H := by
      linarith

    have hMomentBound :=
      h3TerminalForcingThirdQMoment14MassAt_le_bessel_radial14_16
        hH3 hClass (hτ n) j

    have hMomentLe :
        M
          ≤
        C * (2 * Real.sqrt H) := by

      have hScaled :
          C * (Real.sqrt A + Real.sqrt B)
            ≤
          C * (2 * Real.sqrt H) :=
        mul_le_mul_of_nonneg_left
          hSum
          hC0

      exact
        hMomentBound.trans
          hScaled

    have hPowLe :
        M ^ 4
          ≤
        (C * (2 * Real.sqrt H)) ^ 4 :=
      pow_le_pow_left₀
        hM0
        hMomentLe
        4

    have hScaledPow :
        K * M ^ 4
          ≤
        K * (C * (2 * Real.sqrt H)) ^ 4 :=
      mul_le_mul_of_nonneg_left
        hPowLe
        hK0

    have hRateRaw :
        rate n
          <
        K * (C * (2 * Real.sqrt H)) ^ 4 :=
      (hRate n).trans_le
        hScaledPow

    simpa only [
      C,
      H,
      A,
      B,
      hChosen n
    ] using
      hRateRaw

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q₀ : Fin 2,
          channel n = q₀ :=
    Frequently.of_forall
      (
        fun n =>
          ⟨
            channel n,
            rfl
          ⟩
      )

  obtain
    ⟨q₀, hFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySome

  obtain
    ⟨s, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop
      hFrequently

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

  have hRateFixed :
      ∀ n : ℕ,
        rate (s n)
          <
        K
          *
        (
          h3StandardInverseBesselWeightL2Factor
            *
          (
            2
              *
            Real.sqrt
              (
                h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                  hH3 hClass (hτ (s n)) j q₀
              )
          )
        ) ^ 4 := by

    intro n

    have hRaw :=
      hRateChosen
        (s n)

    rw [hFixed n] at hRaw

    exact
      hRaw

  have hTopBefore :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMoment14RadialSquareChannelAt
              hH3 hClass
              (hτ (s n))
              j
              (channel (s n))
        )
        atTop
        atTop :=
    hChosenTop.comp
      hsTop

  have hTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMoment14RadialSquareChannelAt
              hH3 hClass
              (hτ (s n))
              j
              q₀
        )
        atTop
        atTop := by

    simpa only [hFixed] using
      hTopBefore

  have hHigherTop :=
    h3TerminalForcingThirdQMoment14RadialSquareChannel_escape_resolves_higherRadial
      hH3
      hClass
      j
      q₀
      (fun n : ℕ => τ (s n))
      (fun n : ℕ => hτ (s n))
      hTop

  exact
    ⟨
      q₀,
      s,
      hMono,
      hTauSub,
      hRateFixed,
      hTop,
      hHigherTop
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

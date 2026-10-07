import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.Closure

/-!
# Quantitative second-q moment-six split

The second-q moment-six mass satisfies

    M6 ≤ L1 + M10 ≤ 2 * max(L1, M10).

Thus any lower rate carried by `M6^4` transfers to the fourth power of one
fixed resolver after a finite extraction.  The raw-L1 branch additionally
forces physical H3-energy escape on that same refined terminal sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1400000

theorem h3TerminalSecondQVelocityMoment6_rate_split_rawL1_or_velocityMoment10
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
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
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
            hH3 hClass (hτ n) i
        ) ^ 4)
    (hMomentTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
              hH3 hClass (hτ n) i
        )
        atTop
        atTop) :
    (
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
              2
                *
              h3TerminalForcingThirdQRawL1MassAt
                hH3 hClass (hτ (s n)) i
            ) ^ 4
        )
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQRawL1MassAt
                hH3 hClass (hτ (s n)) i
          )
          atTop
          atTop
          ∧
        Tendsto
          (
            fun n : ℕ =>
              velocityH3EnergyAt u (τ (s n))
          )
          atTop
          atTop
    )
      ∨
    (
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
              2
                *
              h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
                hH3 hClass (hτ (s n)) i
            ) ^ 4
        )
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
                hH3 hClass (hτ (s n)) i
          )
          atTop
          atTop
    ) := by

  classical

  let channel : ℕ → Fin 2 :=
    fun n =>
      if
        h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i
          ≤
        h3TerminalForcingThirdQRawL1MassAt
          hH3 hClass (hτ n) i
      then 0
      else 1

  have hChosen :
      ∀ n : ℕ,
        h3TerminalSecondQVelocityMoment6ResolverAt
            hH3 hClass (hτ n) i (channel n)
          =
        max
          (
            h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass (hτ n) i
          )
          (
            h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
              hH3 hClass (hτ n) i
          ) := by

    intro n
    dsimp only [channel]

    by_cases h :
        h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i
          ≤
        h3TerminalForcingThirdQRawL1MassAt
          hH3 hClass (hτ n) i

    · simp only [if_pos h]
      unfold h3TerminalSecondQVelocityMoment6ResolverAt
      simp only [if_pos]
      exact
        (max_eq_left h).symm

    · simp only [if_neg h]

      have hReverse :
          h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass (hτ n) i
            ≤
          h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i :=
        le_of_lt
          (lt_of_not_ge h)

      unfold h3TerminalSecondQVelocityMoment6ResolverAt
      simp only [one_ne_zero]

      exact
        (max_eq_right hReverse).symm

  have hMaxTop :
      Tendsto
        (
          fun n : ℕ =>
            max
              (
                h3TerminalForcingThirdQRawL1MassAt
                  hH3 hClass (hτ n) i
              )
              (
                h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
                  hH3 hClass (hτ n) i
              )
        )
        atTop
        atTop := by

    refine tendsto_atTop.2 ?_
    intro M

    let R : ℝ := max M 0

    have hMLe :
        M ≤ R := by
      dsimp only [R]
      exact
        le_max_left M 0

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          2 * R + 1
            <
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
            hH3 hClass (hτ n) i :=
      hMomentTop.eventually
        (eventually_gt_atTop (2 * R + 1))

    filter_upwards [hLarge] with n hn

    let A : ℝ :=
      h3TerminalForcingThirdQRawL1MassAt
        hH3 hClass (hτ n) i

    let B : ℝ :=
      h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
        hH3 hClass (hτ n) i

    let H : ℝ :=
      max A B

    have hAH :
        A ≤ H := by
      dsimp only [H]
      exact le_max_left A B

    have hBH :
        B ≤ H := by
      dsimp only [H]
      exact le_max_right A B

    have hBound :=
      h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt_le_rawL1_add_moment10
        hH3 hClass (hτ n) i

    have hRLtH :
        R < H := by

      by_contra hNot

      have hHLe :
          H ≤ R :=
        le_of_not_gt hNot

      have hALe :
          A ≤ R :=
        hAH.trans hHLe

      have hBLe :
          B ≤ R :=
        hBH.trans hHLe

      have hSum :
          A + B ≤ 2 * R := by
        linarith

      have hMomentLe :
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
              hH3 hClass (hτ n) i
            ≤
          2 * R := by
        dsimp only [A, B] at hBound hSum
        exact
          hBound.trans
            hSum

      linarith

    change
      M
        ≤
      max
        (
          h3TerminalForcingThirdQRawL1MassAt
            hH3 hClass (hτ n) i
        )
        (
          h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i
        )

    exact
      hMLe.trans
        (le_of_lt hRLtH)

  have hChosenTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalSecondQVelocityMoment6ResolverAt
              hH3 hClass (hτ n) i (channel n)
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
          2
            *
          h3TerminalSecondQVelocityMoment6ResolverAt
            hH3 hClass (hτ n) i (channel n)
        ) ^ 4 := by

    intro n

    let M6 : ℝ :=
      h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
        hH3 hClass (hτ n) i

    let A : ℝ :=
      h3TerminalForcingThirdQRawL1MassAt
        hH3 hClass (hτ n) i

    let B : ℝ :=
      h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
        hH3 hClass (hτ n) i

    let H : ℝ :=
      max A B

    have hM60 :
        0 ≤ M6 := by
      dsimp only [M6]
      unfold
        h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
      dsimp only
      exact
        h3SpectralScalarRawFourierMomentMass_nonneg
          (6 : ℝ) _

    have hA0 :
        0 ≤ A := by
      dsimp only [A]
      exact
        h3TerminalForcingThirdQRawL1MassAt_nonneg
          hH3 hClass (hτ n) i

    have hH0 :
        0 ≤ H := by
      exact
        hA0.trans
          (by
            dsimp only [H]
            exact le_max_left A B)

    have hAH :
        A ≤ H := by
      dsimp only [H]
      exact le_max_left A B

    have hBH :
        B ≤ H := by
      dsimp only [H]
      exact le_max_right A B

    have hBound :=
      h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt_le_rawL1_add_moment10
        hH3 hClass (hτ n) i

    have hSum :
        A + B ≤ 2 * H := by
      linarith

    have hM6Le :
        M6 ≤ 2 * H := by
      exact
        hBound.trans
          hSum

    have hRight0 :
        0 ≤ 2 * H :=
      mul_nonneg
        (by norm_num)
        hH0

    have hPowLe :
        M6 ^ 4
          ≤
        (2 * H) ^ 4 :=
      pow_le_pow_left₀
        hM60
        hM6Le
        4

    have hScaled :
        K * M6 ^ 4
          ≤
        K * (2 * H) ^ 4 :=
      mul_le_mul_of_nonneg_left
        hPowLe
        hK0

    have hRaw :
        rate n
          <
        K * (2 * H) ^ 4 :=
      (hRate n).trans_le
        hScaled

    simpa only [
      H,
      A,
      B,
      hChosen n
    ] using
      hRaw

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q₀ : Fin 2,
          channel n = q₀ :=
    Frequently.of_forall
      (fun n => ⟨channel n, rfl⟩)

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
          2
            *
          h3TerminalSecondQVelocityMoment6ResolverAt
            hH3 hClass (hτ (s n)) i q₀
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
            h3TerminalSecondQVelocityMoment6ResolverAt
              hH3 hClass
              (hτ (s n))
              i
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
            h3TerminalSecondQVelocityMoment6ResolverAt
              hH3 hClass
              (hτ (s n))
              i
              q₀
        )
        atTop
        atTop := by

    simpa only [hFixed] using
      hTopBefore

  fin_cases q₀

  · have hL1Top :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQRawL1MassAt
                hH3 hClass (hτ (s n)) i
          )
          atTop
          atTop := by

      simpa [
        h3TerminalSecondQVelocityMoment6ResolverAt
      ] using
        hTop

    have hEnergyTop :=
      velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
        hH3
        hClass
        i
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hL1Top

    exact
      Or.inl
        ⟨
          s,
          hMono,
          hTauSub,
          by
            intro n
            simpa [
              h3TerminalSecondQVelocityMoment6ResolverAt
            ] using
              hRateFixed n,
          hL1Top,
          hEnergyTop
        ⟩

  · have hM10Top :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
                hH3 hClass (hτ (s n)) i
          )
          atTop
          atTop := by

      simpa [
        h3TerminalSecondQVelocityMoment6ResolverAt
      ] using
        hTop

    exact
      Or.inr
        ⟨
          s,
          hMono,
          hTauSub,
          by
            intro n
            simpa [
              h3TerminalSecondQVelocityMoment6ResolverAt
            ] using
              hRateFixed n,
          hM10Top
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor

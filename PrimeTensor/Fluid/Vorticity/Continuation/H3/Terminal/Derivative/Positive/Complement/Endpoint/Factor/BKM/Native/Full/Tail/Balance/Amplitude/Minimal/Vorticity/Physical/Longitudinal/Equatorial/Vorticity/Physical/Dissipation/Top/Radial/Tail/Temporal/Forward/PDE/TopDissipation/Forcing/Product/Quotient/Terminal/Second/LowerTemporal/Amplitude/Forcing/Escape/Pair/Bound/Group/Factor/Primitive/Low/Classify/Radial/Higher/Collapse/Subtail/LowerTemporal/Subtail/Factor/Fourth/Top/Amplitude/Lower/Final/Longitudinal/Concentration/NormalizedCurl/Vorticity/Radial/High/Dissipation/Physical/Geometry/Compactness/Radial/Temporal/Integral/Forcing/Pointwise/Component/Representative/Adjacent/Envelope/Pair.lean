import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.SecondQ.Escape

/-!
# Freeze a canonical radial product pair

The canonical adjacent-q envelope branch carries the reciprocal-width rate

    δ / (12 Δt_n) < E_q(n)^2

for one fixed `q ∈ {2,4}`.

At each strict time the named Leray envelope is bounded by one universal
positive coefficient times one of the nine radial product-convolution norms.
A finite extraction freezes that pair while preserving the canonical lineage.

The result is neutral: either an order-three product norm (second-q branch) or
an order-five product norm (fourth-q branch) carries the rate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalPhysicalTopDissipationFixedForcingRadialProductPairCanonicalRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ j₀ : Fin 3,
      ∃ m q φ ψ : ℕ → ℕ,
        Tendsto m atTop atTop
          ∧
        Tendsto q atTop atTop
          ∧
        StrictMono φ
          ∧
        StrictMono ψ
          ∧
        ∃ s r : ℕ → ℝ,
          ∃ hs :
            ∀ n : ℕ,
              s n ∈ Set.Ioo a T,
            ∃ hσ :
              ∀ n : ℕ,
                σ n ∈ Set.Ioo a T,
              ∃ hr :
                ∀ n : ℕ,
                  r (φ (ψ n)) ∈ Set.Ioo a T,
                Tendsto
                    (fun n : ℕ => s (φ (ψ n)))
                    atTop
                    (𝓝 T)
                  ∧
                Tendsto
                    (fun n : ℕ => σ (m (q (φ (ψ n)))))
                    atTop
                    (𝓝 T)
                  ∧
                (
                  ∀ n : ℕ,
                    s (φ (ψ n))
                      <
                    σ (m (q (φ (ψ n))))
                )
                  ∧
                (
                  ∀ n : ℕ,
                    r (φ (ψ n)) ∈
                      Set.Icc
                        (s (φ (ψ n)))
                        (σ (m (q (φ (ψ n)))))
                )
                  ∧
                Tendsto
                    (fun n : ℕ => r (φ (ψ n)))
                    atTop
                    (𝓝 T)
                  ∧
                (
                  (
                    ∃ k₀ l₀ : Fin 3,
                      ∃ χ : ℕ → ℕ,
                        StrictMono χ
                          ∧
                        Tendsto
                            (fun n : ℕ =>
                              s (φ (ψ (χ n))))
                            atTop
                            (𝓝 T)
                          ∧
                        Tendsto
                            (fun n : ℕ =>
                              σ (m (q (φ (ψ (χ n))))))
                            atTop
                            (𝓝 T)
                          ∧
                        Tendsto
                            (fun n : ℕ =>
                              r (φ (ψ (χ n))))
                            atTop
                            (𝓝 T)
                          ∧
                        (
                          ∀ n : ℕ,
                            δ
                                /
                              (
                                12
                                  *
                                (
                                  σ (m (q (φ (ψ (χ n)))))
                                    -
                                  s (φ (ψ (χ n)))
                                )
                              )
                              <
                            (
                              h3TerminalForcingSecondQFixedPairCoefficient
                                *
                              h3TerminalForcingSecondQRadialProductNormAt
                                hH3 hClass (hr (χ n)) k₀ l₀
                            ) ^ 2
                        )
                          ∧
                        Tendsto
                          (
                            fun n : ℕ =>
                              h3TerminalForcingSecondQRadialProductNormAt
                                hH3 hClass (hr (χ n)) k₀ l₀
                          )
                          atTop
                          atTop
                  )
                    ∨
                  (
                    ∃ k₀ l₀ : Fin 3,
                      ∃ χ : ℕ → ℕ,
                        StrictMono χ
                          ∧
                        Tendsto
                            (fun n : ℕ =>
                              s (φ (ψ (χ n))))
                            atTop
                            (𝓝 T)
                          ∧
                        Tendsto
                            (fun n : ℕ =>
                              σ (m (q (φ (ψ (χ n))))))
                            atTop
                            (𝓝 T)
                          ∧
                        Tendsto
                            (fun n : ℕ =>
                              r (φ (ψ (χ n))))
                            atTop
                            (𝓝 T)
                          ∧
                        (
                          ∀ n : ℕ,
                            δ
                                /
                              (
                                12
                                  *
                                (
                                  σ (m (q (φ (ψ (χ n)))))
                                    -
                                  s (φ (ψ (χ n)))
                                )
                              )
                              <
                            (
                              h3TerminalForcingFourthQFixedPairCoefficient
                                *
                              h3TerminalForcingFourthQRadialProductNormAt
                                hH3 hClass (hr (χ n)) k₀ l₀
                            ) ^ 2
                        )
                          ∧
                        Tendsto
                          (
                            fun n : ℕ =>
                              h3TerminalForcingFourthQRadialProductNormAt
                                hH3 hClass (hr (χ n)) k₀ l₀
                          )
                          atTop
                          atTop
                  )
                )

theorem fixedForcingRadialProductPairCanonicalRateEscapeSubsequenceOf_of_adjacentQEnvelopeCanonicalRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hEnvelope :
      H3TerminalPhysicalTopDissipationFixedThirdRadialForcingAdjacentQEnvelopeCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationFixedForcingRadialProductPairCanonicalRateEscapeSubsequenceOf
      hH3 hClass σ := by

  classical

  obtain
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      ψ,
      hmTop,
      hqTop,
      hPhiMono,
      hPsiMono,
      s,
      r,
      hs,
      hσ,
      hr,
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      hBranch
    ⟩ :=
    hEnvelope

  refine
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      ψ,
      hmTop,
      hqTop,
      hPhiMono,
      hPsiMono,
      s,
      r,
      hs,
      hσ,
      hr,
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      ?_
    ⟩

  rcases hBranch with hSecond | hFourth

  · left

    have hChoice :
        ∀ n : ℕ,
          ∃ p : Fin 3 × Fin 3,
            h3TerminalForcingSecondQRadialLerayEnvelopeAt
                hH3 hClass (hr n) j₀
              ≤
            h3TerminalForcingSecondQFixedPairCoefficient
              *
            h3TerminalForcingSecondQRadialProductNormAt
              hH3 hClass (hr n) p.1 p.2 := by

      intro n

      obtain
        ⟨k, l, hkl⟩ :=
        exists_pair_h3TerminalForcingSecondQRadialLerayEnvelopeAt_le_fixedCoefficient_mul_productNorm
          hH3 hClass (hr n) j₀

      exact
        ⟨
          (k, l),
          hkl
        ⟩

    choose p hp using hChoice

    have hCoeffPos :
        0 < h3TerminalForcingSecondQFixedPairCoefficient :=
      h3TerminalForcingSecondQFixedPairCoefficient_pos

    have hChosenRate :
        ∀ n : ℕ,
          δ
              /
            (
              12
                *
              (
                σ (m (q (φ (ψ n))))
                  -
                s (φ (ψ n))
              )
            )
            <
          (
            h3TerminalForcingSecondQFixedPairCoefficient
              *
            h3TerminalForcingSecondQRadialProductNormAt
              hH3 hClass (hr n) (p n).1 (p n).2
          ) ^ 2 := by

      intro n

      have hEnvelopeNonneg :=
        h3TerminalForcingSecondQRadialLerayEnvelopeAt_nonneg
          hH3 hClass (hr n) j₀

      have hProductNonneg :=
        h3TerminalForcingSecondQRadialProductNormAt_nonneg
          hH3 hClass (hr n) (p n).1 (p n).2

      have hScaledNonneg :
          0
            ≤
          h3TerminalForcingSecondQFixedPairCoefficient
            *
          h3TerminalForcingSecondQRadialProductNormAt
            hH3 hClass (hr n) (p n).1 (p n).2 :=
        mul_nonneg
          hCoeffPos.le
          hProductNonneg

      have hSqLe :
          (
            h3TerminalForcingSecondQRadialLerayEnvelopeAt
              hH3 hClass (hr n) j₀
          ) ^ 2
            ≤
          (
            h3TerminalForcingSecondQFixedPairCoefficient
              *
            h3TerminalForcingSecondQRadialProductNormAt
              hH3 hClass (hr n) (p n).1 (p n).2
          ) ^ 2 :=
        (
          sq_le_sq₀
            hEnvelopeNonneg
            hScaledNonneg
        ).2
          (hp n)

      exact
        (hSecond.1 n).trans_le
          hSqLe

    have hChosenTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingSecondQRadialProductNormAt
                hH3 hClass (hr n) (p n).1 (p n).2
          )
          atTop
          atTop := by

      refine
        tendsto_atTop.2
          ?_

      intro M

      let R : ℝ :=
        max M 0

      have hMLe :
          M ≤ R := by
        dsimp only [R]
        exact le_max_left M 0

      have hLarge :
          ∀ᶠ n : ℕ in atTop,
            h3TerminalForcingSecondQFixedPairCoefficient * R
              <
            h3TerminalForcingSecondQRadialLerayEnvelopeAt
              hH3 hClass (hr n) j₀ :=
        hSecond.2.eventually
          (
            eventually_gt_atTop
              (
                h3TerminalForcingSecondQFixedPairCoefficient * R
              )
          )

      filter_upwards [hLarge] with n hn

      have hScaled :
          h3TerminalForcingSecondQFixedPairCoefficient * R
            <
          h3TerminalForcingSecondQFixedPairCoefficient
            *
          h3TerminalForcingSecondQRadialProductNormAt
            hH3 hClass (hr n) (p n).1 (p n).2 :=
        lt_of_lt_of_le
          hn
          (hp n)

      have hRLt :
          R
            <
          h3TerminalForcingSecondQRadialProductNormAt
            hH3 hClass (hr n) (p n).1 (p n).2 := by

        exact
          lt_of_mul_lt_mul_left
            hScaled
            hCoeffPos.le

      exact
        hMLe.trans
          (le_of_lt hRLt)

    have hFrequentlySome :
        ∃ᶠ n : ℕ in atTop,
          ∃ p₀ : Fin 3 × Fin 3,
            p n = p₀ :=
      Frequently.of_forall
        (
          fun n =>
            ⟨
              p n,
              rfl
            ⟩
        )

    obtain
      ⟨p₀, hFrequently⟩ :=
      (Filter.frequently_exists).1
        hFrequentlySome

    obtain
      ⟨χ, hChiMono, hFixed⟩ :=
      extraction_of_frequently_atTop
        hFrequently

    have hChiTop :
        Tendsto χ atTop atTop :=
      hChiMono.tendsto_atTop

    have hRateFixed :
        ∀ n : ℕ,
          δ
              /
            (
              12
                *
              (
                σ (m (q (φ (ψ (χ n)))))
                  -
                s (φ (ψ (χ n)))
              )
            )
            <
          (
            h3TerminalForcingSecondQFixedPairCoefficient
              *
            h3TerminalForcingSecondQRadialProductNormAt
              hH3 hClass (hr (χ n)) p₀.1 p₀.2
          ) ^ 2 := by

      intro n

      have hRaw :=
        hChosenRate
          (χ n)

      rw [
        hFixed n
      ] at hRaw

      exact
        hRaw

    have hPairTopBeforeRewrite :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingSecondQRadialProductNormAt
                hH3 hClass
                (hr (χ n))
                (p (χ n)).1
                (p (χ n)).2
          )
          atTop
          atTop :=
      hChosenTop.comp
        hChiTop

    have hPairTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingSecondQRadialProductNormAt
                hH3 hClass
                (hr (χ n))
                p₀.1
                p₀.2
          )
          atTop
          atTop := by

      simpa only [hFixed] using
        hPairTopBeforeRewrite

    exact
      ⟨
        p₀.1,
        p₀.2,
        χ,
        hChiMono,
        hsTendsto.comp hChiTop,
        hSigmaTendsto.comp hChiTop,
        hrTendsto.comp hChiTop,
        hRateFixed,
        hPairTop
      ⟩

  · right

    have hChoice :
        ∀ n : ℕ,
          ∃ p : Fin 3 × Fin 3,
            h3TerminalForcingFourthQRadialLerayEnvelopeAt
                hH3 hClass (hr n) j₀
              ≤
            h3TerminalForcingFourthQFixedPairCoefficient
              *
            h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass (hr n) p.1 p.2 := by

      intro n

      obtain
        ⟨k, l, hkl⟩ :=
        exists_pair_h3TerminalForcingFourthQRadialLerayEnvelopeAt_le_fixedCoefficient_mul_productNorm
          hH3 hClass (hr n) j₀

      exact
        ⟨
          (k, l),
          hkl
        ⟩

    choose p hp using hChoice

    have hCoeffPos :
        0 < h3TerminalForcingFourthQFixedPairCoefficient :=
      h3TerminalForcingFourthQFixedPairCoefficient_pos

    have hChosenRate :
        ∀ n : ℕ,
          δ
              /
            (
              12
                *
              (
                σ (m (q (φ (ψ n))))
                  -
                s (φ (ψ n))
              )
            )
            <
          (
            h3TerminalForcingFourthQFixedPairCoefficient
              *
            h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass (hr n) (p n).1 (p n).2
          ) ^ 2 := by

      intro n

      have hEnvelopeNonneg :=
        h3TerminalForcingFourthQRadialLerayEnvelopeAt_nonneg
          hH3 hClass (hr n) j₀

      have hProductNonneg :=
        h3TerminalForcingFourthQRadialProductNormAt_nonneg
          hH3 hClass (hr n) (p n).1 (p n).2

      have hScaledNonneg :
          0
            ≤
          h3TerminalForcingFourthQFixedPairCoefficient
            *
          h3TerminalForcingFourthQRadialProductNormAt
            hH3 hClass (hr n) (p n).1 (p n).2 :=
        mul_nonneg
          hCoeffPos.le
          hProductNonneg

      have hSqLe :
          (
            h3TerminalForcingFourthQRadialLerayEnvelopeAt
              hH3 hClass (hr n) j₀
          ) ^ 2
            ≤
          (
            h3TerminalForcingFourthQFixedPairCoefficient
              *
            h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass (hr n) (p n).1 (p n).2
          ) ^ 2 :=
        (
          sq_le_sq₀
            hEnvelopeNonneg
            hScaledNonneg
        ).2
          (hp n)

      exact
        (hFourth.1 n).trans_le
          hSqLe

    have hChosenTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingFourthQRadialProductNormAt
                hH3 hClass (hr n) (p n).1 (p n).2
          )
          atTop
          atTop := by

      refine
        tendsto_atTop.2
          ?_

      intro M

      let R : ℝ :=
        max M 0

      have hMLe :
          M ≤ R := by
        dsimp only [R]
        exact le_max_left M 0

      have hLarge :
          ∀ᶠ n : ℕ in atTop,
            h3TerminalForcingFourthQFixedPairCoefficient * R
              <
            h3TerminalForcingFourthQRadialLerayEnvelopeAt
              hH3 hClass (hr n) j₀ :=
        hFourth.2.eventually
          (
            eventually_gt_atTop
              (
                h3TerminalForcingFourthQFixedPairCoefficient * R
              )
          )

      filter_upwards [hLarge] with n hn

      have hScaled :
          h3TerminalForcingFourthQFixedPairCoefficient * R
            <
          h3TerminalForcingFourthQFixedPairCoefficient
            *
          h3TerminalForcingFourthQRadialProductNormAt
            hH3 hClass (hr n) (p n).1 (p n).2 :=
        lt_of_lt_of_le
          hn
          (hp n)

      have hRLt :
          R
            <
          h3TerminalForcingFourthQRadialProductNormAt
            hH3 hClass (hr n) (p n).1 (p n).2 := by

        by_contra hNot

        have hReverse :
            h3TerminalForcingFourthQRadialProductNormAt
                hH3 hClass (hr n) (p n).1 (p n).2
              ≤
            R :=
          le_of_not_gt
            hNot

        have hScaledReverse :
            h3TerminalForcingFourthQFixedPairCoefficient
                *
              h3TerminalForcingFourthQRadialProductNormAt
                hH3 hClass (hr n) (p n).1 (p n).2
              ≤
            h3TerminalForcingFourthQFixedPairCoefficient * R :=
          mul_le_mul_of_nonneg_left
            hReverse
            hCoeffPos.le

        exact
          (not_lt_of_ge hScaledReverse)
            hScaled

      exact
        hMLe.trans
          (le_of_lt hRLt)

    have hFrequentlySome :
        ∃ᶠ n : ℕ in atTop,
          ∃ p₀ : Fin 3 × Fin 3,
            p n = p₀ :=
      Frequently.of_forall
        (
          fun n =>
            ⟨
              p n,
              rfl
            ⟩
        )

    obtain
      ⟨p₀, hFrequently⟩ :=
      (Filter.frequently_exists).1
        hFrequentlySome

    obtain
      ⟨χ, hChiMono, hFixed⟩ :=
      extraction_of_frequently_atTop
        hFrequently

    have hChiTop :
        Tendsto χ atTop atTop :=
      hChiMono.tendsto_atTop

    have hRateFixed :
        ∀ n : ℕ,
          δ
              /
            (
              12
                *
              (
                σ (m (q (φ (ψ (χ n)))))
                  -
                s (φ (ψ (χ n)))
              )
            )
            <
          (
            h3TerminalForcingFourthQFixedPairCoefficient
              *
            h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass (hr (χ n)) p₀.1 p₀.2
          ) ^ 2 := by

      intro n

      have hRaw :=
        hChosenRate
          (χ n)

      rw [
        hFixed n
      ] at hRaw

      exact
        hRaw

    have hPairTopBeforeRewrite :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingFourthQRadialProductNormAt
                hH3 hClass
                (hr (χ n))
                (p (χ n)).1
                (p (χ n)).2
          )
          atTop
          atTop :=
      hChosenTop.comp
        hChiTop

    have hPairTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingFourthQRadialProductNormAt
                hH3 hClass
                (hr (χ n))
                p₀.1
                p₀.2
          )
          atTop
          atTop := by

      simpa only [hFixed] using
        hPairTopBeforeRewrite

    exact
      ⟨
        p₀.1,
        p₀.2,
        χ,
        hChiMono,
        hsTendsto.comp hChiTop,
        hSigmaTendsto.comp hChiTop,
        hrTendsto.comp hChiTop,
        hRateFixed,
        hPairTop
      ⟩

theorem exists_fixed_terminalSequence_with_canonicalForcingRadialProductPairRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          SmoothContinuationExtension u v T)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
        )
        atTop
        (𝓝 0)
        ∧
      ∃ σ : ℕ → ℝ,
        ∃ hσ :
          ∀ n : ℕ,
            σ n ∈ Set.Ioo a T,
          Tendsto σ atTop (𝓝 T)
            ∧
          (
            ∀ n : ℕ,
              ENNReal.ofReal (ε ^ 2 / 64)
                <
              16 *
                h3TerminalPhysicalDissipationBadConeHighRadialMass
                  hH3
                  i
                  ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                  1
                  (σ n)
                  ⟨
                    lt_trans hClass.terminal_start.1
                      (hσ n).1,
                    (hσ n).2
                  ⟩
          )
            ∧
          H3TerminalPhysicalTopDissipationFixedForcingRadialProductPairCanonicalRateEscapeSubsequenceOf
            hH3 hClass σ := by

  obtain
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hEnvelope
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalAdjacentQEnvelopeRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hPair :
      H3TerminalPhysicalTopDissipationFixedForcingRadialProductPairCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ :=
    fixedForcingRadialProductPairCanonicalRateEscapeSubsequenceOf_of_adjacentQEnvelopeCanonicalRateEscapeSubsequenceOf
      hH3
      hClass
      σ
      hEnvelope

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hPair
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

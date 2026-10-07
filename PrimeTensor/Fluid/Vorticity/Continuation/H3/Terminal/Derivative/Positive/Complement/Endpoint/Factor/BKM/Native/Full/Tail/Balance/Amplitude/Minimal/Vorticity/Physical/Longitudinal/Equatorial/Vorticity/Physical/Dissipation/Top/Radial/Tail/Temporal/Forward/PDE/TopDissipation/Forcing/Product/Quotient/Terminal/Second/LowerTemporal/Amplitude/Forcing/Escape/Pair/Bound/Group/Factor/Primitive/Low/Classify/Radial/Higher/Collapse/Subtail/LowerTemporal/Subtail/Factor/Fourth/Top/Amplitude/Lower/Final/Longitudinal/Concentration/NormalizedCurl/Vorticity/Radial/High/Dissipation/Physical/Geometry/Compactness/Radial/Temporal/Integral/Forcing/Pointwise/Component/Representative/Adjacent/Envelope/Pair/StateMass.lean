import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.SecondQ.Escape.StateMass

/-!
# Canonical fixed-product state-mass rate

The canonical product-pair checkpoint carries a reciprocal-width lower bound
for one fixed order-three or order-five radial product norm.  The Young
convolution estimate bounds the square of that product norm by an explicit
state-mass envelope.  Therefore the same canonical rate transfers directly to
the state-mass level without another extraction.

The two adjacent-q branches remain explicit and neutral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

def H3TerminalPhysicalTopDissipationFixedForcingProductStateMassCanonicalRateEscapeSubsequenceOf
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
                            ) ^ 2
                              *
                            h3TerminalForcingSecondQStateMassEnvelopeAt
                              hH3 hClass (hr (χ n)) k₀ l₀
                        )
                          ∧
                        Tendsto
                          (
                            fun n : ℕ =>
                              h3TerminalForcingSecondQStateMassEnvelopeAt
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
                            ) ^ 2
                              *
                            h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
                              hH3 hClass (hr (χ n)) k₀ l₀
                        )
                          ∧
                        Tendsto
                          (
                            fun n : ℕ =>
                              h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
                                hH3 hClass (hr (χ n)) k₀ l₀
                          )
                          atTop
                          atTop
                  )
                )

theorem fixedForcingProductStateMassCanonicalRateEscapeSubsequenceOf_of_productPairCanonicalRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hPair :
      H3TerminalPhysicalTopDissipationFixedForcingRadialProductPairCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationFixedForcingProductStateMassCanonicalRateEscapeSubsequenceOf
      hH3 hClass σ := by

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
    hPair

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

  · rcases hSecond with
      ⟨
        k₀,
        l₀,
        χ,
        hChiMono,
        hsChi,
        hSigmaChi,
        hrChi,
        hRate,
        hNormTop
      ⟩

    left

    refine
      ⟨
        k₀,
        l₀,
        χ,
        hChiMono,
        hsChi,
        hSigmaChi,
        hrChi,
        ?_,
        ?_
      ⟩

    · intro n

      have hState :=
        sq_h3TerminalForcingSecondQRadialProductNormAt_le_stateMassEnvelope
          hH3 hClass (hr (χ n)) k₀ l₀

      have hCoeffSqNonneg :
          0 ≤
            (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2 :=
        sq_nonneg _

      calc
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
          ) ^ 2 :=
          hRate n

        _ =
          (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
            *
          (
            h3TerminalForcingSecondQRadialProductNormAt
              hH3 hClass (hr (χ n)) k₀ l₀
          ) ^ 2 := by
            ring

        _ ≤
          (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
            *
          h3TerminalForcingSecondQStateMassEnvelopeAt
            hH3 hClass (hr (χ n)) k₀ l₀ :=
          mul_le_mul_of_nonneg_left
            hState
            hCoeffSqNonneg

    · exact
        h3TerminalForcingSecondQStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
          hH3
          hClass
          k₀
          l₀
          (fun n : ℕ => r (φ (ψ (χ n))))
          (fun n : ℕ => hr (χ n))
          hNormTop

  · rcases hFourth with
      ⟨
        k₀,
        l₀,
        χ,
        hChiMono,
        hsChi,
        hSigmaChi,
        hrChi,
        hRate,
        hNormTop
      ⟩

    right

    refine
      ⟨
        k₀,
        l₀,
        χ,
        hChiMono,
        hsChi,
        hSigmaChi,
        hrChi,
        ?_,
        ?_
      ⟩

    · intro n

      have hState :=
        sq_h3TerminalForcingFourthQRadialProductNormAt_le_stateMassEnvelope
          hH3 hClass (hr (χ n)) k₀ l₀

      have hCoeffSqNonneg :
          0 ≤
            (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2 :=
        sq_nonneg _

      calc
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
          ) ^ 2 :=
          hRate n

        _ =
          (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
            *
          (
            h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass (hr (χ n)) k₀ l₀
          ) ^ 2 := by
            ring

        _ ≤
          (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
            *
          h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
            hH3 hClass (hr (χ n)) k₀ l₀ :=
          mul_le_mul_of_nonneg_left
            hState
            hCoeffSqNonneg

    · exact
        h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
          hH3
          hClass
          k₀
          l₀
          (fun n : ℕ => r (φ (ψ (χ n))))
          (fun n : ℕ => hr (χ n))
          hNormTop

theorem exists_fixed_terminalSequence_with_canonicalForcingProductStateMassRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalTopDissipationFixedForcingProductStateMassCanonicalRateEscapeSubsequenceOf
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
      hPair
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalForcingRadialProductPairRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hState :
      H3TerminalPhysicalTopDissipationFixedForcingProductStateMassCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ :=
    fixedForcingProductStateMassCanonicalRateEscapeSubsequenceOf_of_productPairCanonicalRateEscapeSubsequenceOf
      hH3
      hClass
      σ
      hPair

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hState
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

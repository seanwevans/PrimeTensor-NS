import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.SecondQ.Escape.StateMass.Primitive
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive

/-!
# Canonical primitive forcing witness

The second-q state-mass branch already has a six-way primitive extraction.

The current fourth-q hierarchy is intentionally more structured: its state
envelope first resolves into a raw-L2 product or a moment/L1 mixture, and only
then into primitive masses.  This file follows that modular hierarchy rather
than importing the obsolete monolithic fourth-q primitive module.

On every final refinement we preserve the reciprocal-width lower bound at the
state-mass level and freeze an actual primitive mass which diverges on exactly
that refined canonical lineage.  A later layer may sharpen the inherited
state-mass rate onto the primitive itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalPhysicalTopDissipationFixedForcingPrimitiveWitnessCanonicalRateEscapeSubsequenceOf
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
                        ∃ q₀ : Fin 6,
                          ∃ ω : ℕ → ℕ,
                            Tendsto ω atTop atTop
                              ∧
                            Tendsto
                                (fun n : ℕ =>
                                  s (φ (ψ (χ (ω n)))))
                                atTop
                                (𝓝 T)
                              ∧
                            Tendsto
                                (fun n : ℕ =>
                                  σ (m (q (φ (ψ (χ (ω n)))))))
                                atTop
                                (𝓝 T)
                              ∧
                            Tendsto
                                (fun n : ℕ =>
                                  r (φ (ψ (χ (ω n)))))
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
                                      σ (m (q (φ (ψ (χ (ω n))))))
                                        -
                                      s (φ (ψ (χ (ω n))))
                                    )
                                  )
                                  <
                                (
                                  h3TerminalForcingSecondQFixedPairCoefficient
                                ) ^ 2
                                  *
                                h3TerminalForcingSecondQStateMassEnvelopeAt
                                  hH3 hClass
                                  (hr (χ (ω n)))
                                  k₀ l₀
                            )
                              ∧
                            Tendsto
                              (
                                fun n : ℕ =>
                                  h3TerminalForcingSecondQPrimitiveFactorAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    k₀ l₀ q₀
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
                        (
                          (
                            ∃ r₀ : Fin 2,
                              ∃ ω : ℕ → ℕ,
                                Tendsto ω atTop atTop
                                  ∧
                                Tendsto
                                    (fun n : ℕ =>
                                      s (φ (ψ (χ (ω n)))))
                                    atTop
                                    (𝓝 T)
                                  ∧
                                Tendsto
                                    (fun n : ℕ =>
                                      σ (m (q (φ (ψ (χ (ω n)))))))
                                    atTop
                                    (𝓝 T)
                                  ∧
                                Tendsto
                                    (fun n : ℕ =>
                                      r (φ (ψ (χ (ω n)))))
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
                                          σ (m (q (φ (ψ (χ (ω n))))))
                                            -
                                          s (φ (ψ (χ (ω n))))
                                        )
                                      )
                                      <
                                    (
                                      h3TerminalForcingFourthQFixedPairCoefficient
                                    ) ^ 2
                                      *
                                    h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
                                      hH3 hClass
                                      (hr (χ (ω n)))
                                      k₀ l₀
                                )
                                  ∧
                                Tendsto
                                  (
                                    fun n : ℕ =>
                                      h3TerminalForcingFourthQRawL2FactorAt
                                        hH3 hClass
                                        (hr (χ (ω n)))
                                        k₀ l₀ r₀
                                  )
                                  atTop
                                  atTop
                          )
                            ∨
                          (
                            ∃ r₀ q₀ : Fin 2,
                              ∃ ω : ℕ → ℕ,
                                Tendsto ω atTop atTop
                                  ∧
                                Tendsto
                                    (fun n : ℕ =>
                                      s (φ (ψ (χ (ω n)))))
                                    atTop
                                    (𝓝 T)
                                  ∧
                                Tendsto
                                    (fun n : ℕ =>
                                      σ (m (q (φ (ψ (χ (ω n)))))))
                                    atTop
                                    (𝓝 T)
                                  ∧
                                Tendsto
                                    (fun n : ℕ =>
                                      r (φ (ψ (χ (ω n)))))
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
                                          σ (m (q (φ (ψ (χ (ω n))))))
                                            -
                                          s (φ (ψ (χ (ω n))))
                                        )
                                      )
                                      <
                                    (
                                      h3TerminalForcingFourthQFixedPairCoefficient
                                    ) ^ 2
                                      *
                                    h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
                                      hH3 hClass
                                      (hr (χ (ω n)))
                                      k₀ l₀
                                )
                                  ∧
                                Tendsto
                                  (
                                    fun n : ℕ =>
                                      h3TerminalForcingFourthQMomentL1PrimitiveAt
                                        hH3 hClass
                                        (hr (χ (ω n)))
                                        k₀ l₀ r₀ q₀
                                  )
                                  atTop
                                  atTop
                          )
                        )
                  )
                )

theorem fixedForcingPrimitiveWitnessCanonicalRateEscapeSubsequenceOf_of_stateMassCanonicalRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hState :
      H3TerminalPhysicalTopDissipationFixedForcingProductStateMassCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationFixedForcingPrimitiveWitnessCanonicalRateEscapeSubsequenceOf
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
    hState

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
        hEnvelopeTop
      ⟩

    obtain
      ⟨q₀, ω, _hOmegaLe, hOmegaTop, _hrFinal, hPrimitiveTop⟩ :=
      exists_fixed_h3TerminalForcingSecondQPrimitiveFactor_subsequence_of_stateMassEnvelope_tendstoAtTop
        hH3
        hClass
        k₀
        l₀
        (fun n : ℕ => r (φ (ψ (χ n))))
        (fun n : ℕ => hr (χ n))
        hrChi
        hEnvelopeTop

    exact
      Or.inl
        ⟨
          k₀,
          l₀,
          χ,
          hChiMono,
          q₀,
          ω,
          hOmegaTop,
          hsChi.comp hOmegaTop,
          hSigmaChi.comp hOmegaTop,
          hrChi.comp hOmegaTop,
          (fun n => hRate (ω n)),
          hPrimitiveTop
        ⟩

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
        hEnvelopeTop
      ⟩

    obtain
      ⟨g, v, _hvLe, hvTop, hTauV, hGroupTop⟩ :=
      exists_fixed_h3TerminalForcingFourthQStateMassGroup_subsequence_of_envelope_tendstoAtTop
        hH3
        hClass
        k₀
        l₀
        (fun n : ℕ => r (φ (ψ (χ n))))
        (fun n : ℕ => hr (χ n))
        hrChi
        hEnvelopeTop

    rcases
      h3TerminalForcingFourthQStateMassGroup_escape_resolves_factor
        hH3
        hClass
        k₀
        l₀
        g
        (fun n : ℕ => r (φ (ψ (χ (v n)))))
        (fun n : ℕ => hr (χ (v n)))
        hTauV
        hGroupTop
    with
      hRaw
      |
      hMoment

    · rcases hRaw with
        ⟨r₀, w, _hwLe, hwTop, _hTauW, hFactorTop⟩

      let ω : ℕ → ℕ :=
        fun n => v (w n)

      have hOmegaTop :
          Tendsto ω atTop atTop := by
        dsimp only [ω]
        exact
          hvTop.comp
            hwTop

      exact
        Or.inr
          ⟨
            k₀,
            l₀,
            χ,
            hChiMono,
            Or.inl
              ⟨
                r₀,
                ω,
                hOmegaTop,
                hsChi.comp hOmegaTop,
                hSigmaChi.comp hOmegaTop,
                hrChi.comp hOmegaTop,
                (fun n => hRate (ω n)),
                hFactorTop
              ⟩
          ⟩

    · rcases hMoment with
        ⟨r₀, w, _hwLe, hwTop, hTauW, hProductTop⟩

      obtain
        ⟨q₀, z, _hzLe, hzTop, _hTauZ, hPrimitiveTop⟩ :=
        exists_fixed_h3TerminalForcingFourthQMomentL1Primitive_subsequence_of_product_tendstoAtTop
          hH3
          hClass
          k₀
          l₀
          r₀
          (fun n : ℕ => r (φ (ψ (χ (v (w n))))))
          (fun n : ℕ => hr (χ (v (w n))))
          hTauW
          hProductTop

      let ω : ℕ → ℕ :=
        fun n => v (w (z n))

      have hOmegaTop :
          Tendsto ω atTop atTop := by
        dsimp only [ω]
        exact
          hvTop.comp
            (hwTop.comp hzTop)

      exact
        Or.inr
          ⟨
            k₀,
            l₀,
            χ,
            hChiMono,
            Or.inr
              ⟨
                r₀,
                q₀,
                ω,
                hOmegaTop,
                hsChi.comp hOmegaTop,
                hSigmaChi.comp hOmegaTop,
                hrChi.comp hOmegaTop,
                (fun n => hRate (ω n)),
                hPrimitiveTop
              ⟩
          ⟩

theorem exists_fixed_terminalSequence_with_canonicalForcingPrimitiveWitnessRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalTopDissipationFixedForcingPrimitiveWitnessCanonicalRateEscapeSubsequenceOf
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
      hState
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalForcingProductStateMassRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hPrimitive :
      H3TerminalPhysicalTopDissipationFixedForcingPrimitiveWitnessCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ :=
    fixedForcingPrimitiveWitnessCanonicalRateEscapeSubsequenceOf_of_stateMassCanonicalRateEscapeSubsequenceOf
      hH3
      hClass
      σ
      hState

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hPrimitive
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

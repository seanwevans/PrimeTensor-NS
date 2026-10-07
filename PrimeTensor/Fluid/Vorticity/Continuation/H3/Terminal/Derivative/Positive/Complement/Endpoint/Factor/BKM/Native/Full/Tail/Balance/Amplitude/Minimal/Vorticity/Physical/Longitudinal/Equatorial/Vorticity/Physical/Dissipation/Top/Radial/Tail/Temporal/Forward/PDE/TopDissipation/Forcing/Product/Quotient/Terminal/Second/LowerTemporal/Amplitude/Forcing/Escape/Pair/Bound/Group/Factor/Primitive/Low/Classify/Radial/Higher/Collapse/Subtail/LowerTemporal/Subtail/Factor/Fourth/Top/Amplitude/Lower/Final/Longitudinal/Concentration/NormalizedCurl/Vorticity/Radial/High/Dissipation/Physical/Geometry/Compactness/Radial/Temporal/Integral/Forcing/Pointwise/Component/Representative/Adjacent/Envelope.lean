import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.SecondQ.Escape

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

def H3TerminalPhysicalTopDissipationFixedThirdRadialForcingAdjacentQEnvelopeCanonicalRateEscapeSubsequenceOf
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
                    (
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
                          h3TerminalForcingSecondQRadialLerayEnvelopeAt
                            hH3 hClass (hr n) j₀
                        ) ^ 2
                    )
                      ∧
                    Tendsto
                      (
                        fun n : ℕ =>
                          h3TerminalForcingSecondQRadialLerayEnvelopeAt
                            hH3 hClass (hr n) j₀
                      )
                      atTop
                      atTop
                  )
                    ∨
                  (
                    (
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
                          h3TerminalForcingFourthQRadialLerayEnvelopeAt
                            hH3 hClass (hr n) j₀
                        ) ^ 2
                    )
                      ∧
                    Tendsto
                      (
                        fun n : ℕ =>
                          h3TerminalForcingFourthQRadialLerayEnvelopeAt
                            hH3 hClass (hr n) j₀
                      )
                      atTop
                      atTop
                  )
                )

theorem adjacentQEnvelopeCanonicalRateEscapeSubsequenceOf_of_adjacentQCanonicalRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hAdjacent :
      H3TerminalPhysicalTopDissipationFixedThirdRadialForcingAdjacentQCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationFixedThirdRadialForcingAdjacentQEnvelopeCanonicalRateEscapeSubsequenceOf
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
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      hBranch
    ⟩ :=
    hAdjacent

  have hrStrict :
      ∀ n : ℕ,
        r (φ (ψ n)) ∈ Set.Ioo a T := by

    intro n

    exact
      ⟨
        lt_of_lt_of_le
          (hs (φ (ψ n))).1
          (hPoint n).1,
        lt_of_le_of_lt
          (hPoint n).2
          (hσ (m (q (φ (ψ n))))).2
      ⟩

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
      hrStrict,
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      ?_
    ⟩

  rcases hBranch with hSecond | hFourth

  · left

    have hRate :
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
            h3TerminalForcingSecondQRadialLerayEnvelopeAt
              hH3 hClass (hrStrict n) j₀
          ) ^ 2 := by

      intro n

      have hBound :=
        h3TerminalPhysicalTopDissipationForcingSecondQMassAt_le_sq_radialLerayEnvelope
          hH3 hClass (hrStrict n) j₀

      rw [
        ← h3TerminalPhysicalTopDissipationForcingSecondQMassPath_eq
          hH3 hClass (hrStrict n) j₀
      ] at hBound

      exact
        (hSecond.1 n).trans_le
          hBound

    have hTop :=
      h3TerminalForcingSecondQRadialLerayEnvelopeAt_tendstoAtTop_of_massPath_tendstoAtTop
        hH3
        hClass
        j₀
        (fun n : ℕ => r (φ (ψ n)))
        hrStrict
        hSecond.2

    exact
      ⟨
        hRate,
        hTop
      ⟩

  · right

    have hRate :
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
            h3TerminalForcingFourthQRadialLerayEnvelopeAt
              hH3 hClass (hrStrict n) j₀
          ) ^ 2 := by

      intro n

      have hBound :=
        h3TerminalPhysicalTopDissipationForcingFourthQMassAt_le_sq_radialLerayEnvelope
          hH3 hClass (hrStrict n) j₀

      rw [
        ← h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq
          hH3 hClass (hrStrict n) j₀
      ] at hBound

      exact
        (hFourth.1 n).trans_le
          hBound

    have hTop :=
      h3TerminalForcingFourthQRadialLerayEnvelopeAt_tendstoAtTop_of_massPath_tendstoAtTop
        hH3
        hClass
        j₀
        (fun n : ℕ => r (φ (ψ n)))
        hrStrict
        hFourth.2

    exact
      ⟨
        hRate,
        hTop
      ⟩

theorem exists_fixed_terminalSequence_with_canonicalAdjacentQEnvelopeRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalTopDissipationFixedThirdRadialForcingAdjacentQEnvelopeCanonicalRateEscapeSubsequenceOf
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
      hAdjacent
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalAdjacentQForcingRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hEnvelope :
      H3TerminalPhysicalTopDissipationFixedThirdRadialForcingAdjacentQEnvelopeCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ :=
    adjacentQEnvelopeCanonicalRateEscapeSubsequenceOf_of_adjacentQCanonicalRateEscapeSubsequenceOf
      hH3
      hClass
      σ
      hAdjacent

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hEnvelope
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

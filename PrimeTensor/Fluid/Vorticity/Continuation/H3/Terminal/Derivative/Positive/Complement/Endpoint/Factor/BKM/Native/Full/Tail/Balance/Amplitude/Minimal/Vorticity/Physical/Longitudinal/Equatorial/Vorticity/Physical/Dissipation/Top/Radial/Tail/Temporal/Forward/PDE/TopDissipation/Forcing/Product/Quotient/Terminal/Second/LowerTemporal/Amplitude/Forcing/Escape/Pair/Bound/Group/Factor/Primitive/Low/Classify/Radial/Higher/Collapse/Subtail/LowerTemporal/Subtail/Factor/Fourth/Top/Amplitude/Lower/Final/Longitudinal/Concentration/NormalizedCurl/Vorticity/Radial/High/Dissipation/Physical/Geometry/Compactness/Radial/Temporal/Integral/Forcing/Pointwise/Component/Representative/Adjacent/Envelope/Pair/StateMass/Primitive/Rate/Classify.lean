import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.SecondQ.Escape.StateMass.Primitive.Classify
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify

/-!
# Classify the canonical primitive forcing rate

The preceding canonical rate theorem freezes one primitive index in either the
second-q or fourth-q forcing branch.

The first two primitive indices are raw-L2 factors and cannot diverge along a
strict terminal sequence.  The remaining indices are exactly:

* second-q: one raw-L1 component or one moment-six component;
* fourth-q: one raw-L1 component or one moment-ten component.

The raw-L1 alternatives force physical H3-energy escape on the same canonical
sequence.  The moment alternatives retain the explicit fourth-power
reciprocal-width lower bound unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalPhysicalTopDissipationClassifiedForcingPrimitiveCanonicalRateEscapeSubsequenceOf
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
                    ∃ χ ω : ℕ → ℕ,
                      StrictMono χ
                        ∧
                      StrictMono ω
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
                        (
                          ∃ j : Fin 3,
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
                                (
                                  2 *
                                    h3FourierMomentSplitCoefficient (6 : ℝ)
                                )
                                  *
                                (
                                  h3TerminalForcingThirdQRawL1MassAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    j
                                ) ^ 4
                            )
                              ∧
                            Tendsto
                              (
                                fun n : ℕ =>
                                  h3TerminalForcingThirdQRawL1MassAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    j
                              )
                              atTop
                              atTop
                              ∧
                            Tendsto
                              (
                                fun n : ℕ =>
                                  velocityH3EnergyAt u
                                    (r (φ (ψ (χ (ω n)))))
                              )
                              atTop
                              atTop
                        )
                          ∨
                        (
                          ∃ j : Fin 3,
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
                                (
                                  2 *
                                    h3FourierMomentSplitCoefficient (6 : ℝ)
                                )
                                  *
                                (
                                  h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    j
                                ) ^ 4
                            )
                              ∧
                            Tendsto
                              (
                                fun n : ℕ =>
                                  h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    j
                              )
                              atTop
                              atTop
                        )
                      )
                  )
                    ∨
                  (
                    ∃ χ ω : ℕ → ℕ,
                      StrictMono χ
                        ∧
                      StrictMono ω
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
                        (
                          ∃ j : Fin 3,
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
                                (
                                  2 *
                                    h3FourierMomentSplitCoefficient (10 : ℝ)
                                )
                                  *
                                (
                                  h3TerminalForcingFourthQRawL1MassAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    j
                                ) ^ 4
                            )
                              ∧
                            Tendsto
                              (
                                fun n : ℕ =>
                                  h3TerminalForcingFourthQRawL1MassAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    j
                              )
                              atTop
                              atTop
                              ∧
                            Tendsto
                              (
                                fun n : ℕ =>
                                  velocityH3EnergyAt u
                                    (r (φ (ψ (χ (ω n)))))
                              )
                              atTop
                              atTop
                        )
                          ∨
                        (
                          ∃ j : Fin 3,
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
                                (
                                  2 *
                                    h3FourierMomentSplitCoefficient (10 : ℝ)
                                )
                                  *
                                (
                                  h3TerminalForcingFourthQMoment10MassAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    j
                                ) ^ 4
                            )
                              ∧
                            Tendsto
                              (
                                fun n : ℕ =>
                                  h3TerminalForcingFourthQMoment10MassAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    j
                              )
                              atTop
                              atTop
                        )
                      )
                  )
                )

theorem classifiedForcingPrimitiveCanonicalRateEscapeSubsequenceOf_of_primitiveCanonicalRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hRate :
      H3TerminalPhysicalTopDissipationFixedForcingPrimitiveCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationClassifiedForcingPrimitiveCanonicalRateEscapeSubsequenceOf
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
    hRate

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
        q₀,
        ω,
        hOmegaMono,
        hsFinal,
        hSigmaFinal,
        hrFinal,
        hPrimitiveRate,
        hPrimitiveTop
      ⟩

    left

    refine
      ⟨
        χ,
        ω,
        hChiMono,
        hOmegaMono,
        hsFinal,
        hSigmaFinal,
        hrFinal,
        ?_
      ⟩

    fin_cases q₀

    · have hRawTop :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingThirdQRawL2FactorAt
                  hH3 hClass
                  (hr (χ (ω n)))
                  k₀ l₀ 0
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingSecondQPrimitiveFactorAt,
          h3TerminalForcingThirdQRawL2FactorAt
        ] using hPrimitiveTop

      have hNot :=
        not_h3TerminalForcingThirdQRawL2FactorAt_tendstoAtTop
          hH3 hClass k₀ l₀ 0
          (fun n : ℕ => r (φ (ψ (χ (ω n)))))
          (fun n : ℕ => hr (χ (ω n)))
          hrFinal

      exact
        False.elim
          (hNot hRawTop)

    · have hRawTop :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingThirdQRawL2FactorAt
                  hH3 hClass
                  (hr (χ (ω n)))
                  k₀ l₀ 1
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingSecondQPrimitiveFactorAt,
          h3TerminalForcingThirdQRawL2FactorAt
        ] using hPrimitiveTop

      have hNot :=
        not_h3TerminalForcingThirdQRawL2FactorAt_tendstoAtTop
          hH3 hClass k₀ l₀ 1
          (fun n : ℕ => r (φ (ψ (χ (ω n)))))
          (fun n : ℕ => hr (χ (ω n)))
          hrFinal

      exact
        False.elim
          (hNot hRawTop)

    · right

      refine
        ⟨
          k₀,
          ?_,
          ?_
        ⟩

      · intro n
        simpa [
          h3TerminalForcingSecondQPrimitiveFactorAt,
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
        ] using hPrimitiveRate n

      · simpa [
          h3TerminalForcingSecondQPrimitiveFactorAt,
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
        ] using hPrimitiveTop

    · left

      have hL1Top :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingThirdQRawL1MassAt
                  hH3 hClass
                  (hr (χ (ω n)))
                  l₀
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingSecondQPrimitiveFactorAt,
          h3TerminalForcingThirdQRawL1MassAt
        ] using hPrimitiveTop

      have hEnergyTop :=
        velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
          hH3
          hClass
          l₀
          (fun n : ℕ => r (φ (ψ (χ (ω n)))))
          (fun n : ℕ => hr (χ (ω n)))
          hL1Top

      refine
        ⟨
          l₀,
          ?_,
          hL1Top,
          hEnergyTop
        ⟩

      intro n
      simpa [
        h3TerminalForcingSecondQPrimitiveFactorAt,
        h3TerminalForcingThirdQRawL1MassAt
      ] using hPrimitiveRate n

    · left

      have hL1Top :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingThirdQRawL1MassAt
                  hH3 hClass
                  (hr (χ (ω n)))
                  k₀
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingSecondQPrimitiveFactorAt,
          h3TerminalForcingThirdQRawL1MassAt
        ] using hPrimitiveTop

      have hEnergyTop :=
        velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
          hH3
          hClass
          k₀
          (fun n : ℕ => r (φ (ψ (χ (ω n)))))
          (fun n : ℕ => hr (χ (ω n)))
          hL1Top

      refine
        ⟨
          k₀,
          ?_,
          hL1Top,
          hEnergyTop
        ⟩

      intro n
      simpa [
        h3TerminalForcingSecondQPrimitiveFactorAt,
        h3TerminalForcingThirdQRawL1MassAt
      ] using hPrimitiveRate n

    · right

      refine
        ⟨
          l₀,
          ?_,
          ?_
        ⟩

      · intro n
        simpa [
          h3TerminalForcingSecondQPrimitiveFactorAt,
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
        ] using hPrimitiveRate n

      · simpa [
          h3TerminalForcingSecondQPrimitiveFactorAt,
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
        ] using hPrimitiveTop

  · rcases hFourth with
      ⟨
        k₀,
        l₀,
        χ,
        hChiMono,
        q₀,
        ω,
        hOmegaMono,
        hsFinal,
        hSigmaFinal,
        hrFinal,
        hPrimitiveRate,
        hPrimitiveTop
      ⟩

    right

    refine
      ⟨
        χ,
        ω,
        hChiMono,
        hOmegaMono,
        hsFinal,
        hSigmaFinal,
        hrFinal,
        ?_
      ⟩

    fin_cases q₀

    · have hRawTop :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingFourthQRawL2FactorAt
                  hH3 hClass
                  (hr (χ (ω n)))
                  k₀ l₀ 0
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingFourthQModularPrimitiveFactorAt,
          h3TerminalForcingFourthQRawL2FactorAt
        ] using hPrimitiveTop

      have hNot :=
        not_h3TerminalForcingFourthQRawL2FactorAt_tendstoAtTop
          hH3 hClass k₀ l₀ 0
          (fun n : ℕ => r (φ (ψ (χ (ω n)))))
          (fun n : ℕ => hr (χ (ω n)))
          hrFinal

      exact
        False.elim
          (hNot hRawTop)

    · have hRawTop :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingFourthQRawL2FactorAt
                  hH3 hClass
                  (hr (χ (ω n)))
                  k₀ l₀ 1
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingFourthQModularPrimitiveFactorAt,
          h3TerminalForcingFourthQRawL2FactorAt
        ] using hPrimitiveTop

      have hNot :=
        not_h3TerminalForcingFourthQRawL2FactorAt_tendstoAtTop
          hH3 hClass k₀ l₀ 1
          (fun n : ℕ => r (φ (ψ (χ (ω n)))))
          (fun n : ℕ => hr (χ (ω n)))
          hrFinal

      exact
        False.elim
          (hNot hRawTop)

    · right

      refine
        ⟨
          k₀,
          ?_,
          ?_
        ⟩

      · intro n
        simpa [
          h3TerminalForcingFourthQModularPrimitiveFactorAt,
          h3TerminalForcingFourthQMoment10MassAt
        ] using hPrimitiveRate n

      · simpa [
          h3TerminalForcingFourthQModularPrimitiveFactorAt,
          h3TerminalForcingFourthQMoment10MassAt
        ] using hPrimitiveTop

    · left

      have hL1Top :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingFourthQRawL1MassAt
                  hH3 hClass
                  (hr (χ (ω n)))
                  l₀
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingFourthQModularPrimitiveFactorAt,
          h3TerminalForcingFourthQRawL1MassAt
        ] using hPrimitiveTop

      have hEnergyTop :=
        velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingFourthQRawL1MassAt_tendstoAtTop
          hH3
          hClass
          l₀
          (fun n : ℕ => r (φ (ψ (χ (ω n)))))
          (fun n : ℕ => hr (χ (ω n)))
          hL1Top

      refine
        ⟨
          l₀,
          ?_,
          hL1Top,
          hEnergyTop
        ⟩

      intro n
      simpa [
        h3TerminalForcingFourthQModularPrimitiveFactorAt,
        h3TerminalForcingFourthQRawL1MassAt
      ] using hPrimitiveRate n

    · left

      have hL1Top :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingFourthQRawL1MassAt
                  hH3 hClass
                  (hr (χ (ω n)))
                  k₀
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingFourthQModularPrimitiveFactorAt,
          h3TerminalForcingFourthQRawL1MassAt
        ] using hPrimitiveTop

      have hEnergyTop :=
        velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingFourthQRawL1MassAt_tendstoAtTop
          hH3
          hClass
          k₀
          (fun n : ℕ => r (φ (ψ (χ (ω n)))))
          (fun n : ℕ => hr (χ (ω n)))
          hL1Top

      refine
        ⟨
          k₀,
          ?_,
          hL1Top,
          hEnergyTop
        ⟩

      intro n
      simpa [
        h3TerminalForcingFourthQModularPrimitiveFactorAt,
        h3TerminalForcingFourthQRawL1MassAt
      ] using hPrimitiveRate n

    · right

      refine
        ⟨
          l₀,
          ?_,
          ?_
        ⟩

      · intro n
        simpa [
          h3TerminalForcingFourthQModularPrimitiveFactorAt,
          h3TerminalForcingFourthQMoment10MassAt
        ] using hPrimitiveRate n

      · simpa [
          h3TerminalForcingFourthQModularPrimitiveFactorAt,
          h3TerminalForcingFourthQMoment10MassAt
        ] using hPrimitiveTop

theorem exists_fixed_terminalSequence_with_classifiedCanonicalForcingPrimitiveRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalTopDissipationClassifiedForcingPrimitiveCanonicalRateEscapeSubsequenceOf
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
      hRate
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalForcingPrimitiveRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hClassified :
      H3TerminalPhysicalTopDissipationClassifiedForcingPrimitiveCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ :=
    classifiedForcingPrimitiveCanonicalRateEscapeSubsequenceOf_of_primitiveCanonicalRateEscapeSubsequenceOf
      hH3
      hClass
      σ
      hRate

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hClassified
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

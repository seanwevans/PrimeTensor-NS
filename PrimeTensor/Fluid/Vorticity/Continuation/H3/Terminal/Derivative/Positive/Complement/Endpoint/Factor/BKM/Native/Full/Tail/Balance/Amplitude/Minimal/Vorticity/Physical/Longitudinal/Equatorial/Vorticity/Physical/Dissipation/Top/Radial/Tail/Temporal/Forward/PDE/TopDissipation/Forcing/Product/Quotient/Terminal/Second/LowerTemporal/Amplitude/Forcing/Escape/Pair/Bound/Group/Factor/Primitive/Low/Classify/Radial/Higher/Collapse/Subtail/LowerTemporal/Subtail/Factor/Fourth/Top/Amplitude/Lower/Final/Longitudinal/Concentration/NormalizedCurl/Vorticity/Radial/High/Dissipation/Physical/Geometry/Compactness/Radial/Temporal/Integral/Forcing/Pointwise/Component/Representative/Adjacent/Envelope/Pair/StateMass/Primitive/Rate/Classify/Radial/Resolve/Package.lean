import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve

/-!
# Package the resolved canonical forcing rate

The classified canonical forcing package still records raw-L1 and moment
alternatives.  The local resolver removes those internal alternatives.

This file preserves the complete canonical terminal geometry and replaces the
last forcing classification with exactly three outcomes:

* physical H3-energy escape;
* the resolved second-q higher-radial channel;
* the resolved fourth-q higher-radial channel.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalPhysicalTopDissipationResolvedCanonicalForcingRateEscapeSubsequenceOf
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
                  let τ : ℕ → ℝ :=
                    fun n : ℕ =>
                      r (φ (ψ (χ (ω n))))
                  let rate : ℕ → ℝ :=
                    fun n : ℕ =>
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
                  (
                    ∃ v : ℕ → ℕ,
                      StrictMono v
                        ∧
                      Tendsto
                        (fun n : ℕ => τ (v n))
                        atTop
                        (𝓝 T)
                        ∧
                      Tendsto
                        (
                          fun n : ℕ =>
                            velocityH3EnergyAt u (τ (v n))
                        )
                        atTop
                        atTop
                  )
                    ∨
                  (
                    ∃ j : Fin 3,
                      ∃ qRadial : Fin 2,
                        ∃ v : ℕ → ℕ,
                          StrictMono v
                            ∧
                          Tendsto
                            (fun n : ℕ => τ (v n))
                            atTop
                            (𝓝 T)
                            ∧
                          (
                            ∀ n : ℕ,
                              rate (v n)
                                <
                              (
                                (
                                  (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
                                    *
                                  (
                                    2
                                      *
                                    h3FourierMomentSplitCoefficient (6 : ℝ)
                                  )
                                )
                                  *
                                256
                              )
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
                                        hH3 hClass
                                        (hr (χ (ω (v n))))
                                        j
                                        qRadial
                                    )
                                )
                              ) ^ 4
                          )
                            ∧
                          Tendsto
                            (
                              fun n : ℕ =>
                                h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                                  hH3 hClass
                                  (hr (χ (ω (v n))))
                                  j
                                  qRadial
                            )
                            atTop
                            atTop
                            ∧
                          Tendsto
                            (
                              fun n : ℕ =>
                                h3TerminalPhysicalExtendedHigherRadialMomentAt
                                  hH3 hClass
                                  (h3TerminalForcingThirdQHigherRadialShift qRadial)
                                  (τ (v n))
                                  (hr (χ (ω (v n))))
                            )
                            atTop
                            (𝓝 ∞)
                  )
                    ∨
                  (
                    ∃ j : Fin 3,
                      ∃ qRadial : Fin 2,
                        ∃ v : ℕ → ℕ,
                          StrictMono v
                            ∧
                          Tendsto
                            (fun n : ℕ => τ (v n))
                            atTop
                            (𝓝 T)
                            ∧
                          (
                            ∀ n : ℕ,
                              rate (v n)
                                <
                              (
                                (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
                                  *
                                (
                                  2
                                    *
                                  h3FourierMomentSplitCoefficient (10 : ℝ)
                                )
                              )
                                *
                              (
                                h3StandardInverseBesselWeightL2Factor
                                  *
                                (
                                  2
                                    *
                                  Real.sqrt
                                    (
                                      h3TerminalForcingFourthQMoment10RadialSquareChannelAt
                                        hH3 hClass
                                        (hr (χ (ω (v n))))
                                        j
                                        qRadial
                                    )
                                )
                              ) ^ 4
                          )
                            ∧
                          Tendsto
                            (
                              fun n : ℕ =>
                                h3TerminalForcingFourthQMoment10RadialSquareChannelAt
                                  hH3 hClass
                                  (hr (χ (ω (v n))))
                                  j
                                  qRadial
                            )
                            atTop
                            atTop
                            ∧
                          Tendsto
                            (
                              fun n : ℕ =>
                                h3TerminalPhysicalExtendedHigherRadialMomentAt
                                  hH3 hClass
                                  (h3TerminalForcingFourthQHigherRadialShift qRadial)
                                  (τ (v n))
                                  (hr (χ (ω (v n))))
                            )
                            atTop
                            (𝓝 ∞)
                  )

theorem resolvedCanonicalForcingRateEscapeSubsequenceOf_of_classifiedCanonicalForcingPrimitiveRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hClassified :
      H3TerminalPhysicalTopDissipationClassifiedForcingPrimitiveCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationResolvedCanonicalForcingRateEscapeSubsequenceOf
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
    hClassified

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

  · obtain
      ⟨
        χ,
        ω,
        hChiMono,
        hOmegaMono,
        hsFinal,
        hSigmaFinal,
        hrFinal,
        hLocal
      ⟩ :=
      hSecond

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

    let τ : ℕ → ℝ :=
      fun n : ℕ =>
        r (φ (ψ (χ (ω n))))

    let rate : ℕ → ℝ :=
      fun n : ℕ =>
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

    have hτ :
        ∀ n : ℕ,
          τ n ∈ Set.Ioo a T := by
      intro n
      dsimp only [τ]
      exact
        hr (χ (ω n))

    have hResolved :=
      h3TerminalClassifiedCanonicalForcingPrimitiveRate_resolves_energy_or_fixedHigherRadial
        hH3
        hClass
        τ
        hτ
        (by
          simpa only [τ] using hrFinal)
        rate
        (by
          rcases hLocal with hL1 | hMoment

          · left
            obtain
              ⟨j, _hRate, _hL1Top, hEnergyTop⟩ :=
              hL1
            exact
              ⟨j, by simpa only [τ] using hEnergyTop⟩

          · right
            left
            obtain
              ⟨j, hRateMoment, hMomentTop⟩ :=
              hMoment
            exact
              ⟨
                j,
                by
                  intro n
                  simpa only [rate, τ] using hRateMoment n,
                by
                  simpa only [τ] using hMomentTop
              ⟩)

    simpa only [τ, rate] using
      hResolved

  · obtain
      ⟨
        χ,
        ω,
        hChiMono,
        hOmegaMono,
        hsFinal,
        hSigmaFinal,
        hrFinal,
        hLocal
      ⟩ :=
      hFourth

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

    let τ : ℕ → ℝ :=
      fun n : ℕ =>
        r (φ (ψ (χ (ω n))))

    let rate : ℕ → ℝ :=
      fun n : ℕ =>
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

    have hτ :
        ∀ n : ℕ,
          τ n ∈ Set.Ioo a T := by
      intro n
      dsimp only [τ]
      exact
        hr (χ (ω n))

    have hResolved :=
      h3TerminalClassifiedCanonicalForcingPrimitiveRate_resolves_energy_or_fixedHigherRadial
        hH3
        hClass
        τ
        hτ
        (by
          simpa only [τ] using hrFinal)
        rate
        (by
          rcases hLocal with hL1 | hMoment

          · right
            right
            left
            obtain
              ⟨j, _hRate, _hL1Top, hEnergyTop⟩ :=
              hL1
            exact
              ⟨j, by simpa only [τ] using hEnergyTop⟩

          · right
            right
            right
            obtain
              ⟨j, hRateMoment, hMomentTop⟩ :=
              hMoment
            exact
              ⟨
                j,
                by
                  intro n
                  simpa only [rate, τ] using hRateMoment n,
                by
                  simpa only [τ] using hMomentTop
              ⟩)

    simpa only [τ, rate] using
      hResolved

end

end Euclidean
end Bridge
end PrimeTensor

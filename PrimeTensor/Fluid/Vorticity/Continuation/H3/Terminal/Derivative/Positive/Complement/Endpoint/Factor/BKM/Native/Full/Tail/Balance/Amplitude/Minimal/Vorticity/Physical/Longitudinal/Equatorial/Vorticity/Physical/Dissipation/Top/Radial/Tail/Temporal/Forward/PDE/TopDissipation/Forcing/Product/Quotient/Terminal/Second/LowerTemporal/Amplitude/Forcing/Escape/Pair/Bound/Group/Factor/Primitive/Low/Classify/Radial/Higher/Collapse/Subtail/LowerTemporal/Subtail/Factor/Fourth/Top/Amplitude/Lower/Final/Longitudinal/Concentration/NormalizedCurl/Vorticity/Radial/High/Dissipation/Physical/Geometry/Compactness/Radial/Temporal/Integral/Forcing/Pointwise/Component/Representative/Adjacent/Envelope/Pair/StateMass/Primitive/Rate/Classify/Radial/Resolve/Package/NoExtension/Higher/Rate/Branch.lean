import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate

/-!
# Divergent reciprocal-width rate on resolved forcing branches

The resolved forcing classification already retains the reciprocal-width lower
bound on each fixed radial branch.  The canonical shrinking-interval lemma
shows that this inherited rate itself tends to `+∞`.

This file adds that fact at the local branch level, so later package wrappers
do not need to repeat the interval-width argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

theorem h3TerminalResolvedCanonicalForcingRateBranch_adds_rate_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hδ : 0 < δ)
    (s t τ rate : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hsTendsto :
      Tendsto s atTop (𝓝 T))
    (htUpper :
      ∀ n : ℕ,
        t n < T)
    (hForward :
      ∀ n : ℕ,
        s n < t n)
    (hRateEq :
      ∀ n : ℕ,
        rate n
          =
        δ
          /
        (
          12
            *
          (
            t n
              -
            s n
          )
        ))
    (hBranch :
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
                            (hτ (v n))
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
                      (hτ (v n))
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
                      (hτ (v n))
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
                            (hτ (v n))
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
                      (hτ (v n))
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
                      (hτ (v n))
                )
                atTop
                (𝓝 ∞)
      )) :
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
            Tendsto
              (fun n : ℕ => rate (v n))
              atTop
              atTop
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
                          (hτ (v n))
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
                    (hτ (v n))
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
                    (hτ (v n))
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
            Tendsto
              (fun n : ℕ => rate (v n))
              atTop
              atTop
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
                          (hτ (v n))
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
                    (hτ (v n))
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
                    (hτ (v n))
              )
              atTop
              (𝓝 ∞)
    ) := by

  have hRateTopRaw :
      Tendsto
        (
          fun n : ℕ =>
            δ
              /
            (
              12
                *
              (
                t n
                  -
                s n
              )
            )
        )
        atTop
        atTop :=
    h3TerminalCanonicalReciprocalWidthRate_tendstoAtTop
      hδ
      s
      t
      hsTendsto
      htUpper
      hForward

  have hRateFun :
      rate
        =
      fun n : ℕ =>
        δ
          /
        (
          12
            *
          (
            t n
              -
            s n
          )
        ) := by

    funext n
    exact
      hRateEq n

  have hRateTop :
      Tendsto rate atTop atTop := by

    rw [hRateFun]

    exact
      hRateTopRaw

  rcases hBranch with hEnergy | hSecond | hFourth

  · exact
      Or.inl
        hEnergy

  · obtain
      ⟨
        j,
        qRadial,
        v,
        hMono,
        hTauSub,
        hRate,
        hSquareTop,
        hHigherTop
      ⟩ :=
      hSecond

    have hRateSubTop :
        Tendsto
          (fun n : ℕ => rate (v n))
          atTop
          atTop :=
      hRateTop.comp
        hMono.tendsto_atTop

    exact
      Or.inr
        (Or.inl
          ⟨
            j,
            qRadial,
            v,
            hMono,
            hTauSub,
            hRateSubTop,
            hRate,
            hSquareTop,
            hHigherTop
          ⟩)

  · obtain
      ⟨
        j,
        qRadial,
        v,
        hMono,
        hTauSub,
        hRate,
        hSquareTop,
        hHigherTop
      ⟩ :=
      hFourth

    have hRateSubTop :
        Tendsto
          (fun n : ℕ => rate (v n))
          atTop
          atTop :=
      hRateTop.comp
        hMono.tendsto_atTop

    exact
      Or.inr
        (Or.inr
          ⟨
            j,
            qRadial,
            v,
            hMono,
            hTauSub,
            hRateSubTop,
            hRate,
            hSquareTop,
            hHigherTop
          ⟩)

end

end Euclidean
end Bridge
end PrimeTensor

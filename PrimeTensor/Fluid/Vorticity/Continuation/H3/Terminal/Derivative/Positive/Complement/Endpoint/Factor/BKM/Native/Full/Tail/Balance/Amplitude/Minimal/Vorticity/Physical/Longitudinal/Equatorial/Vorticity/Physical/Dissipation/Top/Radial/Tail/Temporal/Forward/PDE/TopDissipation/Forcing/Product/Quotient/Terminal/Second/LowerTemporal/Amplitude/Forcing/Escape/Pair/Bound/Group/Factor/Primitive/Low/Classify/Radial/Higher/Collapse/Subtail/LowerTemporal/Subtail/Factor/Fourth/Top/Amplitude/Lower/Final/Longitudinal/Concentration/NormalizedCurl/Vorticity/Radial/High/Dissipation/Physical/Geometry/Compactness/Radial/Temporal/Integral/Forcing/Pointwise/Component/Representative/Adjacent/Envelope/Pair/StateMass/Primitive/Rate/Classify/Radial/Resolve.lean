import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Second.Resolve.Canonical
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Fourth.Canonical

/-!
# Resolve classified canonical forcing primitive rates

After primitive classification there are only four live local cases:

* second-q raw-L1;
* second-q derivative moment-six;
* fourth-q raw-L1;
* fourth-q moment-ten.

The raw-L1 cases are already physical H3-energy escape.  The two moment cases
are resolved by the canonical quantitative radial bridges.  Hence every
classified canonical primitive rate reduces to energy escape or one of two
fixed higher-radial channels.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

theorem h3TerminalClassifiedCanonicalForcingPrimitiveRate_resolves_energy_or_fixedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (rate : ℕ → ℝ)
    (hBranch :
      (
        ∃ j : Fin 3,
          Tendsto
            (
              fun n : ℕ =>
                velocityH3EnergyAt u (τ n)
            )
            atTop
            atTop
      )
        ∨
      (
        ∃ j : Fin 3,
          (
            ∀ n : ℕ,
              rate n
                <
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
              (
                h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
                  hH3 hClass (hτ n) j
              ) ^ 4
          )
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
                  hH3 hClass (hτ n) j
            )
            atTop
            atTop
      )
        ∨
      (
        ∃ j : Fin 3,
          Tendsto
            (
              fun n : ℕ =>
                velocityH3EnergyAt u (τ n)
            )
            atTop
            atTop
      )
        ∨
      (
        ∃ j : Fin 3,
          (
            ∀ n : ℕ,
              rate n
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
                h3TerminalForcingFourthQMoment10MassAt
                  hH3 hClass (hτ n) j
              ) ^ 4
          )
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingFourthQMoment10MassAt
                  hH3 hClass (hτ n) j
            )
            atTop
            atTop
      )) :
    (
      ∃ s : ℕ → ℕ,
        StrictMono s
          ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T)
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
      ∃ j : Fin 3,
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
              (𝓝 ∞)
    )
      ∨
    (
      ∃ j : Fin 3,
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
                          hH3 hClass (hτ (s n)) j q
                      )
                  )
                ) ^ 4
            )
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalForcingFourthQMoment10RadialSquareChannelAt
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
                    (h3TerminalForcingFourthQHigherRadialShift q)
                    (τ (s n))
                    (hτ (s n))
              )
              atTop
              (𝓝 ∞)
    ) := by

  rcases hBranch with hSecondL1 | hSecondMoment | hFourthL1 | hFourthMoment

  · obtain
      ⟨j, hEnergyTop⟩ :=
      hSecondL1

    exact
      Or.inl
        ⟨
          id,
          strictMono_id,
          by simpa using hTauTendsto,
          by simpa using hEnergyTop
        ⟩

  · obtain
      ⟨j, hRate, hMomentTop⟩ :=
      hSecondMoment

    rcases
      h3TerminalSecondQVelocityMoment6_canonicalCoefficient_rate_resolves_energy_or_fixedHigherRadial
        hH3
        hClass
        j
        τ
        hτ
        hTauTendsto
        rate
        hRate
        hMomentTop with
      hEnergy | hRadial

    · exact
        Or.inl
          hEnergy

    · obtain
        ⟨q, s, hMono, hTauSub, hRateFinal, hSquareTop, hHigherTop⟩ :=
        hRadial

      exact
        Or.inr
          (Or.inl
            ⟨
              j,
              q,
              s,
              hMono,
              hTauSub,
              hRateFinal,
              hSquareTop,
              hHigherTop
            ⟩)

  · obtain
      ⟨j, hEnergyTop⟩ :=
      hFourthL1

    exact
      Or.inl
        ⟨
          id,
          strictMono_id,
          by simpa using hTauTendsto,
          by simpa using hEnergyTop
        ⟩

  · obtain
      ⟨j, hRate, hMomentTop⟩ :=
      hFourthMoment

    obtain
      ⟨q, s, hMono, hTauSub, hRateFinal, hSquareTop, hHigherTop⟩ :=
      h3TerminalForcingFourthQMoment10_canonicalCoefficient_rate_resolves_fixedHigherRadial
        hH3
        hClass
        j
        τ
        hτ
        hTauTendsto
        rate
        hRate
        hMomentTop

    exact
      Or.inr
        (Or.inr
          ⟨
            j,
            q,
            s,
            hMono,
            hTauSub,
            hRateFinal,
            hSquareTop,
            hHigherTop
          ⟩)

end

end Euclidean
end Bridge
end PrimeTensor

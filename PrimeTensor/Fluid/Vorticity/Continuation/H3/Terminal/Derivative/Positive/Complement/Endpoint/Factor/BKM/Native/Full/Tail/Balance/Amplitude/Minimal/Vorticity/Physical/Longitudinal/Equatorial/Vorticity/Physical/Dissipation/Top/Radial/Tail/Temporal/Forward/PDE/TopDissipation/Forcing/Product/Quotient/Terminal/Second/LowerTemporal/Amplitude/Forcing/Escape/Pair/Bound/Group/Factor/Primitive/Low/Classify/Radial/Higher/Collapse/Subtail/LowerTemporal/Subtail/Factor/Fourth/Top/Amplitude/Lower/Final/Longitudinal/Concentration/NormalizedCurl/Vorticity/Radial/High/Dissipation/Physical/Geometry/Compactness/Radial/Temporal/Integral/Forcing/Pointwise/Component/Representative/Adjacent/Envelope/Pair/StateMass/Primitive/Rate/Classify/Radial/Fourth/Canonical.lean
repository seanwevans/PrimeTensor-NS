import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial

/-!
# Canonical fourth-q moment-ten rate resolution

Specialize the quantitative fourth-q moment-ten radial transfer to the exact
coefficient produced by the canonical primitive forcing classification.

Unlike the second-q moment-six branch, this branch already sits at the moment-ten
radial frontier, so no intermediate resolver loss is needed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

theorem h3TerminalForcingFourthQMoment10_canonicalCoefficient_rate_resolves_fixedHigherRadial
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
    (hRate :
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
        ) ^ 4)
    (hMomentTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQMoment10MassAt
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
          (𝓝 ∞) := by

  let K : ℝ :=
    (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
      *
    (
      2
        *
      h3FourierMomentSplitCoefficient (10 : ℝ)
    )

  have hMomentCoefficient0 :
      0
        ≤
      2
        *
      h3FourierMomentSplitCoefficient (10 : ℝ) :=
    mul_nonneg
      (by norm_num)
      (h3FourierMomentSplitCoefficient_nonneg (10 : ℝ))

  have hK0 :
      0 ≤ K := by
    dsimp only [K]
    exact
      mul_nonneg
        (sq_nonneg _)
        hMomentCoefficient0

  have hResolved :=
    exists_fixed_h3TerminalForcingFourthQMoment10RadialSquareChannel_rate_subsequence
      hH3
      hClass
      j
      τ
      hτ
      hTauTendsto
      rate
      K
      hK0
      (by
        intro n
        simpa only [K] using hRate n)
      hMomentTop

  simpa only [K] using
    hResolved

end

end Euclidean
end Bridge
end PrimeTensor

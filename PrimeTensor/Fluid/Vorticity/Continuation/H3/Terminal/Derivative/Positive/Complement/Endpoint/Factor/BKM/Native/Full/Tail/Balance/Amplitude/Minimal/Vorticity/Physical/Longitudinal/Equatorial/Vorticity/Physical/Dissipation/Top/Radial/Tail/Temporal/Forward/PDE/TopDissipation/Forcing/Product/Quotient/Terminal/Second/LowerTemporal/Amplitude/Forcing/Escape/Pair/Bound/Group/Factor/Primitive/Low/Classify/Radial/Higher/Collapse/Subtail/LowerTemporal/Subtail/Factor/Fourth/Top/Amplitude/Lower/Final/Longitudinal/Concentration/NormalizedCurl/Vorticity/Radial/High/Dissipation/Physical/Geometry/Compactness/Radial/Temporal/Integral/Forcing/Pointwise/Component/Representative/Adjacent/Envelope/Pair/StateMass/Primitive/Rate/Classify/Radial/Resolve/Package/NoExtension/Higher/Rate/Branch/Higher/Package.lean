import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Package
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher

/-!
# Higher-moment domination on divergent resolved forcing branches

Each non-energy divergent forcing branch already fixes one radial-square
channel and one selected terminal subsequence.  The channel domination lemmas
therefore apply pointwise at every selected time.

This strengthens the branch with a same-time quantitative bridge from the
selected radial-square mass into the corresponding extended higher-radial
moment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalResolvedCanonicalForcingDivergentRateHigherDominatedBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (rate : ℕ → ℝ) : Prop :=
  (
    ∃ v : ℕ → ℕ,
      StrictMono v
        ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T)
        ∧
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (τ (v n)))
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
          Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T)
            ∧
          Tendsto (fun n : ℕ => rate (v n)) atTop atTop
            ∧
          (
            ∀ n : ℕ,
              rate (v n)
                <
              (
                (
                  (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
                    *
                  (2 * h3FourierMomentSplitCoefficient (6 : ℝ))
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
                        hH3 hClass (hτ (v n)) j qRadial
                    )
                )
              ) ^ 4
          )
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                  hH3 hClass (hτ (v n)) j qRadial
            )
            atTop
            atTop
            ∧
          (
            ∀ n : ℕ,
              ENNReal.ofReal
                (
                  h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
                    *
                  h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                    hH3 hClass (hτ (v n)) j qRadial
                )
                ≤
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass
                (h3TerminalForcingThirdQHigherRadialShift qRadial)
                (τ (v n))
                (hτ (v n))
          )
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
          Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T)
            ∧
          Tendsto (fun n : ℕ => rate (v n)) atTop atTop
            ∧
          (
            ∀ n : ℕ,
              rate (v n)
                <
              (
                (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
                  *
                (2 * h3FourierMomentSplitCoefficient (10 : ℝ))
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
                        hH3 hClass (hτ (v n)) j qRadial
                    )
                )
              ) ^ 4
          )
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingFourthQMoment10RadialSquareChannelAt
                  hH3 hClass (hτ (v n)) j qRadial
            )
            atTop
            atTop
            ∧
          (
            ∀ n : ℕ,
              ENNReal.ofReal
                (
                  h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
                    *
                  h3TerminalForcingFourthQMoment10RadialSquareChannelAt
                    hH3 hClass (hτ (v n)) j qRadial
                )
                ≤
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass
                (h3TerminalForcingFourthQHigherRadialShift qRadial)
                (τ (v n))
                (hτ (v n))
          )
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
  )

theorem resolvedCanonicalForcingDivergentRateHigherDominatedBranch_of_divergentRateBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (rate : ℕ → ℝ)
    (hBranch :
      H3TerminalResolvedCanonicalForcingDivergentRateBranch
        hH3 hClass τ hτ rate) :
    H3TerminalResolvedCanonicalForcingDivergentRateHigherDominatedBranch
      hH3 hClass τ hτ rate := by

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
        hRateTop,
        hRate,
        hSquareTop,
        hHigherTop
      ⟩ :=
      hSecond

    have hDom :
        ∀ n : ℕ,
          ENNReal.ofReal
            (
              h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
                *
              h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                hH3 hClass (hτ (v n)) j qRadial
            )
            ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass
            (h3TerminalForcingThirdQHigherRadialShift qRadial)
            (τ (v n))
            (hτ (v n)) := by

      intro n

      exact
        ofReal_scaled_h3TerminalForcingThirdQMoment14RadialSquareChannelAt_le_extendedHigherRadial
          hH3
          hClass
          (hτ (v n))
          j
          qRadial

    exact
      Or.inr
        (Or.inl
          ⟨
            j,
            qRadial,
            v,
            hMono,
            hTauSub,
            hRateTop,
            hRate,
            hSquareTop,
            hDom,
            hHigherTop
          ⟩)

  · obtain
      ⟨
        j,
        qRadial,
        v,
        hMono,
        hTauSub,
        hRateTop,
        hRate,
        hSquareTop,
        hHigherTop
      ⟩ :=
      hFourth

    have hDom :
        ∀ n : ℕ,
          ENNReal.ofReal
            (
              h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
                *
              h3TerminalForcingFourthQMoment10RadialSquareChannelAt
                hH3 hClass (hτ (v n)) j qRadial
            )
            ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass
            (h3TerminalForcingFourthQHigherRadialShift qRadial)
            (τ (v n))
            (hτ (v n)) := by

      intro n

      exact
        ofReal_scaled_h3TerminalForcingFourthQMoment10RadialSquareChannelAt_le_extendedHigherRadial
          hH3
          hClass
          (hτ (v n))
          j
          qRadial

    exact
      Or.inr
        (Or.inr
          ⟨
            j,
            qRadial,
            v,
            hMono,
            hTauSub,
            hRateTop,
            hRate,
            hSquareTop,
            hDom,
            hHigherTop
          ⟩)

end

end Euclidean
end Bridge
end PrimeTensor

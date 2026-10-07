import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Package
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct

/-!
# Collapse divergent forcing branches directly to higher radial moments

The preceding checkpoints retain both the intermediate radial-square channel
and the final extended higher-radial moment.  For downstream endpoint
arguments the square channel is no longer necessary.

Since the resolved reciprocal-width rate tends to `+∞`, it is eventually
positive.  The direct rate-to-higher-moment lemmas therefore apply eventually
on either fixed radial branch.

This file packages the reduced conclusion:

* energy escape; or
* a fixed second-q channel with divergent rate, an eventual explicit
  rate-to-higher-moment lower bound, and higher-moment escape; or
* the analogous fixed fourth-q channel.

The intermediate radial-square escape and its separate domination inequality
have been eliminated from the exposed branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalResolvedCanonicalForcingDivergentRateDirectHigherBranch
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
            ∀ᶠ n : ℕ in atTop,
              ENNReal.ofReal
                  (
                    h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
                      *
                    Real.sqrt
                      (
                        rate (v n)
                          /
                        h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                      )
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
            ∀ᶠ n : ℕ in atTop,
              ENNReal.ofReal
                  (
                    h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
                      *
                    Real.sqrt
                      (
                        rate (v n)
                          /
                        h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                      )
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

theorem resolvedCanonicalForcingDivergentRateDirectHigherBranch_of_higherDominatedBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (rate : ℕ → ℝ)
    (hBranch :
      H3TerminalResolvedCanonicalForcingDivergentRateHigherDominatedBranch
        hH3 hClass τ hτ rate) :
    H3TerminalResolvedCanonicalForcingDivergentRateDirectHigherBranch
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
        hDom,
        hHigherTop
      ⟩ :=
      hSecond

    have hRatePos :
        ∀ᶠ n : ℕ in atTop,
          0 < rate (v n) :=
      hRateTop.eventually
        (eventually_gt_atTop (0 : ℝ))

    have hDirect :
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal
              (
                h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
                  *
                Real.sqrt
                  (
                    rate (v n)
                      /
                    h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                  )
              )
            ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass
            (h3TerminalForcingThirdQHigherRadialShift qRadial)
            (τ (v n))
            (hτ (v n)) := by

      filter_upwards [hRatePos] with n hn

      exact
        ofReal_thirdQHigherScale_mul_sqrt_secondQResolvedRate_le_extendedHigherRadial
          hH3
          hClass
          (hτ (v n))
          j
          qRadial
          hn
          (hRate n)

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
            hDirect,
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
        hDom,
        hHigherTop
      ⟩ :=
      hFourth

    have hRatePos :
        ∀ᶠ n : ℕ in atTop,
          0 < rate (v n) :=
      hRateTop.eventually
        (eventually_gt_atTop (0 : ℝ))

    have hDirect :
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal
              (
                h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
                  *
                Real.sqrt
                  (
                    rate (v n)
                      /
                    h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                  )
              )
            ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass
            (h3TerminalForcingFourthQHigherRadialShift qRadial)
            (τ (v n))
            (hτ (v n)) := by

      filter_upwards [hRatePos] with n hn

      exact
        ofReal_fourthQHigherScale_mul_sqrt_fourthQResolvedRate_le_extendedHigherRadial
          hH3
          hClass
          (hτ (v n))
          j
          qRadial
          hn
          (hRate n)

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
            hDirect,
            hHigherTop
          ⟩)

end

end Euclidean
end Bridge
end PrimeTensor

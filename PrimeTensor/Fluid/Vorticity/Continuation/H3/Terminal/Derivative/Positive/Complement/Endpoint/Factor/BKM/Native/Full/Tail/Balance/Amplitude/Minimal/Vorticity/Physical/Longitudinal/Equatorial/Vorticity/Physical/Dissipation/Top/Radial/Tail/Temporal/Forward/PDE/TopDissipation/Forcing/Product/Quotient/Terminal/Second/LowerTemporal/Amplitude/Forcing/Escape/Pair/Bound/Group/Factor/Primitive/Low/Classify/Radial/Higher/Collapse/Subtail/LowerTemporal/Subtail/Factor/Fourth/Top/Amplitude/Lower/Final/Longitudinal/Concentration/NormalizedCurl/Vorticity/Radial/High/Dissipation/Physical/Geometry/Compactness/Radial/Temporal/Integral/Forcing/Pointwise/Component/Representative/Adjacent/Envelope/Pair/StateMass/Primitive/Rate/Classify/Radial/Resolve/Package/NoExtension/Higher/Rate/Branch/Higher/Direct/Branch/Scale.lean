import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Branch
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Positive

/-!
# Divergence of the direct higher-radial lower scale

The direct forcing branch carries

    ofReal (scale * sqrt (rate / K)) ≤ higherMoment

eventually, together with `rate → +∞`.

The preceding positivity checkpoint proves both canonical coefficients `K`
strictly positive, and the channel-normalization scales are already strictly
positive. Therefore the real lower scale itself tends to `+∞`; consequently
its `ENNReal.ofReal` image tends to `∞` as well.

This file records those asymptotics directly in the reduced branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/--
Positive division, square root, and multiplication preserve divergence to
`+∞`.
-/
theorem tendsto_positiveScale_mul_sqrt_div_atTop
    {f : ℕ → ℝ}
    (hf : Tendsto f atTop atTop)
    {K scale : ℝ}
    (hK : 0 < K)
    (hScale : 0 < scale) :
    Tendsto
      (fun n : ℕ =>
        scale * Real.sqrt (f n / K))
      atTop
      atTop := by

  have hDiv :
      Tendsto
        (fun n : ℕ => f n / K)
        atTop
        atTop := by

    have hScaled :=
      hf.const_mul_atTop
        (inv_pos.mpr hK)

    simpa only [
      div_eq_mul_inv,
      mul_comm
    ] using
      hScaled

  have hRoot :
      Tendsto
        (fun n : ℕ => Real.sqrt (f n / K))
        atTop
        atTop :=
    Real.tendsto_sqrt_atTop.comp
      hDiv

  exact
    hRoot.const_mul_atTop
      hScale

/--
The `ENNReal.ofReal` image of the positive scaled square-root lower profile
also diverges to `∞`.
-/
theorem tendsto_ofReal_positiveScale_mul_sqrt_div_atTop
    {f : ℕ → ℝ}
    (hf : Tendsto f atTop atTop)
    {K scale : ℝ}
    (hK : 0 < K)
    (hScale : 0 < scale) :
    Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal
          (scale * Real.sqrt (f n / K)))
      atTop
      (𝓝 ∞) := by

  exact
    ENNReal.tendsto_ofReal_atTop.comp
      (
        tendsto_positiveScale_mul_sqrt_div_atTop
          hf
          hK
          hScale
      )

def H3TerminalResolvedCanonicalForcingDivergentRateDirectHigherScaleBranch
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
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
                  *
                Real.sqrt
                  (
                    rate (v n)
                      /
                    h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                  )
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
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
            )
            atTop
            (𝓝 ∞)
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
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
                  *
                Real.sqrt
                  (
                    rate (v n)
                      /
                    h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                  )
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
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
            )
            atTop
            (𝓝 ∞)
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

theorem resolvedCanonicalForcingDivergentRateDirectHigherScaleBranch_of_directHigherBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (rate : ℕ → ℝ)
    (hBranch :
      H3TerminalResolvedCanonicalForcingDivergentRateDirectHigherBranch
        hH3 hClass τ hτ rate) :
    H3TerminalResolvedCanonicalForcingDivergentRateDirectHigherScaleBranch
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
        hDirect,
        hHigherTop
      ⟩ :=
      hSecond

    have hScaleTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
                *
              Real.sqrt
                (
                  rate (v n)
                    /
                  h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                )
          )
          atTop
          atTop :=
      tendsto_positiveScale_mul_sqrt_div_atTop
        hRateTop
        h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient_pos
        (h3TerminalForcingThirdQMoment14RadialSquareHigherScale_pos qRadial)

    have hOfRealScaleTop :
        Tendsto
          (
            fun n : ℕ =>
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
          )
          atTop
          (𝓝 ∞) :=
      ENNReal.tendsto_ofReal_atTop.comp
        hScaleTop

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
            hScaleTop,
            hOfRealScaleTop,
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
        hDirect,
        hHigherTop
      ⟩ :=
      hFourth

    have hScaleTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
                *
              Real.sqrt
                (
                  rate (v n)
                    /
                  h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                )
          )
          atTop
          atTop :=
      tendsto_positiveScale_mul_sqrt_div_atTop
        hRateTop
        h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient_pos
        (h3TerminalForcingFourthQMoment10RadialSquareHigherScale_pos qRadial)

    have hOfRealScaleTop :
        Tendsto
          (
            fun n : ℕ =>
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
          )
          atTop
          (𝓝 ∞) :=
      ENNReal.tendsto_ofReal_atTop.comp
        hScaleTop

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
            hScaleTop,
            hOfRealScaleTop,
            hDirect,
            hHigherTop
          ⟩)

end

end Euclidean
end Bridge
end PrimeTensor

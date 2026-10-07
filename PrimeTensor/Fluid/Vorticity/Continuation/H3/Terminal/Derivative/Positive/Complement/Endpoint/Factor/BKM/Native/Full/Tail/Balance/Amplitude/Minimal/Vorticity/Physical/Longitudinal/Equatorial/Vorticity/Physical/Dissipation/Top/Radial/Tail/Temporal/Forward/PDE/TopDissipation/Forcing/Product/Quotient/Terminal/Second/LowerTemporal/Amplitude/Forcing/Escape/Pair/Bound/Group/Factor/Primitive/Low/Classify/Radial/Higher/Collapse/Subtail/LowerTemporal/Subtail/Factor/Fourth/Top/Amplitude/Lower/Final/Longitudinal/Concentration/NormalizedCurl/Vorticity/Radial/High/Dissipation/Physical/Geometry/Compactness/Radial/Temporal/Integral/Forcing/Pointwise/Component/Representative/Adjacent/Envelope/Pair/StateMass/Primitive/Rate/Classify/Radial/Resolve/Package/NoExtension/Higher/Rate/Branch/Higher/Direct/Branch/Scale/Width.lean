import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Branch.Scale

/-!
# Replace the abstract forcing rate by the reciprocal-width scale

The canonical forcing rate has the exact form

    rate n = δ / (12 * gap n).

The direct higher-radial lower profile from the preceding checkpoint is

    scale * sqrt (rate n / K).

This file substitutes the exact rate and rewrites the profile as

    scale * sqrt (δ / (12 * K * gap n)).

Thus the surviving radial alternatives expose the explicit inverse
square-root width scale directly, rather than through an abstract `rate`.
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
Pure field identity behind the reciprocal-width substitution.
-/
theorem reciprocalWidth_rate_div_coefficient
    (δ gap K : ℝ) :
    (δ / (12 * gap)) / K
      =
    δ / (12 * K * gap) := by

  calc
    (δ / (12 * gap)) / K
        =
      δ / ((12 * gap) * K) := by
        rw [div_div]
    _ =
      δ / (12 * K * gap) := by
        congr 1
        ring

def H3TerminalResolvedCanonicalForcingDivergentWidthDirectHigherScaleBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (δ : ℝ)
    (gap : ℕ → ℝ) : Prop :=
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
          Tendsto
            (fun n : ℕ =>
              δ / (12 * gap (v n)))
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
                  *
                Real.sqrt
                  (
                    δ
                      /
                    (
                      12
                        *
                      h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                        *
                      gap (v n)
                    )
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
                        δ
                          /
                        (
                          12
                            *
                          h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                            *
                          gap (v n)
                        )
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
                        δ
                          /
                        (
                          12
                            *
                          h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                            *
                          gap (v n)
                        )
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
          Tendsto
            (fun n : ℕ =>
              δ / (12 * gap (v n)))
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
                  *
                Real.sqrt
                  (
                    δ
                      /
                    (
                      12
                        *
                      h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                        *
                      gap (v n)
                    )
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
                        δ
                          /
                        (
                          12
                            *
                          h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                            *
                          gap (v n)
                        )
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
                        δ
                          /
                        (
                          12
                            *
                          h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                            *
                          gap (v n)
                        )
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

theorem resolvedCanonicalForcingDivergentWidthDirectHigherScaleBranch_of_rateScaleBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (rate gap : ℕ → ℝ)
    (δ : ℝ)
    (hRate :
      ∀ n : ℕ,
        rate n = δ / (12 * gap n))
    (hBranch :
      H3TerminalResolvedCanonicalForcingDivergentRateDirectHigherScaleBranch
        hH3 hClass τ hτ rate) :
    H3TerminalResolvedCanonicalForcingDivergentWidthDirectHigherScaleBranch
      hH3 hClass τ hτ δ gap := by

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
        hScaleTop,
        hOfRealScaleTop,
        hDirect,
        hHigherTop
      ⟩ :=
      hSecond

    have hRateWidth :
        Tendsto
          (fun n : ℕ =>
            δ / (12 * gap (v n)))
          atTop
          atTop := by

      simpa only [hRate] using
        hRateTop

    have hProfileEq :
        ∀ n : ℕ,
          h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
              *
            Real.sqrt
              (
                rate (v n)
                  /
                h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
              )
            =
          h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
              *
            Real.sqrt
              (
                δ
                  /
                (
                  12
                    *
                  h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                    *
                  gap (v n)
                )
              ) := by

      intro n

      rw [hRate]

      rw [
        reciprocalWidth_rate_div_coefficient
          δ
          (gap (v n))
          h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
      ]

    have hScaleFun :
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
          =
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
              *
            Real.sqrt
              (
                δ
                  /
                (
                  12
                    *
                  h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                    *
                  gap (v n)
                )
              )
        ) := by

      funext n

      exact
        hProfileEq n

    have hScaleWidth :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
                *
              Real.sqrt
                (
                  δ
                    /
                  (
                    12
                      *
                    h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                      *
                    gap (v n)
                  )
                )
          )
          atTop
          atTop := by

      rw [← hScaleFun]

      exact
        hScaleTop

    have hOfRealScaleWidth :
        Tendsto
          (
            fun n : ℕ =>
              ENNReal.ofReal
                (
                  h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
                    *
                  Real.sqrt
                    (
                      δ
                        /
                      (
                        12
                          *
                        h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                          *
                        gap (v n)
                      )
                    )
                )
          )
          atTop
          (𝓝 ∞) := by

      exact
        ENNReal.tendsto_ofReal_atTop.comp
          hScaleWidth

    have hDirectWidth :
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal
              (
                h3TerminalForcingThirdQMoment14RadialSquareHigherScale qRadial
                  *
                Real.sqrt
                  (
                    δ
                      /
                    (
                      12
                        *
                      h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
                        *
                      gap (v n)
                    )
                  )
              )
            ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass
            (h3TerminalForcingThirdQHigherRadialShift qRadial)
            (τ (v n))
            (hτ (v n)) := by

      filter_upwards [hDirect] with n hn

      rw [← hProfileEq n]

      exact
        hn

    exact
      Or.inr
        (Or.inl
          ⟨
            j,
            qRadial,
            v,
            hMono,
            hTauSub,
            hRateWidth,
            hScaleWidth,
            hOfRealScaleWidth,
            hDirectWidth,
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
        hScaleTop,
        hOfRealScaleTop,
        hDirect,
        hHigherTop
      ⟩ :=
      hFourth

    have hRateWidth :
        Tendsto
          (fun n : ℕ =>
            δ / (12 * gap (v n)))
          atTop
          atTop := by

      simpa only [hRate] using
        hRateTop

    have hProfileEq :
        ∀ n : ℕ,
          h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
              *
            Real.sqrt
              (
                rate (v n)
                  /
                h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
              )
            =
          h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
              *
            Real.sqrt
              (
                δ
                  /
                (
                  12
                    *
                  h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                    *
                  gap (v n)
                )
              ) := by

      intro n

      rw [hRate]

      rw [
        reciprocalWidth_rate_div_coefficient
          δ
          (gap (v n))
          h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
      ]

    have hScaleFun :
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
          =
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
              *
            Real.sqrt
              (
                δ
                  /
                (
                  12
                    *
                  h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                    *
                  gap (v n)
                )
              )
        ) := by

      funext n

      exact
        hProfileEq n

    have hScaleWidth :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
                *
              Real.sqrt
                (
                  δ
                    /
                  (
                    12
                      *
                    h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                      *
                    gap (v n)
                  )
                )
          )
          atTop
          atTop := by

      rw [← hScaleFun]

      exact
        hScaleTop

    have hOfRealScaleWidth :
        Tendsto
          (
            fun n : ℕ =>
              ENNReal.ofReal
                (
                  h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
                    *
                  Real.sqrt
                    (
                      δ
                        /
                      (
                        12
                          *
                        h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                          *
                        gap (v n)
                      )
                    )
                )
          )
          atTop
          (𝓝 ∞) := by

      exact
        ENNReal.tendsto_ofReal_atTop.comp
          hScaleWidth

    have hDirectWidth :
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal
              (
                h3TerminalForcingFourthQMoment10RadialSquareHigherScale qRadial
                  *
                Real.sqrt
                  (
                    δ
                      /
                    (
                      12
                        *
                      h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
                        *
                      gap (v n)
                    )
                  )
              )
            ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass
            (h3TerminalForcingFourthQHigherRadialShift qRadial)
            (τ (v n))
            (hτ (v n)) := by

      filter_upwards [hDirect] with n hn

      rw [← hProfileEq n]

      exact
        hn

    exact
      Or.inr
        (Or.inr
          ⟨
            j,
            qRadial,
            v,
            hMono,
            hTauSub,
            hRateWidth,
            hScaleWidth,
            hOfRealScaleWidth,
            hDirectWidth,
            hHigherTop
          ⟩)

end

end Euclidean
end Bridge
end PrimeTensor

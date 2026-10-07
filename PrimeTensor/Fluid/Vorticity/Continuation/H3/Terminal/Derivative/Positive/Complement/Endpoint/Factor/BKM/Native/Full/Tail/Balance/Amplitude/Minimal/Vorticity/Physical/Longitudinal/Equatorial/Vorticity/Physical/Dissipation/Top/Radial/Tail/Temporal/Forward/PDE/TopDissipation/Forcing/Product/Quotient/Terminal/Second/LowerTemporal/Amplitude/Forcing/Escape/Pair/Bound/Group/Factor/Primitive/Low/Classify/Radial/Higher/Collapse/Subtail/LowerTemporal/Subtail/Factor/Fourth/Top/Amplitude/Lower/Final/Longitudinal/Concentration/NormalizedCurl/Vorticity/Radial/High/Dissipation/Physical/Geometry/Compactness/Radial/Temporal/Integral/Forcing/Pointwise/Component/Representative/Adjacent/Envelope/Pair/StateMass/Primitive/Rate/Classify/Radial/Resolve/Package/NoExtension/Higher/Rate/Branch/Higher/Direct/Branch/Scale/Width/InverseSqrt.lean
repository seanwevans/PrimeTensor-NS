import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Branch.Scale.Width
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Positive

/-!
# Normalize reciprocal-width higher-radial scales

The width-native forcing profile is presently written as

    scale * sqrt (δ / (12 * K * gap)).

For positive width this is exactly

    C / sqrt gap,

where the fixed coefficient is

    C = scale * sqrt (δ / (12 * K)).

This file names the two canonical coefficients and proves both their strict
positivity and the exact inverse-square-root identities.  No endpoint
alternative is changed here.
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
Fixed inverse-square-root width coefficient for the resolved second-q radial
branch.
-/
noncomputable def h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient
    (δ : ℝ)
    (q : Fin 2) : ℝ :=
  h3TerminalForcingThirdQMoment14RadialSquareHigherScale q
    *
  Real.sqrt
    (
      δ
        /
      (
        12
          *
        h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
      )
    )

/--
Fixed inverse-square-root width coefficient for the resolved fourth-q radial
branch.
-/
noncomputable def h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient
    (δ : ℝ)
    (q : Fin 2) : ℝ :=
  h3TerminalForcingFourthQMoment10RadialSquareHigherScale q
    *
  Real.sqrt
    (
      δ
        /
      (
        12
          *
        h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
      )
    )

theorem h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient_pos
    {δ : ℝ}
    (hδ : 0 < δ)
    (q : Fin 2) :
    0 <
      h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient
        δ q := by

  unfold
    h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient

  apply mul_pos

  · exact
      h3TerminalForcingThirdQMoment14RadialSquareHigherScale_pos
        q

  · apply Real.sqrt_pos.2

    exact
      div_pos
        hδ
        (
          mul_pos
            (by norm_num)
            h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient_pos
        )

theorem h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient_pos
    {δ : ℝ}
    (hδ : 0 < δ)
    (q : Fin 2) :
    0 <
      h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient
        δ q := by

  unfold
    h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient

  apply mul_pos

  · exact
      h3TerminalForcingFourthQMoment10RadialSquareHigherScale_pos
        q

  · apply Real.sqrt_pos.2

    exact
      div_pos
        hδ
        (
          mul_pos
            (by norm_num)
            h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient_pos
        )

/--
The second-q reciprocal-width profile is exactly a fixed positive coefficient
times the inverse square root of the width.
-/
theorem h3TerminalForcingThirdQHigherScale_sqrt_reciprocalWidth_eq_inverseSqrt
    {δ gap : ℝ}
    (hδ : 0 ≤ δ)
    (hGap : 0 < gap)
    (q : Fin 2) :
    h3TerminalForcingThirdQMoment14RadialSquareHigherScale q
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
            gap
          )
        )
      =
    h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient
        δ q
      /
    Real.sqrt gap := by

  have hBaseNonneg :
      0 ≤
        δ
          /
        (
          12
            *
          h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
        ) := by

    exact
      div_nonneg
        hδ
        (
          le_of_lt
            (
              mul_pos
                (by norm_num)
                h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient_pos
            )
        )

  unfold
    h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient

  rw [← div_div]

  rw [
    Real.sqrt_div
      hBaseNonneg
      gap
  ]

  ring

/--
The fourth-q reciprocal-width profile is exactly a fixed positive coefficient
times the inverse square root of the width.
-/
theorem h3TerminalForcingFourthQHigherScale_sqrt_reciprocalWidth_eq_inverseSqrt
    {δ gap : ℝ}
    (hδ : 0 ≤ δ)
    (hGap : 0 < gap)
    (q : Fin 2) :
    h3TerminalForcingFourthQMoment10RadialSquareHigherScale q
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
            gap
          )
        )
      =
    h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient
        δ q
      /
    Real.sqrt gap := by

  have hBaseNonneg :
      0 ≤
        δ
          /
        (
          12
            *
          h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
        ) := by

    exact
      div_nonneg
        hδ
        (
          le_of_lt
            (
              mul_pos
                (by norm_num)
                h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient_pos
            )
        )

  unfold
    h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient

  rw [← div_div]

  rw [
    Real.sqrt_div
      hBaseNonneg
      gap
  ]

  ring

end

end Euclidean
end Bridge
end PrimeTensor

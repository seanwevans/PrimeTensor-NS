import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch

/-!
# Quantitative radial-square channel domination

The two surviving resolved forcing branches select a fixed neighboring radial
square mass.  The older higher-radial bridge proves the corresponding scaled
component mass is bounded by an extended higher-radial moment.

This file packages those four concrete inequalities behind the two `Fin 2`
channel selectors.  Hence the reciprocal-width forcing rate and the
higher-radial quantity can now be compared at exactly the same selected times.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-- Fourier normalization attached to the third-q order-14/16 square channel. -/
noncomputable def h3TerminalForcingThirdQMoment14RadialSquareHigherScale
    (q : Fin 2) : ℝ :=
  if q = 0 then
    (2 * Real.pi) ^ 28
  else
    (2 * Real.pi) ^ 32

/--
The selected third-q order-14/16 radial-square channel is quantitatively
dominated, after its exact Fourier normalization, by its selected extended
higher-radial moment (shift `10` or `12`).
-/
theorem ofReal_scaled_h3TerminalForcingThirdQMoment14RadialSquareChannelAt_le_extendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (q : Fin 2) :
    ENNReal.ofReal
      (
        h3TerminalForcingThirdQMoment14RadialSquareHigherScale q
          *
        h3TerminalForcingThirdQMoment14RadialSquareChannelAt
          hH3 hClass ht j q
      )
      ≤
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass
      (h3TerminalForcingThirdQHigherRadialShift q)
      t
      ht := by

  fin_cases q

  · simpa [
      h3TerminalForcingThirdQMoment14RadialSquareHigherScale,
      h3TerminalForcingThirdQMoment14RadialSquareChannelAt,
      h3TerminalForcingThirdQHigherRadialShift
    ] using
      ofReal_scaled_h3TerminalForcingThirdQRawRadialSquareMass14_le_extendedHigherTen
        hH3 hClass ht j

  · simpa [
      h3TerminalForcingThirdQMoment14RadialSquareHigherScale,
      h3TerminalForcingThirdQMoment14RadialSquareChannelAt,
      h3TerminalForcingThirdQHigherRadialShift
    ] using
      ofReal_scaled_h3TerminalForcingThirdQRawRadialSquareMass16_le_extendedHigherTwelve
        hH3 hClass ht j

/-- Fourier normalization attached to the fourth-q order-10/12 square channel. -/
noncomputable def h3TerminalForcingFourthQMoment10RadialSquareHigherScale
    (q : Fin 2) : ℝ :=
  if q = 0 then
    (2 * Real.pi) ^ 20
  else
    (2 * Real.pi) ^ 24

/--
The selected fourth-q order-10/12 radial-square channel is quantitatively
dominated, after its exact Fourier normalization, by its selected extended
higher-radial moment (shift `6` or `8`).
-/
theorem ofReal_scaled_h3TerminalForcingFourthQMoment10RadialSquareChannelAt_le_extendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (q : Fin 2) :
    ENNReal.ofReal
      (
        h3TerminalForcingFourthQMoment10RadialSquareHigherScale q
          *
        h3TerminalForcingFourthQMoment10RadialSquareChannelAt
          hH3 hClass ht j q
      )
      ≤
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass
      (h3TerminalForcingFourthQHigherRadialShift q)
      t
      ht := by

  fin_cases q

  · simpa [
      h3TerminalForcingFourthQMoment10RadialSquareHigherScale,
      h3TerminalForcingFourthQMoment10RadialSquareChannelAt,
      h3TerminalForcingFourthQHigherRadialShift
    ] using
      ofReal_scaled_h3TerminalForcingFourthQRawRadialSquareMass10_le_extendedHigherSix
        hH3 hClass ht j

  · simpa [
      h3TerminalForcingFourthQMoment10RadialSquareHigherScale,
      h3TerminalForcingFourthQMoment10RadialSquareChannelAt,
      h3TerminalForcingFourthQHigherRadialShift
    ] using
      ofReal_scaled_h3TerminalForcingFourthQRawRadialSquareMass12_le_extendedHigherEight
        hH3 hClass ht j

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.Fourth.Forcing.Bound.Escape.StateMass.Group.Factor.Primitive

/-! Check that root and historical imports coexist and expose the public API. -/

open PrimeTensor.Bridge.Euclidean

#check h3TerminalFourthQForcingDerivativeMomentL1PrimitiveAt
#check h3TerminalFourthQForcingDerivativeMomentL1PrimitiveAt_nonneg
#check h3TerminalFourthQForcingDerivativeMomentL1ProductAt_eq_primitives
#check exists_fixed_h3TerminalFourthQForcingDerivativeMomentL1Primitive_subsequence_of_product_tendstoAtTop
#check fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedForcingDerivativePrimitiveMass

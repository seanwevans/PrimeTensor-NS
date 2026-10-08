import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Factors
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.RHS.Continuity

/-!
# Separate physical weighted PDE terms in Fourier L²

At every strict physical time, positive-time smoothing gives two actual
Fourier `L²` states for each coordinate:

    A_j = q³ û_j,
    B_j = q² F_j(U,U).

The derivative representative proved in the preceding checkpoint is their
negative sum.  Here we package the two terms separately.

This is the exact integrability input needed to split the restricted pairing
integral into the physical diffusion and nonlinear-transfer integrals.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailSeparatedPDETerms
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2500000

/--
At every strict physical time and for each velocity coordinate there exist
global Fourier `L²` states representing the separated weighted diffusion and
forcing terms `q³ û_j` and `q² F_j(U,U)`.
-/
theorem exists_h3TerminalPhysicalTopTailSeparatedWeightedPDETerms
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ∃ A B : H3FourierComplexL2,
      (
        ((A : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
            *
          (
            h3SpectralScalarRawFourierL2
              (U j)
          ) ξ)
      )
        ∧
      (
        ((B : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          h3RawFinLerayOuterProductDivergence
            U U j ξ)
      ) := by
  exact
    exists_h3TerminalPhysicalTopDissipationStrictTimeWeightedPDEFactors
      hH3 hClass ht j

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathTransportPressureL2SplitFrontier

/-!
# Recover physical fourth/fifth velocity L² jets from the closed Duhamel tail

The terminal Duhamel radial `L²` frontier is now closed.  Earlier reductions
already built a lossless chain from that statement back to the physical old
velocity jets:

    terminal tail radial L²
      -> complete Duhamel radial L²
      -> selected state radial L²
      -> ordered Fourier coordinate multipliers
      -> complex Fréchet coordinates
      -> real Fréchet coordinates
      -> selected fourth/fifth physical jets
      -> old-path fourth/fifth physical jets.

This file packages that entire chain as one reusable theorem.  The result is
needed next by the nonlinear transport branch: differentiated advection through
order three can now use the fourth/fifth physical `L²` jets without reopening
the spectral restart proof.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory

noncomputable section

/--
Every admissible H³ path automatically has physical `L²` fourth/fifth velocity
jets at every strict energy-class time.

The proof is purely compositional: all analytic work is supplied by the closed
selected terminal-tail radial theorem and the previously compiled transfer
bridges.
-/
theorem h3PathEnergyClassProducesFourthFifthVelocityJetMemLp2_closed :
    H3PathEnergyClassProducesFourthFifthVelocityJetMemLp2 := by

  have hTail :
      H3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius

  have hDuhamel :
      H3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_tail
      hTail

  have hRadial :
      H3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_duhamel
      hDuhamel

  have hMultiplier :
      H3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius_of_radial
      hRadial

  have hComplex :
      H3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius_of_rawCoordinateMultiplier
      hMultiplier

  have hReal :
      H3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius_of_complex
      hComplex

  have hSelected :
      H3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius_of_frechetRealPart
      hReal

  exact
    h3PathEnergyClassProducesFourthFifthVelocityJetMemLp2_of_selected
      hSelected

/-- The formerly open high-diffusion physical `L²` package is therefore also
closed outright. -/
theorem h3PathEnergyClassProducesHighDiffusionMemLp2_closed :
    H3PathEnergyClassProducesHighDiffusionMemLp2 := by
  exact
    h3PathEnergyClassProducesHighDiffusionMemLp2_of_fourthFifthVelocityJetMemLp2
      h3PathEnergyClassProducesFourthFifthVelocityJetMemLp2_closed

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedCanonicalRealMixedDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealTemporalDerivativeRegularity

/-!
# Classicalization: canonical real temporal derivative regularity

The canonical branch now has its own packaged real velocity field,

    h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity,

built from the modern restart-radius physical extension.  The historical
selected branch already proves that every real velocity component is
differentiable on the strict restart interval and that its ordinary derivative
is continuous there.

The modern and historical physical extensions are exactly equal.  This file
first transports that equality through `h3SpectralRealVelocityOfPath`, then
reuses the existing real temporal-regularity theorem verbatim.

No new estimate, differentiability argument, or continuity proof is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalRealTemporalDerivativeRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical packaged real velocity and the historical selected packaged
real velocity are exactly the same spacetime field. -/
theorem h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity_eq_mildSolutionAtRestartRadiusSelectedRealVelocity
    {nu A : ℝ}
    (hnu : 0 < nu)
    (U0 : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU0 : ‖U0‖ ≤ A) :
    h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
        hnu U0 hA hU0
      =
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hnu U0 hA hU0 := by
  unfold h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
  unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
  rw [
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_eq_mildSolutionAtRestartRadiusPhysicalExtension
      hnu U0 hA hU0
  ]

/-- On the whole strict relative restart interval, every component of the
canonical packaged real velocity is differentiable in time and has continuous
ordinary time derivative. -/
theorem h3SpectralFinHeatLerayRestartRadius_selectedRealVelocity_component_temporalDerivativeRegularity
    {nu A : ℝ}
    (hnu : 0 < nu)
    (U0 : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU0 : ‖U0‖ ≤ A)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    let f : ℝ → ℝ :=
      fun s : ℝ =>
        (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
          hnu U0 hA hU0 s x).component j
    let I : Set ℝ :=
      Set.Ioo
        0
        (h3FinHeatLerayRestartRadius nu A)
    DifferentiableOn ℝ f I
      ∧
    ContinuousOn (deriv f) I := by
  dsimp only

  have hOld :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_temporalDerivativeRegularity
      hnu U0 hA hU0 x j

  dsimp only at hOld

  have hVelocity :
      h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
          hnu U0 hA hU0
        =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hnu U0 hA hU0 :=
    h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity_eq_mildSolutionAtRestartRadiusSelectedRealVelocity
      hnu U0 hA hU0

  rw [hVelocity]
  exact hOld

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderTwoSelectedVelocityFourthCoordinateFourierL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path

/-!
# Physical L² continuity of selected fourth velocity coordinates

The preceding checkpoint closed strong Fourier `L²` continuity of every
ordered fourth selected velocity coordinate on the strict restart interval.

This file transports that path through the standard unitary reconstruction

    Fourier L²
      → inverse Plancherel
      → real part
      → `Point3`

to obtain strong physical real `L²` continuity.  No new estimate is needed:
all reconstruction maps are already continuous.

The next checkpoint can identify this canonical physical package a.e. with the
literal ordered fourth spatial derivative of the selected real velocity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory FourierTransform
open scoped ENNReal NNReal Topology FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedVelocityFourthCoordinatePhysicalL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical physical real `L²` reconstruction of one ordered fourth selected
velocity Fourier coordinate. -/
noncomputable def h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j : Fin 3)
    (a b c d : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ).symm
        (h3PreterminalSelectedVelocityFourthCoordinateFourierL2
          hNS ht₀ hE hTail q j a b c d)))

/-- Every ordered fourth selected velocity coordinate is strongly continuous
in physical real `L²` on the strict restart interval. -/
theorem continuous_h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2OnRestartRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3)
    (a b c d : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2
          hNS ht₀ hE hTail q j a b c d) := by

  unfold h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2

  exact
    continuous_h3FromFourierRealL2.comp
      (continuous_h3RealPartFourierL2.comp
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ).symm.continuous.comp
          (continuous_h3PreterminalSelectedVelocityFourthCoordinateFourierL2OnRestartRadius
            hNS ht₀ hE hTail j a b c d)))

end

end Euclidean
end Bridge
end PrimeTensor

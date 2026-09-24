import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderThreeSelectedVelocityFifthCoordinateFourierL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path

/-!
# Physical L² continuity of selected fifth velocity coordinates

The preceding checkpoint closed strong Fourier `L²` continuity of every
ordered fifth selected velocity coordinate on the strict restart interval.

This file transports that path through the standard unitary reconstruction

    Fourier L²
      → inverse Plancherel
      → real part
      → `Point3`

to obtain strong physical real `L²` continuity.  No new estimate is needed:
all reconstruction maps are already continuous.

The next checkpoint can identify this canonical physical package a.e. with the
literal ordered fifth spatial derivative of the selected real velocity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory FourierTransform
open scoped ENNReal NNReal Topology FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedVelocityFifthCoordinatePhysicalL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical physical real `L²` reconstruction of one ordered fifth selected
velocity Fourier coordinate. -/
noncomputable def h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2
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
    (a b c d e : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ).symm
        (h3PreterminalSelectedVelocityFifthCoordinateFourierL2
          hNS ht₀ hE hTail q j a b c d e)))

/-- Every ordered fifth selected velocity coordinate is strongly continuous
in physical real `L²` on the strict restart interval. -/
theorem continuous_h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2OnRestartRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3)
    (a b c d e : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2
          hNS ht₀ hE hTail q j a b c d e) := by

  unfold h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2

  exact
    continuous_h3FromFourierRealL2.comp
      (continuous_h3RealPartFourierL2.comp
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ).symm.continuous.comp
          (continuous_h3PreterminalSelectedVelocityFifthCoordinateFourierL2OnRestartRadius
            hNS ht₀ hE hTail j a b c d e)))

end

end Euclidean
end Bridge
end PrimeTensor

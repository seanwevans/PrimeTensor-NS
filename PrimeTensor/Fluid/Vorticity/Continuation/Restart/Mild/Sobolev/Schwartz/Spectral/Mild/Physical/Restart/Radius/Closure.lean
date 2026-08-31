import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Mild.Physical.Restart.Finite.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Restart.Radius

/-!
# Physical closure at the canonical H³ restart radius

The restart stack now has a mesh-independent physical realization theorem for
arbitrary positive elapsed times lying inside a selected mild interval.  The
existing H³ restart-radius module supplies a canonical positive interval length
depending only on the viscosity and the H³ size bound.

This file joins those two interfaces.  It packages the canonical real restart
radius as an `NNReal`, defines the corresponding globally indexed selected mild
extension, and proves that the complete canonical-radius step has the exact
physical heat-minus-remainder decomposition whose positive nonlinear remainder
is in the Schwartz heat--Leray physical-realization set.

This is the form needed by the uniform-lifespan continuation frontier: the
elapsed time is no longer an auxiliary small parameter.  It is the concrete
positive radius determined by the H³ bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- The canonical H³ restart radius, bundled as a nonnegative real. -/
def h3FinHeatLerayRestartRadiusNN
    (ν A : ℝ)
    (hA : 0 < A) : NNReal :=
  ⟨h3FinHeatLerayRestartRadius ν A,
    (h3FinHeatLerayRestartRadius_pos ν hA).le⟩

@[simp]
theorem h3FinHeatLerayRestartRadiusNN_coe
    (ν A : ℝ)
    (hA : 0 < A) :
    ((h3FinHeatLerayRestartRadiusNN ν A hA : NNReal) : ℝ)
      = h3FinHeatLerayRestartRadius ν A :=
  rfl

/-- The bundled canonical restart radius is strictly positive. -/
theorem h3FinHeatLerayRestartRadiusNN_pos
    (ν A : ℝ)
    (hA : 0 < A) :
    0 < h3FinHeatLerayRestartRadiusNN ν A hA := by
  change 0 < h3FinHeatLerayRestartRadius ν A
  exact h3FinHeatLerayRestartRadius_pos ν hA

/-- The globally indexed physical-time extension of the selected mild solution
on the canonical H³ restart interval. -/
noncomputable def h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    ℝ → H3SpectralVelocityState :=
  h3SpectralFinHeatLerayMildSolutionPhysicalExtension
    hν
    (h3FinHeatLerayRestartRadius_pos ν hA).le
    U₀ hA hU₀
    (h3FinHeatLerayRestartRadius_smallness ν hA.le)

/-- The complete canonical-radius mild step has a physical
heat-minus-remainder representation, and its positive nonlinear remainder is
realized by the Schwartz heat--Leray closure constructed above. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_fullStep_realized
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    let T : NNReal := h3FinHeatLerayRestartRadiusNN ν A hA
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let R : H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν 0 hν W W T
    h3SpectralFinVectorDecodeComplexL2 (W (T : ℝ))
        = h3ComplexPhysicalVelocityHeatApplyNN ν hν.le T (W 0)
          - h3SpectralFinVectorDecodeComplexL2 R
      ∧
    h3SpectralFinVectorDecodeComplexL2 R
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
            ν (T : ℝ) hν := by
  dsimp only
  let T : NNReal := h3FinHeatLerayRestartRadiusNN ν A hA
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  let R : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder
      ν 0 hν W W T

  have hT : 0 < T := by
    dsimp only [T]
    exact h3FinHeatLerayRestartRadiusNN_pos ν A hA

  have hStep0 :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restart_decodeComplexL2_realized
      (τ := h3FinHeatLerayRestartRadius ν A)
      (a := 0)
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      T
      (by norm_num)
      hT
      (by
        dsimp only [T]
        rw [h3FinHeatLerayRestartRadiusNN_coe]
        simpa only [zero_add] using
          (le_refl (h3FinHeatLerayRestartRadius ν A)))

  simpa only [
    T,
    W,
    R,
    zero_add,
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
  ] using hStep0

end

end Euclidean
end Bridge
end PrimeTensor

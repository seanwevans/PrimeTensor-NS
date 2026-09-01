import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.SelectedPhysicalL2Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Retarded.Integrability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Mild.Physical.Restart.Radius.Closure

/-!
# Automatic physical L² closure for the selected Duhamel coordinate

`SelectedPhysicalL2Representative` identifies the canonical selected pointwise
`C¹` reconstruction almost everywhere with the source-time physical `L²`
Bochner integral, under an explicit spectral `IntervalIntegrable` premise.

For the canonical restart-radius selected mild path that premise is not an
extra hypothesis.  The globally indexed physical-time extension is continuous
and uniformly bounded by `2 * A`, while the retarded heat--Leray integrability
theorem turns precisely those two facts into genuine Bochner interval
integrability.

This file discharges that premise once and then exposes the resulting selected
physical `L²` representative theorem without an auxiliary integrability
assumption.

No new estimate, Fourier interchange, or point evaluation of an `L²` class is
used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailSelectedPhysicalL2Closure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual selected restart-radius mild path makes its spectral Duhamel
integrand genuinely interval integrable at every nonnegative target time. -/
theorem h3SelectedDuhamelIntegrand_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 ≤ t) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntervalIntegrable
      (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W)
      volume
      0
      t := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)

  have hWcont : Continuous W := by
    simpa only [
      W,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWb.1

  have hWbound : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    simpa only [
      W,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWb.2 s

  have htwoA : 0 ≤ 2 * A :=
    mul_nonneg (by norm_num) hA.le

  dsimp only
  exact
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν ht htwoA htwoA W W hWcont hWcont
      (fun s _ => hWbound s)
      (fun s _ => hWbound s)

/-- For the canonical selected restart-radius path, the pointwise `C¹`
Duhamel reconstruction is automatically an a.e. representative of the
source-time-integrated physical `L²` Duhamel coordinate. -/
theorem h3SelectedDuhamelC1Representative_ae_eq_physicalL2Duhamel_closed
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SelectedDuhamelC1Representative
        ν A t hν U₀ hA hU₀ ht i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel
        ν t hν W W i : H3ComplexPhysicalScalarL2) :
      H3FourierPoint3 → ℂ) := by
  have hInt :=
    h3SelectedDuhamelIntegrand_intervalIntegrable
      hν U₀ hA hU₀ ht.le

  exact
    h3SelectedDuhamelC1Representative_ae_eq_physicalL2Duhamel
      hν U₀ hA hU₀ ht hInt i

end

end Euclidean
end Bridge
end PrimeTensor

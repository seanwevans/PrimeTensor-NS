import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Selected.Physical.L2.Vector.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Physical.L2.Time.Integrability

/-!
# Selected physical L² Duhamel source-time integrability

The generic physical `L²` retarded path is interval integrable whenever the
spectral Duhamel integrand is interval integrable.

For the canonical selected restart-radius path, that spectral premise has
already been discharged in `SelectedPhysicalL2Closure`.  This file records the
corresponding automatic source-time integrability of every physical `L²`
coordinate and specializes the existing a.e.-in-source-time representative
theorem to the same selected path.

These are the two direct inputs for the later Bochner/Fubini representative
bridge:

* genuine source-time Banach-space integrability of the endpoint-safe physical
  `L²` retarded path;
* for almost every source time, the classical positive-lag `C³`
  reconstruction represents that `L²` class almost everywhere in space.

No new estimate or Fourier interchange is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailSelectedPhysicalL2TimeIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every coordinate of the endpoint-safe selected physical `L²` retarded
Duhamel path is automatically interval integrable in source time. -/
theorem h3SelectedPhysicalL2RetardedIntegrand_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 ≤ t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntervalIntegrable
      (h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand
        ν t hν W W i)
      volume
      0
      t := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W)
        volume
        0
        t := by
    simpa only [W] using
      (h3SelectedDuhamelIntegrand_intervalIntegrable
        hν U₀ hA hU₀ ht)

  dsimp only
  exact
    h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand_intervalIntegrable
      hν W W hInt i

/-- For the canonical selected path, at almost every source time in `(0,t]`
the classical positive-lag `C³` retarded forcing is a spatial a.e.
representative of the endpoint-safe physical `L²` retarded integrand. -/
theorem ae_h3SelectedDuhamelC3RetardedPath_eq_physicalL2RetardedIntegrand
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ∀ᵐ s : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)),
      (fun x : H3FourierPoint3 =>
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t W W i x s)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand
          ν t hν W W i s : H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  dsimp only
  exact
    ae_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_eq_physicalL2RetardedIntegrand
      hν W W i

end

end Euclidean
end Bridge
end PrimeTensor

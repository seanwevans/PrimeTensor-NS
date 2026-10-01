import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Intertwining
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.C0.Time.Integrability

/-!
# Physical intertwining for the positive Duhamel integrand

The fixed positive-lag nonlinear heat reconstruction is already known to agree
almost everywhere with the complex physical decoder of the actual spectral
heat--Leray kernel.

This file inserts that theorem into the endpoint-safe retarded Duhamel
integrand.  At every strict source time `s < t`, the branch condition
`0 < t - s` is automatic, so the spectral Duhamel integrand reduces to the
positive-lag heat--Leray operator and its decoded coordinate has exactly the
classical `C³` retarded representative.

This is the local equality needed before commuting the physical realization
through the source-time integral.  The Duhamel operator remains positive; the
Navier--Stokes minus sign is external to this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailPhysicalIntertwining
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every strict source time, the classical positive-lag nonlinear
reconstruction is an a.e. representative of the decoded spectral Duhamel
integrand, coordinatewise. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_ae_eq_duhamelIntegrandDecode_of_lt
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν (t - s) (U s) (V s) i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3SpectralScalarDecodeComplexL2
        ((h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V s) i) : H3ComplexPhysicalScalarL2) :
      H3FourierPoint3 → ℂ) := by
  have hlag : 0 < t - s := sub_pos.mpr hs
  rw [h3SpectralFinHeatLerayDuhamelIntegrand, dif_pos hlag]
  exact
    h3RawFinLerayOuterProductDivergenceHeatC3Representative_ae_eq_heatLerayDecodeComplexL2
      hν hlag (U s) (V s) i

/-- The same equality stated under the named classical retarded path. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_ae_eq_duhamelIntegrandDecode_of_lt
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3) :
    (fun x : H3FourierPoint3 =>
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x s)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun x : H3FourierPoint3 =>
      ((h3SpectralScalarDecodeComplexL2
          ((h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s) i) : H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ) x) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
  simpa only using
    (h3RawFinLerayOuterProductDivergenceHeatC3Representative_ae_eq_duhamelIntegrandDecode_of_lt
      hν hs U V i)

end

end Euclidean
end Bridge
end PrimeTensor

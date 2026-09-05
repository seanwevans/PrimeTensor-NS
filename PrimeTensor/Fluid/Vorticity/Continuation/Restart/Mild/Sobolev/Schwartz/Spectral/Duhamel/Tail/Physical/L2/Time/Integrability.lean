import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Physical.L2.Representative

/-!
# Source-time integrability of the physical L² Duhamel path

The endpoint-safe physical `L²` retarded integrand is exactly the decoded
spectral Duhamel integrand at every source time.

Hence the existing spectral interval-integrability hypothesis transports
through the bounded complex decoder and finite coordinate projection with no
new estimate.  This is the Banach-space integrability input needed for the
final Bochner/Fubini representative theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailPhysicalL2TimeIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Spectral Duhamel interval integrability implies interval integrability of
each endpoint-safe physical `L²` retarded coordinate. -/
theorem h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand_intervalIntegrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t)
    (i : Fin 3) :
    IntervalIntegrable
      (h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand
        ν t hν U V i)
      volume
      0
      t := by
  have hVectorDecoded :
      IntervalIntegrable
        (fun s : ℝ =>
          h3SpectralFinVectorDecodeComplexL2
            (h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s))
        volume
        0
        t := by
    constructor
    · exact
        h3SpectralFinVectorDecodeComplexL2CLM.integrable_comp hInt.1
    · exact
        h3SpectralFinVectorDecodeComplexL2CLM.integrable_comp hInt.2

  let πi :
      H3ComplexPhysicalFinVectorL2 →L[ℂ] H3ComplexPhysicalScalarL2 :=
    ContinuousLinearMap.proj i

  have hScalarDecoded :
      IntervalIntegrable
        (fun s : ℝ =>
          h3SpectralScalarDecodeComplexL2
            ((h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s) i))
        volume
        0
        t := by
    constructor
    · change
        Integrable
          (fun s : ℝ =>
            πi
              (h3SpectralFinVectorDecodeComplexL2
                (h3SpectralFinHeatLerayDuhamelIntegrand
                  ν t hν U V s)))
          (volume.restrict (Set.Ioc (0 : ℝ) t))
      exact πi.integrable_comp hVectorDecoded.1
    · change
        Integrable
          (fun s : ℝ =>
            πi
              (h3SpectralFinVectorDecodeComplexL2
                (h3SpectralFinHeatLerayDuhamelIntegrand
                  ν t hν U V s)))
          (volume.restrict (Set.Ioc t (0 : ℝ)))
      exact πi.integrable_comp hVectorDecoded.2

  have hEq :
      h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand
          ν t hν U V i
        =
      fun s : ℝ =>
        h3SpectralScalarDecodeComplexL2
          ((h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s) i) := by
    funext s
    exact
      h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand_eq_duhamelIntegrandDecode
        hν U V i s

  rw [hEq]
  exact hScalarDecoded

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.DecodedCoordinateIntegral
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Intertwining

/-!
# Exact physical L² realization of the positive Duhamel coordinate

The fixed positive-lag nonlinear forcing already has a canonical physical `L²`
object,

    h3RawFinLerayOuterProductDivergenceHeatPhysicalL2,

and `Heat.Intertwining` identifies the deweighted Fourier `L²` state of the
actual spectral heat--Leray operator with the raw heat-forcing package.

This file records the resulting exact physical-`L²` equality, then gives the
physical retarded path the same endpoint-safe `dif` convention used by the
spectral Duhamel integrand.  Consequently the two integrands are exactly equal
as `L²` elements at every source time, including the endpoint.

Integrating in source time therefore gives an exact quotient-safe identity:

    physical-L² Duhamel coordinate
      =
    decode (spectral Duhamel coordinate).

No spatial point evaluation and no Fubini interchange is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailPhysicalL2Integral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical positive-lag physical `L²` reconstruction is exactly the
existing decoder of the actual spectral heat--Leray operator. -/
theorem h3RawFinLerayOuterProductDivergenceHeatPhysicalL2_eq_heatLerayDecodeComplexL2
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceHeatPhysicalL2
        ν τ hν hτ U V i
      =
    h3SpectralScalarDecodeComplexL2
      (h3SpectralFinHeatLerayVelocityApply
        ν τ hν hτ U V i) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatPhysicalL2
  unfold h3SpectralScalarDecodeComplexL2
  rw [
    h3SpectralFinHeatLerayVelocityApply_rawFourierL2_eq_rawHeatForcingL2
      hν hτ U V i
  ]

/-- Endpoint-safe physical `L²` retarded nonlinear integrand.  Its endpoint
convention deliberately mirrors `h3SpectralFinHeatLerayDuhamelIntegrand`. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand
    (ν t : ℝ)
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (s : ℝ) :
    H3ComplexPhysicalScalarL2 :=
  if hlag : 0 < t - s then
    h3RawFinLerayOuterProductDivergenceHeatPhysicalL2
      ν (t - s) hν hlag (U s) (V s) i
  else
    0

/-- The endpoint-safe physical `L²` retarded integrand is exactly the decoder
of the spectral Duhamel integrand at every source time. -/
theorem h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand_eq_duhamelIntegrandDecode
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (s : ℝ) :
    h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand
        ν t hν U V i s
      =
    h3SpectralScalarDecodeComplexL2
      ((h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U V s) i) := by
  by_cases hlag : 0 < t - s
  · rw [
      h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand,
      dif_pos hlag,
      h3SpectralFinHeatLerayDuhamelIntegrand,
      dif_pos hlag
    ]
    exact
      h3RawFinLerayOuterProductDivergenceHeatPhysicalL2_eq_heatLerayDecodeComplexL2
        hν hlag (U s) (V s) i
  · rw [
      h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand,
      dif_neg hlag,
      h3SpectralFinHeatLerayDuhamelIntegrand,
      dif_neg hlag
    ]
    simp

/-- Source-time Bochner integral of the endpoint-safe physical `L²` retarded
coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel
    (ν t : ℝ)
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3) :
    H3ComplexPhysicalScalarL2 :=
  ∫ s in (0 : ℝ)..t,
    h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand
      ν t hν U V i s

/-- The physical `L²` Duhamel coordinate is exactly the decoder of the actual
spectral Duhamel coordinate. -/
theorem h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel_eq_decodeComplexL2
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
    h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel
        ν t hν U V i
      =
    h3SpectralScalarDecodeComplexL2
      ((h3SpectralFinHeatLerayDuhamel ν t hν U V) i) := by
  rw [
    h3SpectralScalarDecodeComplexL2_duhamel_eq_intervalIntegral
      hν U V hInt i
  ]
  unfold h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel
  apply intervalIntegral.integral_congr
  intro s hs
  exact
    h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand_eq_duhamelIntegrandDecode
      hν U V i s

end

end Euclidean
end Bridge
end PrimeTensor

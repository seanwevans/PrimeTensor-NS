import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Physical.L2.Integral

/-!
# Classical representative of the endpoint-safe physical L² Duhamel integrand

`PhysicalL2Integral` constructed an endpoint-safe physical `L²` retarded path
which is exactly the decoded spectral Duhamel integrand at every source time.

At every strict source time `s < t`, the classical positive-lag `C³`
reconstruction is already known to be an almost-everywhere representative of
the canonical physical `L²` heat reconstruction.  This file transports that
fixed-lag compatibility to the endpoint-safe retarded path.

The terminal source time `s = t` is excluded pointwise and then restored
almost everywhere on `(0,t]`, since the terminal singleton has zero Lebesgue
measure.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailPhysicalL2Representative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every strict source time, the classical retarded `C³` forcing is an
a.e. representative of the endpoint-safe physical `L²` retarded integrand. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_ae_eq_physicalL2RetardedIntegrand_of_lt
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3) :
    (fun x : H3FourierPoint3 =>
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x s)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand
        ν t hν U V i s : H3ComplexPhysicalScalarL2) :
      H3FourierPoint3 → ℂ) := by
  have hlag : 0 < t - s := sub_pos.mpr hs
  rw [
    h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand,
    dif_pos hlag
  ]
  unfold h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
  exact
    h3RawFinLerayOuterProductDivergenceHeatC3Representative_ae_eq_physicalL2
      hν hlag (U s) (V s) i

/-- On the full source interval `(0,t]`, the classical retarded path is an
a.e.-in-source-time family of spatial a.e. representatives of the endpoint-safe
physical `L²` retarded integrand. -/
theorem ae_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_eq_physicalL2RetardedIntegrand
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3) :
    ∀ᵐ s : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)),
      (fun x : H3FourierPoint3 =>
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t U V i x s)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((h3RawFinLerayOuterProductDivergenceHeatPhysicalL2RetardedIntegrand
          ν t hν U V i s : H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ) := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with s hs
  exact
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_ae_eq_physicalL2RetardedIntegrand_of_lt
      hν hs.2 U V i

end

end Euclidean
end Bridge
end PrimeTensor

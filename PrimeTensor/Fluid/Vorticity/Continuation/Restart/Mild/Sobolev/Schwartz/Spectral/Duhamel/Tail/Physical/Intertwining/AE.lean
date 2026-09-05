import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.PhysicalIntertwining

/-!
# Source-time almost-everywhere physical Duhamel intertwining

The strict-source-time bridge identifies the classical retarded nonlinear
forcing with the decoded spectral Duhamel integrand whenever `s < t`.

The spectral integrand is endpoint-safe and is defined to be zero at `s = t`,
whereas the classical retarded representative takes the instantaneous forcing
value.  These two endpoint conventions therefore do not agree pointwise.

For source-time integration this discrepancy is immaterial: the singleton
`{t}` has zero Lebesgue measure.  This file packages the strict bridge as an
almost-everywhere statement on the full oriented Duhamel source interval
`(0,t]`.

No new estimate or continuity argument is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailPhysicalIntertwiningAE
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On the full source-time interval `(0,t]`, the only possible mismatch
between the classical retarded path and the decoded endpoint-safe spectral
integrand is the terminal singleton.  Hence the two agree for almost every
source time, with spatial equality understood almost everywhere. -/
theorem ae_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_eq_duhamelIntegrandDecode
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3) :
    ∀ᵐ s : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) t)),
      (fun x : H3FourierPoint3 =>
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t U V i x s)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun x : H3FourierPoint3 =>
        ((h3SpectralScalarDecodeComplexL2
            ((h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s) i) : H3ComplexPhysicalScalarL2) :
          H3FourierPoint3 → ℂ) x) := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with s hs
  exact
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_ae_eq_duhamelIntegrandDecode_of_lt
      hν hs.2 U V i

end

end Euclidean
end Bridge
end PrimeTensor

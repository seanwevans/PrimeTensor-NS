import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralFinHeatLerayDuhamelRawFourierL2

/-!
# Classicalization: pointwise representative of the raw Fourier Duhamel kernel

`SpectralFinHeatLerayDuhamelRawFourierL2` identifies exact H³ deweighting of
the Banach-valued heat--Leray Duhamel state with an interval integral of
Fourier `L²` source kernels.

This file records the explicit almost-everywhere representative of each such
source kernel.  At positive retarded lag it is exactly

    ξ ↦ H_{t-s}(ξ) N(U(s),V(s))(ξ),

and at the singular endpoint it is zero, matching the endpoint-safe spectral
Duhamel integrand.

This is the fixed-source-time bridge needed before commuting the source-time
integral through Fourier representatives.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SpectralFinHeatLerayDuhamelRawFourierRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Endpoint-safe pointwise raw Fourier representative of one heat--Leray
Duhamel source kernel. -/
noncomputable def h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (s : ℝ)
    (ξ : H3FourierPoint3) : ℂ :=
  if _hs : 0 < t - s then
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
      ν (t - s) (U s) (V s) i ξ
  else
    0

/-- Every quotient-safe raw Fourier `L²` Duhamel source kernel has the explicit
endpoint-safe raw Fourier integrand as an almost-everywhere representative. -/
theorem h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_ae
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (s : ℝ) :
    ((h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
        ν t hν U V i s : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
      ν t U V i s := by
  by_cases hs : 0 < t - s

  · have hRaw :=
      MemLp.coeFn_toLp
        (h3RawFinLerayOuterProductDivergenceHeatRepresentative_memLp2
          hν hs (U s) (V s) i)

    filter_upwards [hRaw] with ξ hξ

    simp only [
      h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand,
      h3SpectralFinHeatLerayDuhamelRawFourierIntegrand,
      hs
    ]

    unfold h3RawFinLerayOuterProductDivergenceHeatFourierL2
    exact hξ

  · refine Filter.Eventually.of_forall ?_
    intro ξ

    simp [
      h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand,
      h3SpectralFinHeatLerayDuhamelRawFourierIntegrand,
      hs
    ]

/-- On the open source-time interval, the representative is literally the
retarded heat symbol times the raw Leray-projected quadratic forcing. -/
theorem h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_ae_of_mem_Ioo
    {ν t s : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (0 : ℝ) t) :
    ((h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
        ν t hν U V i s : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3HeatFourierSymbol ν (t - s) ξ *
        h3RawFinLerayOuterProductDivergence
          (U s) (V s) i ξ) := by
  have hlag : 0 < t - s := sub_pos.mpr hs.2

  have h :=
    h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_ae
      (ν := ν) (t := t) hν U V i s

  filter_upwards [h] with ξ hξ

  simpa [
    h3SpectralFinHeatLerayDuhamelRawFourierIntegrand,
    hlag,
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
  ] using hξ

end

end Euclidean
end Bridge
end PrimeTensor

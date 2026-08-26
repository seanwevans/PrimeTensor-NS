import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Leray.Physical.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel

/-!
# Physical control of the retarded heat--Leray Duhamel term

The instantaneous positive-time heat--Leray nonlinearity has already been
shown to decode into the physical `L²` closure of genuine Schwartz-product
anchors.  This file crosses the first part of the retarded-time boundary.

First, the finite-vector spectral decoder is norm-contracting.  Second, at
every strict pre-endpoint time `s < t`, the endpoint-safe Duhamel integrand
reduces to the positive-lag heat--Leray kernel, so its decoded value belongs to
the corresponding Schwartz heat--Leray physical closure.  Finally, the
existing square-root-time spectral Duhamel estimate passes immediately through
the contractive decoder.

The remaining step after this checkpoint is closure under the Bochner interval
integral itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Coordinatewise complex physical decoding of a finite weighted H³ spectral
vector does not increase the finite-product norm. -/
theorem norm_h3SpectralFinVectorDecodeComplexL2_le
    (W : H3SpectralFinVectorState) :
    ‖h3SpectralFinVectorDecodeComplexL2 W‖ ≤ ‖W‖ := by
  have hnonneg : 0 ≤ ‖W‖ := norm_nonneg _
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro i
  calc
    ‖h3SpectralFinVectorDecodeComplexL2 W i‖
        = ‖h3SpectralScalarDecodeComplexL2 (W i)‖ := rfl
    _ ≤ ‖W i‖ := norm_h3SpectralScalarDecodeComplexL2_le (W i)
    _ ≤ ‖W‖ := h3SpectralFinVector_coordinate_norm_le W i

/-- At every strict pre-endpoint time, the decoded retarded integrand belongs
to the physical closure of genuine Schwartz heat--Leray anchors at lag
`t - s`. -/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_decodeComplexL2_mem_closure
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (U V : ℝ → H3SpectralFinVectorState) :
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V s)
      ∈ closure
        {u : H3ComplexPhysicalFinVectorL2 |
          H3SchwartzHeatLerayPhysicalFinVectorL2Anchor
            ν (t - s) hν (sub_pos.mpr hs) u} := by
  have hlag : 0 < t - s := sub_pos.mpr hs
  rw [h3SpectralFinHeatLerayDuhamelIntegrand, dif_pos hlag]
  simpa only using
    (h3SpectralFinHeatLerayVelocity_decodeComplexL2_mem_closure
      hν hlag (U s) (V s))

/-- The concrete square-root-time Duhamel estimate survives exact physical
complex decoding. -/
theorem norm_h3SpectralFinHeatLerayDuhamel_decodeComplexL2_le
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t)
    (hU :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖U s‖ ≤ MU)
    (hV :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖V s‖ ≤ MV) :
    ‖h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamel ν t hν U V)‖
      ≤
    h3HeatLerayDuhamelCoefficient ν *
      Real.sqrt t * MU * MV := by
  exact
    (norm_h3SpectralFinVectorDecodeComplexL2_le
      (h3SpectralFinHeatLerayDuhamel ν t hν U V)).trans
      (norm_h3SpectralFinHeatLerayDuhamel_le
        hν ht hMU hMV U V hInt hU hV)

end

end Euclidean
end Bridge
end PrimeTensor

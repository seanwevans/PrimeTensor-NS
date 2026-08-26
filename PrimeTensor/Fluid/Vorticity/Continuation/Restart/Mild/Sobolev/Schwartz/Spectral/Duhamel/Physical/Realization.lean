import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Closed.Convex.Hull

/-!
# Unnormalized physical realization of the heat--Leray Duhamel term

The preceding checkpoint places the normalized decoded Duhamel term

    t⁻¹ • decode (Duhamel t)

in the closed real convex hull of genuine positive-lag Schwartz heat--Leray
anchors.  For the mild equation it is more convenient to remove that
normalization completely.

This file packages the corresponding unnormalized realization set and proves
both its direct membership form and an epsilon approximation form.  Thus the
physical Duhamel term can be approximated arbitrarily well by `t` times an
actual member of the finite real convex hull of genuine Schwartz heat--Leray
anchors.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Unnormalized physical realization set for the Duhamel term at time `t`:
`t` times the closed real convex hull of all genuine positive-lag Schwartz
heat--Leray anchors available up to `t`. -/
def H3SchwartzHeatLerayDuhamelPhysicalRealization
    (ν t : ℝ)
    (hν : 0 < ν) :
    Set H3ComplexPhysicalFinVectorL2 :=
  {u : H3ComplexPhysicalFinVectorL2 |
    ∃ v : H3ComplexPhysicalFinVectorL2,
      v ∈ H3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull ν t hν ∧
        u = t • v}

/-- Multiplying the normalized closed-convex realization by the positive final
time recovers the decoded Duhamel term itself. -/
theorem h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_physicalRealization
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t) :
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamel ν t hν U V)
      ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν t hν := by
  let x : H3ComplexPhysicalFinVectorL2 :=
    h3SpectralFinVectorDecodeComplexL2
      (h3SpectralFinHeatLerayDuhamel ν t hν U V)

  have hnorm :
      t⁻¹ • x
        ∈ H3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull ν t hν := by
    dsimp [x]
    exact
      h3SpectralFinHeatLerayDuhamel_decodeComplexL2_normalized_mem_closedConvexHull
        hν ht U V hInt

  refine ⟨t⁻¹ • x, hnorm, ?_⟩
  have ht0 : t ≠ 0 := ne_of_gt ht
  dsimp [x]
  calc
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamel ν t hν U V)
        = (1 : ℝ) •
            h3SpectralFinVectorDecodeComplexL2
              (h3SpectralFinHeatLerayDuhamel ν t hν U V) := by simp
    _ = (t * t⁻¹) •
          h3SpectralFinVectorDecodeComplexL2
            (h3SpectralFinHeatLerayDuhamel ν t hν U V) := by
          rw [mul_inv_cancel₀ ht0]
    _ = t •
          (t⁻¹ •
            h3SpectralFinVectorDecodeComplexL2
              (h3SpectralFinHeatLerayDuhamel ν t hν U V)) := by
          rw [smul_smul]

/-- Epsilon form of the unnormalized realization: the decoded Duhamel term is
arbitrarily close to `t` times an actual point of the finite real convex hull
of genuine positive-lag Schwartz heat--Leray anchors. -/
theorem exists_h3SchwartzHeatLerayDuhamel_convexHull_dist_lt
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ v : H3ComplexPhysicalFinVectorL2,
      v ∈ convexHull ℝ
        (H3SchwartzHeatLerayDuhamelPhysicalAnchorRange ν t hν) ∧
      dist
        (h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayDuhamel ν t hν U V))
        (t • v) < ε := by
  let x : H3ComplexPhysicalFinVectorL2 :=
    h3SpectralFinVectorDecodeComplexL2
      (h3SpectralFinHeatLerayDuhamel ν t hν U V)

  have hnorm :
      t⁻¹ • x
        ∈ closure
          (convexHull ℝ
            (H3SchwartzHeatLerayDuhamelPhysicalAnchorRange ν t hν)) := by
    simpa [H3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull] using
      (h3SpectralFinHeatLerayDuhamel_decodeComplexL2_normalized_mem_closedConvexHull
        hν ht U V hInt)

  rw [Metric.mem_closure_iff] at hnorm
  have hδ : 0 < ε / t := div_pos hε ht
  obtain ⟨v, hv, hdist⟩ := hnorm (ε / t) hδ
  refine ⟨v, hv, ?_⟩

  have ht0 : t ≠ 0 := ne_of_gt ht
  have hx : x = t • (t⁻¹ • x) := by
    calc
      x = (1 : ℝ) • x := by simp
      _ = (t * t⁻¹) • x := by rw [mul_inv_cancel₀ ht0]
      _ = t • (t⁻¹ • x) := by rw [smul_smul]

  change dist x (t • v) < ε
  rw [hx, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht]
  rw [dist_eq_norm] at hdist
  calc
    t * ‖t⁻¹ • x - v‖ < t * (ε / t) :=
      mul_lt_mul_of_pos_left hdist ht
    _ = ε := by field_simp [ht0]

/-- Automatic unnormalized physical realization on the continuous globally
bounded restart-path class. -/
theorem h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_physicalRealization_of_continuous
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamel ν t hν U V)
      ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν t hν := by
  let x : H3ComplexPhysicalFinVectorL2 :=
    h3SpectralFinVectorDecodeComplexL2
      (h3SpectralFinHeatLerayDuhamel ν t hν U V)

  have hnorm :
      t⁻¹ • x
        ∈ H3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull ν t hν := by
    dsimp [x]
    exact
      h3SpectralFinHeatLerayDuhamel_decodeComplexL2_normalized_mem_closedConvexHull_of_continuous
        hν ht hMU hMV U V hUcont hVcont hU hV

  refine ⟨t⁻¹ • x, hnorm, ?_⟩
  have ht0 : t ≠ 0 := ne_of_gt ht
  dsimp [x]
  calc
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamel ν t hν U V)
        = (1 : ℝ) •
            h3SpectralFinVectorDecodeComplexL2
              (h3SpectralFinHeatLerayDuhamel ν t hν U V) := by simp
    _ = (t * t⁻¹) •
          h3SpectralFinVectorDecodeComplexL2
            (h3SpectralFinHeatLerayDuhamel ν t hν U V) := by
          rw [mul_inv_cancel₀ ht0]
    _ = t •
          (t⁻¹ •
            h3SpectralFinVectorDecodeComplexL2
              (h3SpectralFinHeatLerayDuhamel ν t hν U V)) := by
          rw [smul_smul]

end

end Euclidean
end Bridge
end PrimeTensor

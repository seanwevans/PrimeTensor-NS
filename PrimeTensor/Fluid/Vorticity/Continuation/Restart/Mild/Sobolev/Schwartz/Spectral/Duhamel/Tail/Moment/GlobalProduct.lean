import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.SelectedPhysicalL2TimeIntegrability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterFullFubini

/-!
# Global product integrability of the selected terminal-tail raw kernel

`LocalProduct` proves product integrability of the selected terminal-half raw
Fourier kernel on every finite-measure frequency set.  The later `9/4`
endpoint branch proves genuine product integrability of the same kernel after
multiplication by `|ξ|^(9/4)`.

Those two facts cover the full Fourier space.

* On the closed unit ball, finite-measure `L² -> L¹` is enough.
* Outside the unit ball, `1 ≤ |ξ|^(9/4)`, so the unweighted kernel is dominated
  by the already-integrable `9/4`-weighted kernel.

This file packages that low/high decomposition and obtains global product
integrability on

    (t/2,t) × H3FourierPoint3.

This is the absolute-integrability input required for the unrestricted
time-frequency Fubini swap.  No new endpoint estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailGlobalProduct
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On the high-frequency region `‖ξ‖ > 1`, the ordinary selected tail kernel
is pointwise norm-dominated by its `9/4`-weighted version. -/
theorem norm_h3SelectedDuhamelTailComplexKernel_le_nineQuarter_of_one_lt_norm
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3)
    (hp : 1 < ‖p.2‖) :
    ‖h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i p‖
      ≤
    ‖h3SelectedDuhamelTailNineQuarterComplexKernel
        ν A t hν U₀ hA hU₀ i p‖ := by
  have hWeightNonneg :
      0 ≤ h3FourierNineQuarterWeight p.2 := by
    unfold h3FourierNineQuarterWeight
    positivity

  have hWeightOne :
      1 ≤ h3FourierNineQuarterWeight p.2 := by
    unfold h3FourierNineQuarterWeight
    exact
      Real.one_le_rpow hp.le
        (by norm_num : 0 ≤ (9 : ℝ) / 4)

  unfold h3SelectedDuhamelTailNineQuarterComplexKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hWeightNonneg]

  calc
    ‖h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i p‖
        =
      1 *
        ‖h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i p‖ := by
      rw [one_mul]
    _ ≤
      h3FourierNineQuarterWeight p.2 *
        ‖h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i p‖ :=
      mul_le_mul_of_nonneg_right
        hWeightOne
        (norm_nonneg _)

/-- The actual unweighted selected terminal-half raw Fourier kernel is
globally integrable on source-time × Fourier-frequency space. -/
theorem h3SelectedDuhamelTailComplexKernel_fubini_integrable_global
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

  let μξ : Measure H3FourierPoint3 :=
    (volume : Measure H3FourierPoint3)

  let μ : Measure (ℝ × H3FourierPoint3) :=
    μt.prod μξ

  let S : Set H3FourierPoint3 :=
    Metric.closedBall (0 : H3FourierPoint3) 1

  let low : Set (ℝ × H3FourierPoint3) :=
    Set.univ ×ˢ S

  let high : Set (ℝ × H3FourierPoint3) :=
    Set.univ ×ˢ Sᶜ

  let K : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailComplexKernel
      ν A t hν U₀ hA hU₀ i

  let K9 : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailNineQuarterComplexKernel
      ν A t hν U₀ hA hU₀ i

  have hS : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_closedBall

  have hμS :
      (volume : Measure H3FourierPoint3) S ≠ ∞ := by
    have hfinite :
        (volume : Measure H3FourierPoint3)
            (Metric.closedBall (0 : H3FourierPoint3) 1)
          < ∞ :=
      Metric.isBounded_closedBall.measure_lt_top
    simpa only [S] using hfinite.ne

  have hLowLocal :
      Integrable
        K
        (μt.prod (μξ.restrict S)) := by
    dsimp only [K, μt, μξ]
    exact
      h3SelectedDuhamelTailComplexKernel_local_product_integrable
        hν U₀ hA hU₀ ht i S hS hμS

  have hLow :
      IntegrableOn K low μ := by
    change Integrable K (μ.restrict low)
    dsimp only [μ, low]
    rw [← Measure.prod_restrict]
    rw [Measure.restrict_univ]
    exact hLowLocal

  have hWeighted :
      Integrable K9 μ := by
    dsimp only [K9, μ, μt, μξ]
    exact
      h3SelectedDuhamelTailNineQuarterComplexKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hHighMeas : MeasurableSet high := by
    dsimp only [high]
    measurability

  have hHigh :
      IntegrableOn K high μ := by
    change Integrable K (μ.restrict high)

    have hWeightedHigh :
        Integrable K9 (μ.restrict high) :=
      hWeighted.restrict

    refine
      Integrable.mono
        (f := K)
        (g := K9)
        hWeightedHigh
        ?_
        ?_

    · exact
        (measurable_h3SelectedDuhamelTailComplexKernel
          hν U₀ hA hU₀ i).aestronglyMeasurable

    · rw [ae_restrict_iff' hHighMeas]
      filter_upwards with p hp

      have hpNot : p.2 ∉ S := by
        exact hp.2

      have hpNorm : 1 < ‖p.2‖ := by
        simpa only [
          S,
          Metric.mem_closedBall,
          dist_zero_right,
          not_le
        ] using hpNot

      dsimp only [K, K9]
      exact
        norm_h3SelectedDuhamelTailComplexKernel_le_nineQuarter_of_one_lt_norm
          hν U₀ hA hU₀ i p hpNorm

  have hCover :
      low ∪ high = Set.univ := by
    ext p
    simp only [
      low,
      high,
      Set.mem_union,
      Set.mem_prod,
      Set.mem_univ,
      true_and,
      Set.mem_compl_iff,
      Set.mem_univ,
      iff_true
    ]
    exact Classical.em (p.2 ∈ S)

  have hAll :
      IntegrableOn K (low ∪ high) μ :=
    hLow.union hHigh

  rw [hCover] at hAll

  have hGlobal : Integrable K μ :=
    integrableOn_univ.mp hAll

  simpa only [K, μ, μt, μξ] using hGlobal

end

end Euclidean
end Bridge
end PrimeTensor

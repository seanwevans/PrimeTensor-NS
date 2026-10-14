import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPermutationSectors
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# A common positive six-dimensional tube around all twelve sharp sectors

The preceding module proved positivity on a separate compact ball near each
of the twelve exact coherent resonant frequency pairs. Here the twelve
points are treated as ONE finite compact set. Their exact value 9/64, and
continuity of the genuine fixed Schwartz-field six-order signed kernel,
produce a SINGLE positive radius on which the signed kernel is bounded
strictly below by 9/128 on the entire closed metric thickening.

The signed integral on this common compact thickening is strictly positive.
A separate conditional theorem specifies the remaining support inclusion
needed to conclude positivity of the UNLOCALIZED signed integral. That
support inclusion is not proved for the existing width-1/16 cutoffs.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set Filter
open scoped Topology

noncomputable section

private abbrev TubeV := Fin 3 → ℝ
private abbrev TubePair := TubeV × TubeV

/-- The single finite set of all six positive and six reflected center pairs. -/
def lowNormalQuarterCoherentCenterSet : Set TubePair :=
  Set.range (fun bk : Bool × Fin 6 => lowNormalQuarterCoherentPair bk.1 bk.2)

/-- The entire twelve-point orbit is compact in the Fourier pair space. -/
theorem lowNormalQuarterCoherentCenterSet_isCompact :
    IsCompact lowNormalQuarterCoherentCenterSet := by
  exact (Set.finite_range (fun bk : Bool × Fin 6 =>
    lowNormalQuarterCoherentPair bk.1 bk.2)).isCompact

/-- One *common* positive width works at every coherent center at once.
The quantitative lower bound is half of the exact center value 9/64. -/
theorem lowNormalQuarterSignedKernel_exists_uniform_positive_tube :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ Metric.cthickening δ lowNormalQuarterCoherentCenterSet,
        (9 / 128 : ℝ) < lowNormalQuarterSignedKernel z := by
  have hOpen : IsOpen {z : TubePair | (9 / 128 : ℝ) < lowNormalQuarterSignedKernel z} :=
    isOpen_lt continuous_const lowNormalQuarterSignedKernel_continuous
  have hCenters : lowNormalQuarterCoherentCenterSet ⊆
      {z : TubePair | (9 / 128 : ℝ) < lowNormalQuarterSignedKernel z} := by
    intro z hz
    obtain ⟨⟨b, k⟩, rfl⟩ := hz
    change (9 / 128 : ℝ) <
      lowNormalQuarterSignedKernel (lowNormalQuarterCoherentPair b k)
    rw [lowNormalQuarterCoherentPair_value]
    norm_num
  obtain ⟨ε, hε, hεSub⟩ :=
    lowNormalQuarterCoherentCenterSet_isCompact.exists_thickening_subset_open
      hOpen hCenters
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro z hz
  exact hεSub (Metric.cthickening_subset_thickening'
    hε (half_lt_self hε) lowNormalQuarterCoherentCenterSet hz)

/-- The common coherent tube has strictly positive signed integral, without
summing twelve overlapping balls or presuming any global support claim. -/
theorem lowNormalQuarterSignedKernel_exists_positive_coherent_tube_integral :
    ∃ δ : ℝ, 0 < δ ∧
      0 < ∫ z in Metric.cthickening δ lowNormalQuarterCoherentCenterSet,
        lowNormalQuarterSignedKernel z ∂(volume.prod volume) := by
  obtain ⟨δ, hδ, hPos⟩ :=
    lowNormalQuarterSignedKernel_exists_uniform_positive_tube
  let s : Set TubePair := Metric.cthickening δ lowNormalQuarterCoherentCenterSet
  have hCompact : IsCompact s :=
    lowNormalQuarterCoherentCenterSet_isCompact.cthickening
  have hMeas : MeasurableSet s := Metric.isClosed_cthickening.measurableSet
  have hInt : IntegrableOn lowNormalQuarterSignedKernel s
      (volume.prod volume) :=
    lowNormalQuarterSignedKernel_continuous.continuousOn.integrableOn_compact
      hCompact
  have hNonneg :
      0 ≤ᵐ[(volume.prod volume).restrict s] lowNormalQuarterSignedKernel := by
    filter_upwards [ae_restrict_mem hMeas] with z hz
    exact (le_trans (by norm_num : (0 : ℝ) ≤ 9 / 128) (hPos z hz).le)
  have hCenter : lowNormalQuarterCoherentPair false (0 : Fin 6) ∈
      lowNormalQuarterCoherentCenterSet := by
    exact ⟨(false, 0), rfl⟩
  have hBallSubset :
      Metric.ball (lowNormalQuarterCoherentPair false (0 : Fin 6)) δ ⊆
        Function.support lowNormalQuarterSignedKernel ∩ s := by
    intro z hz
    have hIn : z ∈ s :=
      (Metric.thickening_subset_cthickening δ lowNormalQuarterCoherentCenterSet)
        ((Metric.ball_subset_thickening hCenter δ) hz)
    constructor
    · change lowNormalQuarterSignedKernel z ≠ 0
      exact ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 9 / 128) (hPos z hIn))
    · exact hIn
  have hMeasure :
      0 < (volume.prod volume)
        (Function.support lowNormalQuarterSignedKernel ∩ s) := by
    exact (Metric.measure_ball_pos (volume.prod volume)
      (lowNormalQuarterCoherentPair false (0 : Fin 6)) hδ).trans_le
        (measure_mono hBallSubset)
  refine ⟨δ, hδ, ?_⟩
  change 0 < ∫ z in s, lowNormalQuarterSignedKernel z ∂(volume.prod volume)
  exact (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hMeasure

/-- Exact remaining condition for upgrading uniform local positivity to a
strict sign on the entire (unlocalized) Fourier integral.  This theorem is
conditional: the width-1/16 field is NOT known to have support in the tube. -/
theorem lowNormalQuarterSignedKernel_global_integral_pos_of_support_in_tube
    (δ : ℝ) (hδ : 0 < δ)
    (hPos : ∀ z ∈ Metric.cthickening δ lowNormalQuarterCoherentCenterSet,
      (9 / 128 : ℝ) < lowNormalQuarterSignedKernel z)
    (hSupport : Function.support lowNormalQuarterSignedKernel ⊆
      Metric.cthickening δ lowNormalQuarterCoherentCenterSet)
    (hInt : Integrable lowNormalQuarterSignedKernel (volume.prod volume)) :
    0 < ∫ z, lowNormalQuarterSignedKernel z ∂(volume.prod volume) := by
  have hNonneg : 0 ≤ lowNormalQuarterSignedKernel := by
    intro z
    by_cases hz : lowNormalQuarterSignedKernel z = 0
    · simpa only [Pi.zero_apply, hz] using (le_refl (0 : ℝ))
    · have hMem : z ∈ Function.support lowNormalQuarterSignedKernel := by
        simpa only [Function.mem_support] using hz
      exact (le_trans (by norm_num : (0 : ℝ) ≤ 9 / 128)
        (hPos z (hSupport hMem)).le)
  have hPositiveAt : lowNormalQuarterSignedKernel
      (lowNormalQuarterCoherentPair false (0 : Fin 6)) ≠ 0 := by
    rw [lowNormalQuarterCoherentPair_value]
    norm_num
  have hMeasure :
      0 < (volume.prod volume) (Function.support lowNormalQuarterSignedKernel) :=
    (lowNormalQuarterSignedKernel_continuous.isOpen_support).measure_pos
      (volume.prod volume) ⟨_, hPositiveAt⟩
  exact (integral_pos_iff_support_of_nonneg hNonneg hInt).2 hMeasure

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterLocalSign
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Strictly positive *localized* signed six-order integral

The preceding theorem proved continuity and strict positivity of the signed
six-order symbol at the genuine quarter-scale Schwartz resonant pair.

Here we use its positive neighborhood to construct a closed frequency-pair
ball with positive radius on which the *actual fixed Schwartz-field kernel*
is everywhere strictly positive. The ball is compact in the six-dimensional
finite Euclidean product; hence the continuous kernel is integrable there.
The inner open ball has strictly positive product-Lebesgue volume, so the
signed integral over the closed ball is strictly positive.

This is a nonzero localized integral with the precise support region given.
It does NOT claim the unlocalized six-packet integral is nonzero: other
resonant regions may cancel this positive contribution. Nor does it identify
the formal phase factor I with the sign of a Navier--Stokes energy term.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set Filter
open scoped Topology

noncomputable section

private abbrev QuarterFrequency := Fin 3 → ℝ
private abbrev QuarterFrequencyPair := QuarterFrequency × QuarterFrequency

/-- The momentum-plane pair (p,r) at the sharp quarter-scale example. -/
def lowNormalQuarterResonantPair : QuarterFrequencyPair :=
  (lowNormalAuditP, lowNormalAuditR (1 / 4 : ℝ))

/-- The signed integral on the closed six-dimensional frequency-pair ball. -/
noncomputable def lowNormalQuarterLocalizedSignedIntegral (r : ℝ) : ℝ :=
  ∫ z in Metric.closedBall lowNormalQuarterResonantPair r,
    lowNormalQuarterSignedKernel z ∂(volume.prod volume)

/-- Local sign persistence can be made uniform on a sufficiently small
closed ball around the exact resonant pair. -/
theorem lowNormalQuarterSignedKernel_exists_positive_closedBall :
    ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ Metric.closedBall lowNormalQuarterResonantPair r,
        0 < lowNormalQuarterSignedKernel z := by
  -- `Eventually` unfolds to membership of its predicate set in the filter.
  -- Keep both sides in the same `Eventually` form for elaboration.
  have hEvent :
      ∀ᶠ z : QuarterFrequencyPair in 𝓝 lowNormalQuarterResonantPair,
        0 < lowNormalQuarterSignedKernel z := by
    simpa only [lowNormalQuarterResonantPair] using
      lowNormalQuarterSignedKernel_eventually_positive
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hEvent
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro z hz
  exact hsub ((Metric.closedBall_subset_ball (half_lt_self hε)) hz)

/-- The localized signed integral is strictly positive for an explicit
nonempty compact-frequency neighborhood.  This does not control the
integral on the rest of the six-packet support. -/
theorem lowNormalQuarterLocalizedSignedIntegral_exists_pos :
    ∃ r : ℝ, 0 < r ∧ 0 < lowNormalQuarterLocalizedSignedIntegral r := by
  obtain ⟨r, hr, hpos⟩ :=
    lowNormalQuarterSignedKernel_exists_positive_closedBall
  let s : Set QuarterFrequencyPair :=
    Metric.closedBall lowNormalQuarterResonantPair r
  have hCompact : IsCompact s := isCompact_closedBall _ _
  have hMeas : MeasurableSet s := measurableSet_closedBall
  have hInt : IntegrableOn lowNormalQuarterSignedKernel s
      (volume.prod volume) :=
    lowNormalQuarterSignedKernel_continuous.continuousOn.integrableOn_compact
      hCompact
  have hNonneg :
      0 ≤ᵐ[(volume.prod volume).restrict s] lowNormalQuarterSignedKernel := by
    filter_upwards [ae_restrict_mem hMeas] with z hz
    exact (hpos z hz).le
  have hBallSubset :
      Metric.ball lowNormalQuarterResonantPair r ⊆
        Function.support lowNormalQuarterSignedKernel ∩ s := by
    intro z hz
    constructor
    · change lowNormalQuarterSignedKernel z ≠ 0
      exact ne_of_gt (hpos z (Metric.ball_subset_closedBall hz))
    · exact Metric.ball_subset_closedBall hz
  have hMeasure :
      0 < (volume.prod volume)
        (Function.support lowNormalQuarterSignedKernel ∩ s) := by
    exact (Metric.measure_ball_pos (volume.prod volume)
      lowNormalQuarterResonantPair hr).trans_le (measure_mono hBallSubset)
  refine ⟨r, hr, ?_⟩
  change 0 < ∫ z in s,
    lowNormalQuarterSignedKernel z ∂(volume.prod volume)
  exact (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hMeasure

/-- A nonzero localized *imaginary* six-permutation integral follows from
the signed real phase extraction, without treating the global integral. -/
theorem lowNormalQuarterLocalizedSignedIntegral_exists_ne_zero :
    ∃ r : ℝ, 0 < r ∧ lowNormalQuarterLocalizedSignedIntegral r ≠ 0 := by
  obtain ⟨r, hr, hpos⟩ :=
    lowNormalQuarterLocalizedSignedIntegral_exists_pos
  exact ⟨r, hr, ne_of_gt hpos⟩

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSixSectorPairing244
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic

/-!
# Literal disjoint coherent support sectors for the real full-third kernel

The twelve sharp pair centers are treated on the AXIS-coordinate carrier,
whose product sup metric is the metric used by the existing Fourier support
classification. We do NOT identify this metric with the separate physical
Hilbert-product metric on the integration carrier. Instead the twelve
integration domains are PREIMAGES of actual axis-coordinate open balls.

We prove that all twelve labeled centers are separated by at least one
unit, so balls of radius at most 1/2 are genuinely disjoint. The existing
closed coherent-tube support theorem and the strict-radius enlargement then
show that the actual unphased imaginary H3 kernel vanishes outside their
union whenever ρ < δ and the existing nonresonance width hypothesis holds.

This is geometry and pointwise support, not yet the finite-additivity theorem
for the global integral, nor a sector sign estimate.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev PairFreq244 := Freq244 × Freq244
private abbrev V3 := H3FourierPoint3
private abbrev PairV244 := V3 × V3

noncomputable local instance axisFintypeSectorGeometry244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The twelve *distinct* ordered axis-coordinate pair labels. -/
def thirdFullCoherentPairLabel244 (bk : Bool × Fin 6) : PairFreq244 :=
  (thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair bk.1 bk.2).1,
   thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair bk.1 bk.2).2)

/-- Injectivity is a concrete finite theorem about the twelve enumerated
ordered pairs; it does not assume center distinctness. -/
theorem thirdFullCoherentPairIndex_injective244 :
    Function.Injective (fun bk : Bool × Fin 6 =>
      lowNormalQuarterCoherentLabelPair bk.1 bk.2) := by
  intro ⟨b, i⟩ ⟨c, j⟩ hij
  cases b <;> cases c <;> fin_cases i <;> fin_cases j <;>
    simp_all [lowNormalQuarterCoherentLabelPair]

/-- Among the six sharp real-axis centers at t=1, any two distinct labels
are separated by at least one unit in a physical coordinate. -/
theorem thirdFullSixAxisCenters_coordinate_gap244
    (i j : Fin 6) (hij : i ≠ j) :
    ∃ a : A3, (1 : ℝ) ≤
      |thirdFullAxisSixCenter244 i a - thirdFullAxisSixCenter244 j a| := by
  -- The x coordinate separates every pair except (0,1), (1,0),
  -- (3,4), and (4,3); those four are separated by the y coordinate.
  -- Split on the actual x-coordinate inequality *before* enumerating the
  -- finite labels. This avoids `first` accepting an unfinished x-axis
  -- witness whose remaining goal is False in precisely those four cases.
  by_cases hx : (1 : ℝ) ≤
      |thirdFullAxisSixCenter244 i xAxis -
        thirdFullAxisSixCenter244 j xAxis|
  · exact ⟨xAxis, hx⟩
  · refine ⟨yAxis, ?_⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [thirdFullAxisSixCenter244, lowNormalSixCenter,
        lowNormalLatticeEmbedding, lowNormalSignedLatticeCenter,
        axisRank, xAxis, yAxis] at *

/-- Consequently distinct physical frequency centers have sup-metric
separation at least one. This uses the real-axis Pi norm, NOT the L2 norm. -/
theorem thirdFullSixAxisCenters_dist_gap244
    (i j : Fin 6) (hij : i ≠ j) :
    (1 : ℝ) ≤ dist (thirdFullAxisSixCenter244 i)
      (thirdFullAxisSixCenter244 j) := by
  obtain ⟨a, ha⟩ := thirdFullSixAxisCenters_coordinate_gap244 i j hij
  calc
    (1 : ℝ) ≤
        |thirdFullAxisSixCenter244 i a - thirdFullAxisSixCenter244 j a| := ha
    _ ≤ dist (thirdFullAxisSixCenter244 i)
        (thirdFullAxisSixCenter244 j) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply, dist_eq_norm] using
        (norm_le_pi_norm
          (thirdFullAxisSixCenter244 i - thirdFullAxisSixCenter244 j) a)

/-- The twelve ordered PAIR centers have unit separation on the six-axis
product sup carrier. In particular the six positive permutations are all
distinct from the six Hermitian reflected permutations. -/
theorem thirdFullCoherentPairLabel_dist_gap244
    (s t : Bool × Fin 6) (hst : s ≠ t) :
    (1 : ℝ) ≤ dist (thirdFullCoherentPairLabel244 s)
      (thirdFullCoherentPairLabel244 t) := by
  let is := lowNormalQuarterCoherentLabelPair s.1 s.2
  let it := lowNormalQuarterCoherentLabelPair t.1 t.2
  have hp : is ≠ it := by
    intro heq
    exact hst (thirdFullCoherentPairIndex_injective244 heq)
  change (1 : ℝ) ≤
    max (dist (thirdFullAxisSixCenter244 is.1)
          (thirdFullAxisSixCenter244 it.1))
        (dist (thirdFullAxisSixCenter244 is.2)
          (thirdFullAxisSixCenter244 it.2))
  by_cases hfirst : is.1 = it.1
  · have hlast : is.2 ≠ it.2 := by
      intro hsecond
      exact hp (Prod.ext hfirst hsecond)
    exact (thirdFullSixAxisCenters_dist_gap244 _ _ hlast).trans
      (le_max_right _ _)
  · exact (thirdFullSixAxisCenters_dist_gap244 _ _ hfirst).trans
      (le_max_left _ _)

/-- No two labeled coherent axis-frequency pair balls overlap once twice
their common radius is at most the proven unit separation. -/
theorem thirdFullCoherentAxisBalls_disjoint244
    (s t : Bool × Fin 6) (hst : s ≠ t)
    (δ : ℝ) (hδ : 2 * δ ≤ 1) :
    Disjoint (Metric.ball (thirdFullCoherentPairLabel244 s) δ)
      (Metric.ball (thirdFullCoherentPairLabel244 t) δ) := by
  apply Metric.ball_disjoint_ball
  exact (show δ + δ ≤ (1 : ℝ) by linarith).trans
    (thirdFullCoherentPairLabel_dist_gap244 s t hst)

/-- A sector on the real PHYSICAL integral carrier is the preimage of one
axis-coordinate ball. This avoids conflating its Euclidean/L2 distance with
the axis-coordinate sup metric. -/
def thirdFullHilbertCoherentSector244
    (bk : Bool × Fin 6) (δ : ℝ) : Set PairV244 :=
  {z | (WithLp.ofLp z.1, WithLp.ofLp z.2) ∈
    Metric.ball (thirdFullCoherentPairLabel244 bk) δ}

/-- These genuinely physical measurable-carrier sector domains remain
disjoint, because their axis-coordinate images lie in disjoint balls. -/
theorem thirdFullHilbertCoherentSectors_disjoint244
    (s t : Bool × Fin 6) (hst : s ≠ t)
    (δ : ℝ) (hδ : 2 * δ ≤ 1) :
    Disjoint (thirdFullHilbertCoherentSector244 s δ)
      (thirdFullHilbertCoherentSector244 t δ) := by
  apply Set.disjoint_left.mpr
  intro z hz ht
  exact (Set.disjoint_left.mp
    (thirdFullCoherentAxisBalls_disjoint244 s t hst δ hδ)) hz ht

/-- A nonzero value of the REAL velocity's actual unphased imaginary
commutator kernel lies in one of the twelve labeled open sectors. In the
existing project this uses the closed coherent-tube support theorem, hence
the STRICT enlargement ρ < δ is essential. -/
theorem thirdFullAxisImagKernel_mem_labeled_sector244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ < δ) (A B C : Freq244)
    (z : PairV244)
    (hNonzero :
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im ≠ 0) :
    ∃ bk : Bool × Fin 6, z ∈ thirdFullHilbertCoherentSector244 bk δ := by
  have hIn : (WithLp.ofLp z.1, WithLp.ofLp z.2) ∈
      Metric.cthickening ρ thirdFullAxisCoherentPairCenterSet244 := by
    by_contra hAway
    exact hNonzero (thirdFullAxisRealThirdUnphasedImag_zero_off_tube244
      ρ hρ hSmall ρ (le_refl ρ) A B C z hAway)
  have hOpen : (WithLp.ofLp z.1, WithLp.ofLp z.2) ∈
      Metric.thickening δ thirdFullAxisCoherentPairCenterSet244 :=
    (Metric.cthickening_subset_thickening'
      (lt_trans hρ hρδ) hρδ thirdFullAxisCoherentPairCenterSet244) hIn
  obtain ⟨c, hc, hdist⟩ := Metric.mem_thickening_iff.mp hOpen
  change c ∈ Set.range thirdFullCoherentPairLabel244 at hc
  obtain ⟨bk, rfl⟩ := hc
  exact ⟨bk, hdist⟩

/-- Equivalent pointwise support exclusion: away from all twelve disjoint
open sectors the full imaginary kernel is EXACTLY zero. -/
theorem thirdFullAxisImagKernel_zero_off_labeled_sectors244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ < δ) (A B C : Freq244)
    (z : PairV244)
    (hAway : ∀ bk : Bool × Fin 6,
      z ∉ thirdFullHilbertCoherentSector244 bk δ) :
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im = 0 := by
  by_contra hNonzero
  obtain ⟨bk, hb⟩ := thirdFullAxisImagKernel_mem_labeled_sector244
    ρ hρ hSmall δ hρδ A B C z hNonzero
  exact hAway bk hb

/-- The exact quantitative geometric hypotheses are simultaneously
satisfiable for narrow packets, e.g. any ρ below 1/4 permits δ=1/4. -/
theorem thirdFullAxisSectorGeometry_exists_radius244
    (ρ : ℝ) (hρ : 0 < ρ) (hρSmall : ρ < 1 / 4) :
    ∃ δ : ℝ, ρ < δ ∧ 2 * δ ≤ 1 := by
  refine ⟨1 / 4, hρSmall, ?_⟩
  norm_num

end
end PrimeTensor.FirstMonomialTriad

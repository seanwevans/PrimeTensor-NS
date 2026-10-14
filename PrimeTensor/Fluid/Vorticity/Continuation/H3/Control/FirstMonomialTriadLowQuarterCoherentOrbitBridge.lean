import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterNarrowSupport

/-!
# Exact coherent-label orbit and geometric containment for narrow packets

The preceding width-parameterized Schwartz construction places every
nonzero momentum-conserving triple near a *labeled* coherent frequency pair.
The earlier fixed-width positive-tube theorem is expressed using a different,
twelve-point center orbit. Here we prove these two FINITE CENTER SETS are equal.

This is a geometric identification and a conditional support inclusion for the
new field. It is NOT a statement that the signed coefficient of the new field
coincides with that of the original fixed-width field: altering a cutoff also
alters the trilinear integral kernel. A width-dependent symbol sign estimate
is still necessary for full-integral noncancellation.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Metric
open scoped Topology

noncomputable section

private abbrev OrbitV := Fin 3 → ℝ
private abbrev OrbitPair := OrbitV × OrbitV

/-- Concrete first/third labels of each coherent triad: six positive
permutations and six simultaneous frequency reflections. -/
def lowNormalQuarterCoherentLabelPair (reflected : Bool) (k : Fin 6) :
    Fin 6 × Fin 6 :=
  match reflected, k.val with
  | false, 0 => (0, 2)
  | false, 1 => (2, 0)
  | false, 2 => (1, 2)
  | false, 3 => (2, 1)
  | false, 4 => (1, 0)
  | false, _ => (0, 1)
  | true, 0 => (3, 5)
  | true, 1 => (5, 3)
  | true, 2 => (4, 5)
  | true, 3 => (5, 4)
  | true, 4 => (4, 3)
  | true, _ => (3, 4)

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

/-- Complete finite classification of coherent first/third index pairs.
The middle label is uniquely the remaining element in its orientation class. -/
theorem lowNormalQuarterCoherentLabels_classify
    (i j k : Fin 6) (h : lowNormalCoherentCenters i j k) :
    ∃ reflected : Bool, ∃ n : Fin 6,
      (i, k) = lowNormalQuarterCoherentLabelPair reflected n := by
  -- Exhaust the 216 possibilities directly. Inconsistent triples disappear
  -- under `norm_num` and the 12 coherent ones have explicit witnesses.
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [lowNormalCoherentCenters] at h <;>
    first
    | exact ⟨false, 0, rfl⟩
    | exact ⟨false, 1, rfl⟩
    | exact ⟨false, 2, rfl⟩
    | exact ⟨false, 3, rfl⟩
    | exact ⟨false, 4, rfl⟩
    | exact ⟨false, 5, rfl⟩
    | exact ⟨true, 0, rfl⟩
    | exact ⟨true, 1, rfl⟩
    | exact ⟨true, 2, rfl⟩
    | exact ⟨true, 3, rfl⟩
    | exact ⟨true, 4, rfl⟩
    | exact ⟨true, 5, rfl⟩

/-- Every enumerated ordered label pair can be completed to a coherent
three-center momentum relation (with some middle label). -/
theorem lowNormalQuarterCoherentLabels_complete (reflected : Bool) (n : Fin 6) :
    ∃ j : Fin 6,
      lowNormalCoherentCenters
        (lowNormalQuarterCoherentLabelPair reflected n).1 j
        (lowNormalQuarterCoherentLabelPair reflected n).2 := by
  -- The witnesses are explicit, and `decide` discharges every remaining
  -- closed inequality of concrete `Fin 6` indices after normalization.
  cases reflected with
  | false =>
    fin_cases n
    · exact ⟨1, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩
    · exact ⟨1, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩
    · exact ⟨0, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩
    · exact ⟨0, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩
    · exact ⟨2, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩
    · exact ⟨2, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩
  | true =>
    fin_cases n
    · exact ⟨4, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩
    · exact ⟨4, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩
    · exact ⟨3, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩
    · exact ⟨3, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩
    · exact ⟨5, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩
    · exact ⟨5, by norm_num [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair] <;> decide⟩

/-- Under the concrete real quarter-scale frequency embedding, the indexed
pairs are exactly the orbit points used by the twelve-sector sign theorem. -/
theorem lowNormalQuarterCoherentLabelPair_embedding
    (reflected : Bool) (n : Fin 6) :
    (lowNormalSixCenter (1 / 4 : ℝ)
        (lowNormalQuarterCoherentLabelPair reflected n).1,
     lowNormalSixCenter (1 / 4 : ℝ)
        (lowNormalQuarterCoherentLabelPair reflected n).2) =
      lowNormalQuarterCoherentPair reflected n := by
  have hPrimary := lowNormalSixCenter_primary (1 / 4 : ℝ)
  have hReflected := lowNormalSixCenter_reflected (1 / 4 : ℝ)
  rcases hPrimary with ⟨hP, hQ, hR⟩
  rcases hReflected with ⟨hPm, hQm, hRm⟩
  -- `simp` normalizes `1 / 4` to `4⁻¹` in each finite case.
  -- Normalize the six anchoring equalities first, so they rewrite there.
  simp only [one_div] at hP hQ hR hPm hQm hRm
  -- The reflected cases compare a pointwise-negated function with Pi.neg.
  -- Extensionality, not simplification of an unapplied function, closes them.
  cases reflected <;> fin_cases n <;>
    simp [lowNormalQuarterCoherentLabelPair,
      lowNormalQuarterCoherentPair, lowNormalQuarterPositivePair,
      hP, hQ, hR, hPm, hQm, hRm] <;>
    (constructor <;> funext d <;> simp only [Pi.neg_apply])

/-- **Exact bridge:** the labeled coherent frequency-pair center set from the
narrow field equals the pre-existing twelve-center orbit, as sets. -/
theorem lowNormalQuarterLabeledCoherentPairSet_eq_centerSet :
    lowNormalQuarterLabeledCoherentPairSet =
      lowNormalQuarterCoherentCenterSet := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, j, k, hcoh, rfl⟩ := hz
    obtain ⟨reflected, n, hlabels⟩ :=
      lowNormalQuarterCoherentLabels_classify i j k hcoh
    have hi : i = (lowNormalQuarterCoherentLabelPair reflected n).1 :=
      congrArg Prod.fst hlabels
    have hk : k = (lowNormalQuarterCoherentLabelPair reflected n).2 :=
      congrArg Prod.snd hlabels
    change (lowNormalSixCenter (1 / 4 : ℝ) i,
      lowNormalSixCenter (1 / 4 : ℝ) k) ∈
        Set.range (fun bk : Bool × Fin 6 =>
          lowNormalQuarterCoherentPair bk.1 bk.2)
    refine ⟨(reflected, n), ?_⟩
    change lowNormalQuarterCoherentPair reflected n =
      (lowNormalSixCenter (1 / 4 : ℝ) i,
       lowNormalSixCenter (1 / 4 : ℝ) k)
    rw [hi, hk]
    exact (lowNormalQuarterCoherentLabelPair_embedding reflected n).symm
  · intro hz
    change z ∈ Set.range (fun bk : Bool × Fin 6 =>
      lowNormalQuarterCoherentPair bk.1 bk.2) at hz
    obtain ⟨⟨reflected, n⟩, rfl⟩ := hz
    obtain ⟨j, hj⟩ := lowNormalQuarterCoherentLabels_complete reflected n
    let pair := lowNormalQuarterCoherentLabelPair reflected n
    change ∃ i j k : Fin 6, lowNormalCoherentCenters i j k ∧
      lowNormalQuarterCoherentPair reflected n =
        (lowNormalSixCenter (1 / 4 : ℝ) i,
         lowNormalSixCenter (1 / 4 : ℝ) k)
    exact ⟨pair.1, j, pair.2, hj,
      (lowNormalQuarterCoherentLabelPair_embedding reflected n).symm⟩

/-- The entire nonzero three-wave interaction of a sufficiently narrow
six-packet field lies in an actual common twelve-center tube. -/
theorem lowNormalQuarterNarrowFourier_support_in_centerTube
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 / 4 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ)
    (p r : OrbitV)
    (hp : lowNormalQuarterNarrowFourier ρ hρ p ≠ 0)
    (hq : lowNormalQuarterNarrowFourier ρ hρ (middleFrequency p r) ≠ 0)
    (hr : lowNormalQuarterNarrowFourier ρ hρ r ≠ 0) :
    (p, r) ∈ Metric.cthickening δ lowNormalQuarterCoherentCenterSet := by
  have hNear := lowNormalQuarterNarrowFourier_support_in_coherent_thickening
    ρ hρ hSmall p r hp hq hr
  rw [lowNormalQuarterLabeledCoherentPairSet_eq_centerSet] at hNear
  exact (Metric.thickening_subset_cthickening_of_le hρδ
    lowNormalQuarterCoherentCenterSet) hNear

/-- For *any* positive target tube radius, an adjustable Schwartz field has
a positive width which is both nonresonant and whose three-wave support is
confined to that tube. This is the needed quantifier order for the later
width-dependent signed-symbol analysis. -/
theorem lowNormalQuarterNarrowFourier_exists_width_in_centerTube
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ρ ≤ lowNormalSixCenterSeparationRadius (1 / 4 : ℝ) ∧
      ∀ p r : OrbitV,
        lowNormalQuarterNarrowFourier ρ hρ p ≠ 0 →
        lowNormalQuarterNarrowFourier ρ hρ (middleFrequency p r) ≠ 0 →
        lowNormalQuarterNarrowFourier ρ hρ r ≠ 0 →
        (p, r) ∈ Metric.cthickening δ lowNormalQuarterCoherentCenterSet := by
  let σ := lowNormalSixCenterSeparationRadius (1 / 4 : ℝ)
  have hσ : 0 < σ := lowNormalSixCenterSeparationRadius_pos
    (1 / 4 : ℝ) (by norm_num)
  let ρ := min δ σ / 2
  have hρ : 0 < ρ := half_pos (lt_min hδ hσ)
  have hSmall : ρ ≤ σ := by
    dsimp [ρ]
    linarith [min_le_right δ σ]
  have hρδ : ρ ≤ δ := by
    dsimp [ρ]
    linarith [min_le_left δ σ]
  refine ⟨ρ, hρ, hSmall, ?_⟩
  intro p r hp hq hr
  exact lowNormalQuarterNarrowFourier_support_in_centerTube
    ρ hρ hSmall δ hρδ p r hp hq hr


/-- As a *geometric comparison*, choose a width whose nonzero interactions
lie inside the positivity tube of the ORIGINAL fixed-width kernel. This
assertion deliberately evaluates `lowNormalQuarterSignedKernel`, NOT the
signed kernel obtained from `lowNormalQuarterNarrowFourier`. -/
theorem lowNormalQuarterNarrowFourier_exists_width_in_fixedKernel_positive_region :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ρ ≤ lowNormalSixCenterSeparationRadius (1 / 4 : ℝ) ∧
      ∀ p r : OrbitV,
        lowNormalQuarterNarrowFourier ρ hρ p ≠ 0 →
        lowNormalQuarterNarrowFourier ρ hρ (middleFrequency p r) ≠ 0 →
        lowNormalQuarterNarrowFourier ρ hρ r ≠ 0 →
        (9 / 128 : ℝ) < lowNormalQuarterSignedKernel (p, r) := by
  obtain ⟨δ, hδ, hPositive⟩ :=
    lowNormalQuarterSignedKernel_exists_uniform_positive_tube
  obtain ⟨ρ, hρ, hSmall, hSupport⟩ :=
    lowNormalQuarterNarrowFourier_exists_width_in_centerTube δ hδ
  refine ⟨ρ, hρ, hSmall, ?_⟩
  intro p r hp hq hr
  exact hPositive (p, r) (hSupport p r hp hq hr)

end
end PrimeTensor.FirstMonomialTriad

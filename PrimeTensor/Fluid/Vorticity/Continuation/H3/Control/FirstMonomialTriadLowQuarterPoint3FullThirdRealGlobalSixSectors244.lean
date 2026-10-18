import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSectorGeometry244
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Global six-sector Fourier integral of the full third physical commutator

This module finishes the geometric-to-integral step without claiming a sign.
The twelve sector domains are the PREIMAGES of axis-coordinate sup-metric
balls, not Hilbert L2 balls. The previous disjointness and support results
therefore apply without a change-of-norm argument.

Finite indicator additivity gives an exact decomposition of the entire
unphased imaginary Fourier integral into twelve disjoint sectors. Hermitian
reflection identifies each negative-orientation sector with the corresponding
positive one. The physical factor `(2*pi)^7` and orientation factor two are
preserved. The six remaining sector integrals still require a sign estimate.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev V3 := H3FourierPoint3
private abbrev PairV244 := V3 × V3
private abbrev Label244 := Bool × Fin 6

noncomputable local instance axisFintypeGlobalSix244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The axis-to-Hilbert-carrier preimage sector is measurable. WithLp changes
its norm, not its underlying finite-dimensional topology or Borel sets. -/
theorem thirdFullHilbertCoherentSector_measurable244
    (bk : Label244) (δ : ℝ) :
    MeasurableSet (thirdFullHilbertCoherentSector244 bk δ) := by
  change MeasurableSet
    ((fun z : PairV244 =>
       (WithLp.ofLp z.1, WithLp.ofLp z.2)) ⁻¹'
      Metric.ball (thirdFullCoherentPairLabel244 bk) δ)
  have ho : Continuous (WithLp.ofLp : V3 → Freq244) :=
    PiLp.continuous_ofLp 2 (fun _ : A3 => ℝ)
  have hc : Continuous (fun z : PairV244 =>
      (WithLp.ofLp z.1, WithLp.ofLp z.2)) :=
    (ho.comp continuous_fst).prodMk (ho.comp continuous_snd)
  exact measurableSet_ball.preimage hc.measurable

/-- The actual unphased imaginary Fourier kernel is integrable independently
of the narrow-width/separation assumptions required for the support. -/
theorem thirdFullAxisImagKernel_integrable_global244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    Integrable (fun z : PairV244 =>
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im)
      (volume.prod volume) := by
  exact Complex.imCLM.integrable_comp
    (thirdFullAxisRealThirdUnphasedKernel_integrable244 ρ hρ A B C)

/-- A generic indicator decomposition, assuming exact pointwise support in a
finite family of pairwise disjoint sets. Neither finiteness of the measure
nor nonnegativity of the function is assumed. -/
theorem thirdFullFiniteDisjointIndicatorSum244
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Set PairV244) (f : PairV244 → ℝ)
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hSupport : ∀ z, (∀ i, z ∉ S i) → f z = 0)
    (z : PairV244) :
    f z = ∑ i : ι, (S i).indicator f z := by
  classical
  by_cases hSome : ∃ i : ι, z ∈ S i
  · obtain ⟨i, hi⟩ := hSome
    have hOther (j : ι) (hji : j ≠ i) : z ∉ S j := by
      intro hj
      exact (Set.disjoint_left.mp (hDisjoint j i hji)) hj hi
    have hSum :
        (∑ j : ι, (S j).indicator f z) = (S i).indicator f z := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        have hn := hOther j hji
        simp [Set.indicator, hn]
      · intro hiNot
        simp at hiNot
    rw [hSum]
    simp [Set.indicator, hi]
  · have hAway : ∀ i : ι, z ∉ S i := by
      intro i hi
      exact hSome ⟨i, hi⟩
    have hz : f z = 0 := hSupport z hAway
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro i _
    simp [Set.indicator, hAway i]

/-- The entire imaginary kernel integral, with no cutoff or multiplicity, is
exactly the sum of its twelve disjoint axis-coordinate sector integrals. -/
theorem thirdFullAxisImagKernel_integral_eq_twelve_sectors244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ < δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) :
    (∫ z : PairV244,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume) =
      ∑ bk : Label244,
        ∫ z in thirdFullHilbertCoherentSector244 bk δ,
          (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
            ∂volume.prod volume := by
  classical
  let f : PairV244 → ℝ := fun z =>
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
  let S : Label244 → Set PairV244 :=
    fun bk => thirdFullHilbertCoherentSector244 bk δ
  have hS (bk : Label244) : MeasurableSet (S bk) :=
    thirdFullHilbertCoherentSector_measurable244 bk δ
  have hInt : Integrable f (volume.prod volume) :=
    thirdFullAxisImagKernel_integrable_global244 ρ hρ A B C
  have hIntEach (bk : Label244) :
      Integrable ((S bk).indicator f) (volume.prod volume) :=
    hInt.indicator (hS bk)
  have hPoint (z : PairV244) :
      f z = ∑ bk : Label244, (S bk).indicator f z := by
    apply thirdFullFiniteDisjointIndicatorSum244 S f
    · intro s t hst
      exact thirdFullHilbertCoherentSectors_disjoint244
        s t hst δ hDisj
    · intro w hw
      exact thirdFullAxisImagKernel_zero_off_labeled_sectors244
        ρ hρ hSmall δ hρδ A B C w hw
  calc
    (∫ z : PairV244, f z ∂volume.prod volume) =
      ∫ z : PairV244, ∑ bk : Label244, (S bk).indicator f z
        ∂volume.prod volume := by
          apply integral_congr_ae
          filter_upwards with z
          exact hPoint z
    _ = ∑ bk : Label244,
          ∫ z : PairV244, (S bk).indicator f z
            ∂volume.prod volume := by
          simpa only [Finset.sum_apply] using
            (integral_finsetSum Finset.univ (fun bk _ => hIntEach bk))
    _ = ∑ bk : Label244, ∫ z in S bk, f z
          ∂volume.prod volume := by
          apply Finset.sum_congr rfl
          intro bk _
          exact integral_indicator (hS bk)

/-- The twelve physical-sector centers occur in six exact opposite pairs.
This is a finite computation using the previously proved Hermitian mates. -/
theorem thirdFullCoherentPairLabel_reflect244 (n : Fin 6) :
    thirdFullCoherentPairLabel244 (true, n) =
      -thirdFullCoherentPairLabel244 (false, n) := by
  change
    (thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair true n).1,
     thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair true n).2) =
    (-thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).1,
     -thirdFullAxisSixCenter244 (lowNormalQuarterCoherentLabelPair false n).2)
  fin_cases n <;>
    simp [lowNormalQuarterCoherentLabelPair,
      thirdFullAxisSixCenter_reflect_zero244,
      thirdFullAxisSixCenter_reflect_one244,
      thirdFullAxisSixCenter_reflect_two244]

/-- Simultaneous reflection identifies the two axis-coordinate PREIMAGE
sectors. This does not assert that they are Hilbert L2 balls. -/
theorem thirdFullHilbertCoherentSector_reflect_mem244
    (n : Fin 6) (δ : ℝ) (z : PairV244) :
    (-z.1, -z.2) ∈ thirdFullHilbertCoherentSector244 (true, n) δ ↔
      z ∈ thirdFullHilbertCoherentSector244 (false, n) δ := by
  change dist (WithLp.ofLp (-z.1), WithLp.ofLp (-z.2))
      (thirdFullCoherentPairLabel244 (true, n)) < δ ↔
    dist (WithLp.ofLp z.1, WithLp.ofLp z.2)
      (thirdFullCoherentPairLabel244 (false, n)) < δ
  rw [thirdFullCoherentPairLabel_reflect244]
  simp only [WithLp.ofLp_neg]
  change dist (-(WithLp.ofLp z.1, WithLp.ofLp z.2))
      (-thirdFullCoherentPairLabel244 (false, n)) < δ ↔
    dist (WithLp.ofLp z.1, WithLp.ofLp z.2)
      (thirdFullCoherentPairLabel244 (false, n)) < δ
  rw [dist_neg_neg]

/-- Integral equality for each genuine measurable axis-sector preimage,
not just for round balls in the L2 carrier. -/
theorem thirdFullAxisImagKernel_reflected_sector_integral244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (δ : ℝ) :
    (∫ z in thirdFullHilbertCoherentSector244 (true, n) δ,
       (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
         ∂volume.prod volume) =
    ∫ z in thirdFullHilbertCoherentSector244 (false, n) δ,
       (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
         ∂volume.prod volume := by
  exact thirdFullPairEven_integral_reflected_sets244
    (fun z => (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im)
    (thirdFullAxisImaginaryKernel_even244 ρ hρ A B C)
    (thirdFullHilbertCoherentSector244 (false, n) δ)
    (thirdFullHilbertCoherentSector244 (true, n) δ)
    (thirdFullHilbertCoherentSector_measurable244 (false, n) δ)
    (thirdFullHilbertCoherentSector_measurable244 (true, n) δ)
    (thirdFullHilbertCoherentSector_reflect_mem244 n δ)

/-- The global six-sector signed quantity, using the geometrically correct
sup-metric preimage sectors instead of the earlier labelled L2 balls. -/
noncomputable def thirdFullPositiveSixSectorIntegral244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (δ : ℝ) : ℝ :=
  ∑ n : Fin 6,
    ∫ z in thirdFullHilbertCoherentSector244 (false, n) δ,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume

/-- The full Fourier imaginary-kernel integral reduces EXACTLY to twice the
six positive-orientation sector integrals. There is no missing support,
overcounting, normalization factor or Jacobian. -/
theorem thirdFullAxisImagKernel_integral_eq_twice_six_sectors244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ < δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) :
    (∫ z : PairV244,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume) =
    2 * thirdFullPositiveSixSectorIntegral244 ρ hρ A B C δ := by
  rw [thirdFullAxisImagKernel_integral_eq_twelve_sectors244
    ρ hρ hSmall δ hρδ hDisj A B C]
  unfold thirdFullPositiveSixSectorIntegral244
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [thirdFullAxisImagKernel_reflected_sector_integral244 ρ hρ A B C]
  rw [← Finset.sum_add_distrib]
  simp only [← two_mul]
  rw [← Finset.mul_sum]

/-- Exact physical H3 commutator as SIX signed sector integrals, with its
positive Fourier normalization and the Hermitian factor two. -/
theorem thirdFullAxisRealThirdCommutator_eq_global_six_sectors244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ < δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) :
    fullSchwartzThirdCommutator244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
    2 * (2 * Real.pi) ^ 7 *
      thirdFullPositiveSixSectorIntegral244 ρ hρ A B C δ := by
  rw [thirdFullAxisRealThirdCommutator_eq_imagKernel_integral244,
    thirdFullAxisImagKernel_integral_eq_twice_six_sectors244
      ρ hρ hSmall δ hρδ hDisj A B C]
  ring

/-- The remaining global noncancellation question is EQUIVALENT to the
strict sign of the six actual sector integrals, not just a local symbol. -/
theorem thirdFullAxisRealThirdCommutator_neg_iff_global_six244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ < δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) :
    fullSchwartzThirdCommutator244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) < 0 ↔
    thirdFullPositiveSixSectorIntegral244 ρ hρ A B C δ < 0 := by
  rw [thirdFullAxisRealThirdCommutator_eq_global_six_sectors244
    ρ hρ hSmall δ hρδ hDisj A B C]
  have hc : 0 < 2 * (2 * Real.pi) ^ 7 := by positivity
  constructor
  · intro h
    by_contra hn
    have hp : 0 ≤ thirdFullPositiveSixSectorIntegral244 ρ hρ A B C δ :=
      le_of_not_gt hn
    exact (not_lt_of_ge (mul_nonneg hc.le hp)) h
  · intro h
    exact mul_neg_of_pos_of_neg hc h

end
end PrimeTensor.FirstMonomialTriad

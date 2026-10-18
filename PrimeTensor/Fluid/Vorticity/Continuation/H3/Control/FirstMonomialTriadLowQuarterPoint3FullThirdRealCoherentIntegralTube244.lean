import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSpectrumSupport244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterCoherentOrbitBridge
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Exact twelve-sector localization of trilinear interactions of the REAL Schwartz packet

Our previous theorem proves that nonzero triples of the recovered, real,
solenoidal full-third Schwartz velocity occur only near coherent pairs of six
sharp center frequencies. Here we identify those pairs with the actual
TWELVE-element labeled orbit on the `Axis Depth.three` carrier, choose a
single sufficiently small window radius for any desired coherent tube, and
prove vanishing outside that tube for every trilinear coordinate multiplier.

Consequently the complete integral of any such trilinear multiplier equals
its integral after multiplication by the indicator of this coherent tube.
The frequency multiplier is still abstract: this module DOES NOT identify
such an integral with the specific 3+3+1 and 3+2+2 physical commutator sums,
and it DOES NOT prove signed noncancellation of the twelve coherent sectors.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Metric MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap FourierTransform Topology

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev Pair244 := Freq244 × Freq244

noncomputable local instance axisFintypeFullThirdTube244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The twelve coherent pairs on the *actual* positive-depth Axis carrier.
There are six permutations and their six simultaneous reflections. -/
def thirdFullAxisCoherentPairCenterSet244 : Set Pair244 :=
  Set.range (fun bk : Bool × Fin 6 =>
    (thirdFullAxisSixCenter244
      (lowNormalQuarterCoherentLabelPair bk.1 bk.2).1,
     thirdFullAxisSixCenter244
      (lowNormalQuarterCoherentLabelPair bk.1 bk.2).2))

/-- A finite family of coherent pairs forms a compact set on the physical
six-dimensional frequency-pair carrier. -/
theorem thirdFullAxisCoherentPairCenterSet_isCompact244 :
    IsCompact thirdFullAxisCoherentPairCenterSet244 := by
  exact (Set.finite_range (fun bk : Bool × Fin 6 =>
    (thirdFullAxisSixCenter244
      (lowNormalQuarterCoherentLabelPair bk.1 bk.2).1,
     thirdFullAxisSixCenter244
      (lowNormalQuarterCoherentLabelPair bk.1 bk.2).2))).isCompact

/-- Every coherent labeled triple determines one of the twelve center
pairs; the middle label is kept in the classification hypothesis. -/
theorem thirdFullAxisCoherentPairCenterSet_mem244
    (i j k : Fin 6) (hc : lowNormalCoherentCenters i j k) :
    (thirdFullAxisSixCenter244 i, thirdFullAxisSixCenter244 k) ∈
      thirdFullAxisCoherentPairCenterSet244 := by
  obtain ⟨b, n, hlabel⟩ :=
    lowNormalQuarterCoherentLabels_classify i j k hc
  have hp := congrArg
    (fun labels : Fin 6 × Fin 6 =>
      (thirdFullAxisSixCenter244 labels.1,
       thirdFullAxisSixCenter244 labels.2)) hlabel
  exact ⟨(b, n), hp.symm⟩

/-- Any nonzero three-frequency amplitude of the REAL velocity belongs to
an open radius-ρ tube around the finite twelve-center orbit. -/
theorem thirdFullAxisRealSchwartzTripleMass_mem_coherent_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (A B C : Freq244) (z : Pair244)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C z ≠ 0) :
    z ∈ Metric.thickening ρ thirdFullAxisCoherentPairCenterSet244 := by
  have hp : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.1 ≠ 0 := by
    intro h
    apply hMass
    simp [thirdFullAxisRealSchwartzTripleMass244, h]
  have hq : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
      (thirdFullMiddleFrequency244 z) ≠ 0 := by
    intro h
    apply hMass
    simp [thirdFullAxisRealSchwartzTripleMass244, h]
  have hr : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.2 ≠ 0 := by
    intro h
    apply hMass
    simp [thirdFullAxisRealSchwartzTripleMass244, h]
  obtain ⟨i, j, k, hc, hdist⟩ :=
    thirdFullAxisRealSchwartzSpectrum_coherent_pair244
      ρ hρ hSmall A B C z hp hq hr
  exact (Metric.ball_subset_thickening
    (thirdFullAxisCoherentPairCenterSet_mem244 i j k hc) ρ) hdist

/-- Support exclusion in the form needed to localize a global integral:
all three real-velocity Fourier amplitudes cannot simultaneously survive
outside the *single* twelve-center tube. -/
theorem thirdFullAxisRealSchwartzTripleMass_zero_off_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (A B C : Freq244) (z : Pair244)
    (hAway : z ∉ Metric.thickening ρ thirdFullAxisCoherentPairCenterSet244) :
    thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C z = 0 := by
  by_contra hMass
  exact hAway (thirdFullAxisRealSchwartzTripleMass_mem_coherent_tube244
    ρ hρ hSmall A B C z hMass)

/-- For any desired coherent-tube radius, choose the Fourier windows first,
so their actual triple interactions lie inside that tube for *all* selected
polarizations A,B,C. This quantifier order is crucial for global integration. -/
theorem thirdFullAxisRealSchwartz_exists_width_in_coherent_tube244
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ) ∧
      ∀ (A B C : Freq244) (z : Pair244),
        z ∉ Metric.cthickening δ thirdFullAxisCoherentPairCenterSet244 →
          thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C z = 0 := by
  let σ := lowNormalSixCenterSeparationRadius (1 : ℝ)
  have hσ : 0 < σ :=
    lowNormalSixCenterSeparationRadius_pos (1 : ℝ) (by norm_num)
  let ρ := min δ σ / 2
  have hρ : 0 < ρ := half_pos (lt_min hδ hσ)
  have hSmall : ρ ≤ σ := by
    dsimp [ρ]
    linarith [min_le_right δ σ]
  have hδρ : ρ ≤ δ := by
    dsimp [ρ]
    linarith [min_le_left δ σ]
  refine ⟨ρ, hρ, hSmall, ?_⟩
  intro A B C z hAway
  apply thirdFullAxisRealSchwartzTripleMass_zero_off_tube244
    ρ hρ hSmall A B C z
  intro hz
  exact hAway
    ((Metric.thickening_subset_cthickening_of_le hδρ
      thirdFullAxisCoherentPairCenterSet244) hz)

/-- The real Schwartz velocity's product of three individual complex Fourier
components vanishes if its full-vector triple mass vanishes. The three
frequency arguments are p, q=-p-r, and r, with no frozen polarization. -/
theorem thirdFullAxisRealSchwartzTripleComponent_zero_of_mass244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : Pair244)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C z = 0)
    (a b c : A3) :
    (thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.1 a *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
        (thirdFullMiddleFrequency244 z) b) *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.2 c = 0 := by
  by_cases hp : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.1 = 0
  · simp [hp]
  by_cases hq : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
      (thirdFullMiddleFrequency244 z) = 0
  · simp [hq]
  by_cases hr : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.2 = 0
  · simp [hr]
  have hp' : ‖thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.1‖ ≠ 0 := by
    intro h
    exact hp (norm_eq_zero.mp h)
  have hq' : ‖thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
      (thirdFullMiddleFrequency244 z)‖ ≠ 0 := by
    intro h
    exact hq (norm_eq_zero.mp h)
  have hr' : ‖thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.2‖ ≠ 0 := by
    intro h
    exact hr (norm_eq_zero.mp h)
  have hNonzero : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C z ≠ 0 := by
    unfold thirdFullAxisRealSchwartzTripleMass244
    exact mul_ne_zero (mul_ne_zero hp' hq') hr'
  exact (hNonzero hMass).elim

/-- Every cubic polynomial Fourier coefficient formed from the actual real
velocity's three momentum amplitudes has this structure. The multiplier `w`
can carry ordered derivative frequencies and coordinate contractions. This
abstract multiplier is NOT yet identified with the full physical commutator. -/
noncomputable def thirdFullAxisRealSchwartzWeightedTrilinear244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (w : A3 → A3 → A3 → Pair244 → ℂ) (z : Pair244) : ℂ :=
  ∑ a : A3, ∑ b : A3, ∑ c : A3,
    w a b c z *
      ((thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.1 a *
        thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
          (thirdFullMiddleFrequency244 z) b) *
        thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.2 c)

/-- The entire finite sum of Fourier derivative multipliers vanishes off
the coherent tube, not just the nonnegative triple-mass majorant. -/
theorem thirdFullAxisRealSchwartzWeightedTrilinear_zero_off_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ)
    (A B C : Freq244) (w : A3 → A3 → A3 → Pair244 → ℂ)
    (z : Pair244)
    (hAway : z ∉ Metric.cthickening δ thirdFullAxisCoherentPairCenterSet244) :
    thirdFullAxisRealSchwartzWeightedTrilinear244 ρ hρ A B C w z = 0 := by
  have hM : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C z = 0 := by
    apply thirdFullAxisRealSchwartzTripleMass_zero_off_tube244
      ρ hρ hSmall A B C z
    intro hz
    exact hAway
      ((Metric.thickening_subset_cthickening_of_le hρδ
        thirdFullAxisCoherentPairCenterSet244) hz)
  unfold thirdFullAxisRealSchwartzWeightedTrilinear244
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro c _
  rw [thirdFullAxisRealSchwartzTripleComponent_zero_of_mass244
    ρ hρ A B C z hM a b c]
  simp

/-- Exact localization of the GLOBAL complex Fourier integral of every
trilinear multiplier of the constructed REAL velocity to the chosen finite
coherent tube. The RHS is an indicator integral: no disjoint-ball assumption
or unjustified change of Lebesgue measure has been used. -/
theorem thirdFullAxisRealSchwartzWeightedTrilinear_integral_eq_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ)
    (A B C : Freq244) (w : A3 → A3 → A3 → Pair244 → ℂ)
    (_hIntegrable : Integrable
      (thirdFullAxisRealSchwartzWeightedTrilinear244 ρ hρ A B C w)
      (volume.prod volume)) :
    (∫ z : Pair244,
        thirdFullAxisRealSchwartzWeightedTrilinear244 ρ hρ A B C w z
        ∂(volume.prod volume)) =
      ∫ z : Pair244,
        (Metric.cthickening δ thirdFullAxisCoherentPairCenterSet244).indicator
          (thirdFullAxisRealSchwartzWeightedTrilinear244 ρ hρ A B C w) z
        ∂(volume.prod volume) := by
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ Metric.cthickening δ thirdFullAxisCoherentPairCenterSet244
  · simp only [Set.indicator_of_mem hz]
  · have hZero :=
      thirdFullAxisRealSchwartzWeightedTrilinear_zero_off_tube244
        ρ hρ hSmall δ hρδ A B C w z hz
    -- The indicator is definitionally zero off its support set.
    -- Avoid relying on an unavailable indicator lemma name.
    simpa [Set.indicator, hz] using hZero

/-- A single sufficiently small positive width localizes EVERY ordered
cubic Fourier multiplier integral of the actual real Schwartz velocity to
an arbitrary prescribed positive coherent tube. Only the *integral sign*
and its identification with `fullThirdSchwartzFourierCoefficient244` remain. -/
theorem thirdFullAxisRealSchwartzWeightedTrilinear_exists_integral_tube244
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ) ∧
      ∀ (A B C : Freq244) (w : A3 → A3 → A3 → Pair244 → ℂ),
        Integrable (thirdFullAxisRealSchwartzWeightedTrilinear244 ρ hρ A B C w)
          (volume.prod volume) →
        (∫ z : Pair244,
            thirdFullAxisRealSchwartzWeightedTrilinear244 ρ hρ A B C w z
            ∂(volume.prod volume)) =
          ∫ z : Pair244,
            (Metric.cthickening δ thirdFullAxisCoherentPairCenterSet244).indicator
              (thirdFullAxisRealSchwartzWeightedTrilinear244 ρ hρ A B C w) z
            ∂(volume.prod volume) := by
  let σ := lowNormalSixCenterSeparationRadius (1 : ℝ)
  have hσ : 0 < σ :=
    lowNormalSixCenterSeparationRadius_pos (1 : ℝ) (by norm_num)
  let ρ := min δ σ / 2
  have hρ : 0 < ρ := half_pos (lt_min hδ hσ)
  have hSmall : ρ ≤ σ := by
    dsimp [ρ]
    linarith [min_le_right δ σ]
  have hρδ : ρ ≤ δ := by
    dsimp [ρ]
    linarith [min_le_left δ σ]
  refine ⟨ρ, hρ, hSmall, ?_⟩
  intro A B C w hIntegrable
  exact thirdFullAxisRealSchwartzWeightedTrilinear_integral_eq_tube244
    ρ hρ hSmall δ hρδ A B C w hIntegrable

end
end PrimeTensor.FirstMonomialTriad

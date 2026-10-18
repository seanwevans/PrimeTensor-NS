import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdHermitianLocalTube244
import Mathlib.Tactic

/-!
# Genuine transverse, frequency-varying polarizations for the full H3 symbol

The previous -192 Fourier orbit is an exact finite-dimensional identity but
uses polarizations that are transverse only at its three center frequencies.
Here the polynomial Leray numerator is divided by the NONZERO FIXED CENTER
squared length, never by the varying frequency.  This produces continuously
varying, exactly divergence-free polarization germs that agree with the
sharp polarizations at their centers.

The full corrected six-permutation symbol is trilinear in its three vector
polarizations. We prove this and show that substituting the frequency-varying
germs still gives a strictly negative seven-derivative Hermitian phase
coefficient throughout a nonempty momentum-pair neighborhood.

This is NOT a global noncancellation result for an actual Schwartz Fourier
integral. Compact scalar windows, their support geometry, and all reflected
permutation sectors still must be combined.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set Filter PrimeTensor.Bridge.Euclidean
open scoped Topology BigOperators

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Pair244 := (A3 → ℝ) × (A3 → ℝ)

noncomputable local instance axisFintypeProjectedGerm244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Real scalar multiplication in the second argument of the physical dot. -/
theorem thirdFullAxisDot_mul_right244
    (u v : A3 → ℝ) (t : ℝ) :
    thirdTriadAxisDot244 u (fun i => t * v i) =
      t * thirdTriadAxisDot244 u v := by
  unfold thirdTriadAxisDot244
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Real scalar multiplication in the first argument of the physical dot. -/
theorem thirdFullAxisDot_mul_left244
    (u v : A3 → ℝ) (t : ℝ) :
    thirdTriadAxisDot244 (fun i => t * u i) v =
      t * thirdTriadAxisDot244 u v := by
  unfold thirdTriadAxisDot244
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual corrected ordered symbol is separately linear in each of its
three polarizations; the two distinct gradient contractions are retained. -/
theorem thirdFullPhysicalOrderedSymbol_pol_scaling244
    (p q r A B C : A3 → ℝ) (a b c : ℝ) :
    thirdFullPhysicalOrderedSymbol244 p q r
      (fun i => a * A i) (fun i => b * B i) (fun i => c * C i) =
    (a * b * c) * thirdFullPhysicalOrderedSymbol244 p q r A B C := by
  unfold thirdFullPhysicalOrderedSymbol244
  rw [thirdFullAxisDot_mul_left244, thirdFullAxisDot_mul_right244,
    thirdFullAxisDot_mul_left244, thirdFullAxisDot_mul_left244,
    thirdFullAxisDot_mul_right244, thirdFullAxisDot_mul_left244]
  ring

/-- The actual positive-depth Euclidean dot is symmetric, even though its
finite-sum implementation is ordered by the axis constructors. -/
theorem thirdFullAxisDot_comm244 (u v : A3 → ℝ) :
    thirdTriadAxisDot244 u v = thirdTriadAxisDot244 v u := by
  unfold thirdTriadAxisDot244
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact trilinearity persists under *all six* momentum/polarization
permutations, with no incompressibility hypotheses. -/
theorem thirdFullPhysicalSixSymbol_pol_scaling244
    (p q r A B C : A3 → ℝ) (a b c : ℝ) :
    thirdFullPhysicalSixSymbol244 p q r
      (fun i => a * A i) (fun i => b * B i) (fun i => c * C i) =
    (a * b * c) * thirdFullPhysicalSixSymbol244 p q r A B C := by
  unfold thirdFullPhysicalSixSymbol244
  rw [thirdFullPhysicalOrderedSymbol_pol_scaling244,
    thirdFullPhysicalOrderedSymbol_pol_scaling244,
    thirdFullPhysicalOrderedSymbol_pol_scaling244,
    thirdFullPhysicalOrderedSymbol_pol_scaling244,
    thirdFullPhysicalOrderedSymbol_pol_scaling244,
    thirdFullPhysicalOrderedSymbol_pol_scaling244]
  ring

/-- Normalize at the *fixed* center squared frequency. The varying
frequency is never a denominator; the zero frequency causes no singularity. -/
noncomputable def thirdFullFixedCenterTransverseGerm244
    (η ξ a : A3 → ℝ) : A3 → ℝ :=
  fun i => (thirdTriadAxisDot244 η η)⁻¹ *
    thirdFullTransversePolynomial244 ξ a i

/-- The actual frequency and its lifted polarization are perpendicular
for every frequency, independently of the location of the center. -/
theorem thirdFullFixedCenterTransverseGerm_solenoidal244
    (η ξ a : A3 → ℝ) :
    thirdTriadAxisDot244 ξ (thirdFullFixedCenterTransverseGerm244 η ξ a) = 0 := by
  change thirdTriadAxisDot244 ξ
    (fun i => (thirdTriadAxisDot244 η η)⁻¹ *
      thirdFullTransversePolynomial244 ξ a i) = 0
  rw [thirdFullAxisDot_mul_right244,
    thirdFullTransversePolynomial_solenoidal244]
  ring

/-- At a transverse, nonzero center, normalization recovers exactly the
original polarization rather than only a positive scalar multiple of it. -/
theorem thirdFullFixedCenterTransverseGerm_at_center244
    (η a : A3 → ℝ)
    (hTransverse : thirdTriadAxisDot244 η a = 0)
    (hNonzero : thirdTriadAxisDot244 η η ≠ 0) :
    thirdFullFixedCenterTransverseGerm244 η η a = a := by
  funext i
  change (thirdTriadAxisDot244 η η)⁻¹ *
      thirdFullTransversePolynomial244 η a i = a i
  rw [thirdFullTransversePolynomial_at_transverse244 η a hTransverse]
  change (thirdTriadAxisDot244 η η)⁻¹ *
    (thirdTriadAxisDot244 η η * a i) = a i
  field_simp [hNonzero] <;> ring

/-- The normalized polynomial germ is continuous *globally*, even at zero. -/
theorem thirdFullFixedCenterTransverseGerm_continuous244
    (η a : A3 → ℝ) :
    Continuous (fun ξ : A3 → ℝ => thirdFullFixedCenterTransverseGerm244 η ξ a) := by
  apply continuous_pi
  intro i
  exact continuous_const.mul
    ((continuous_apply i).comp (thirdFullTransversePolynomial_continuous244 a))

/-- On the momentum plane, use a different divergence-free germ at EACH
wave frequency p, q=-p-r, r. This is the physically relevant moving-polarization
coefficient, with no fixed-center transversality approximation. -/
noncomputable def thirdFullProjectedHermitianKernel244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) : ℝ :=
  thirdFullHermitianMomentumKernel244
    (thirdFullFixedCenterTransverseGerm244 p₀ z.1 A)
    (thirdFullFixedCenterTransverseGerm244 q₀
      (thirdFullMiddleFrequency244 z) B)
    (thirdFullFixedCenterTransverseGerm244 r₀ z.2 C) z

/-- Three independent pointwise divergence equations, including the
middle-frequency constraint q=-p-r. -/
theorem thirdFullProjectedHermitianKernel_transverse244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) :
    thirdTriadAxisDot244 z.1
      (thirdFullFixedCenterTransverseGerm244 p₀ z.1 A) = 0 ∧
    thirdTriadAxisDot244 (thirdFullMiddleFrequency244 z)
      (thirdFullFixedCenterTransverseGerm244 q₀
        (thirdFullMiddleFrequency244 z) B) = 0 ∧
    thirdTriadAxisDot244 z.2
      (thirdFullFixedCenterTransverseGerm244 r₀ z.2 C) = 0 := by
  exact ⟨thirdFullFixedCenterTransverseGerm_solenoidal244 _ _ _,
    thirdFullFixedCenterTransverseGerm_solenoidal244 _ _ _,
    thirdFullFixedCenterTransverseGerm_solenoidal244 _ _ _⟩

/-- The corrected physical six-permutation polynomial remains continuous
when the three polarizations vary with their own momentum frequencies. -/
theorem thirdFullProjectedHermitianKernel_continuous244
    (p₀ q₀ r₀ A B C : A3 → ℝ) :
    Continuous (thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C) := by
  have hP : Continuous (fun z : Pair244 =>
      thirdFullFixedCenterTransverseGerm244 p₀ z.1 A) :=
    (thirdFullFixedCenterTransverseGerm_continuous244 p₀ A).comp continuous_fst
  have hQ : Continuous (fun z : Pair244 =>
      thirdFullFixedCenterTransverseGerm244 q₀
        (thirdFullMiddleFrequency244 z) B) :=
    (thirdFullFixedCenterTransverseGerm_continuous244 q₀ B).comp
      thirdFullMiddleFrequency_continuous244
  have hR : Continuous (fun z : Pair244 =>
      thirdFullFixedCenterTransverseGerm244 r₀ z.2 C) :=
    (thirdFullFixedCenterTransverseGerm_continuous244 r₀ C).comp continuous_snd
  have hSix := thirdFullPhysicalSixSymbol_continuous244
    (fun z : Pair244 => z.1) thirdFullMiddleFrequency244
    (fun z : Pair244 => z.2)
    (fun z => thirdFullFixedCenterTransverseGerm244 p₀ z.1 A)
    (fun z => thirdFullFixedCenterTransverseGerm244 q₀
      (thirdFullMiddleFrequency244 z) B)
    (fun z => thirdFullFixedCenterTransverseGerm244 r₀ z.2 C)
    continuous_fst thirdFullMiddleFrequency_continuous244 continuous_snd
    hP hQ hR
  have hCont : Continuous (fun z : Pair244 =>
      2 * thirdFullPhysicalSixSymbol244 z.1
        (thirdFullMiddleFrequency244 z) z.2
        (thirdFullFixedCenterTransverseGerm244 p₀ z.1 A)
        (thirdFullFixedCenterTransverseGerm244 q₀
          (thirdFullMiddleFrequency244 z) B)
        (thirdFullFixedCenterTransverseGerm244 r₀ z.2 C)) :=
    continuous_const.mul hSix
  convert hCont using 1
  funext z
  exact thirdFullHermitianMomentumKernel_eq244 _ _ _ _

/-- A nonzero transverse center has exactly the OLD -192 Hermitian value,
not an approximation. The pointwise projections preserve all three center
polarizations simultaneously. -/
theorem thirdFullProjectedHermitianKernel_at_center244
    (p q r A B C : A3 → ℝ)
    (hm : ∀ i, p i + q i + r i = 0)
    (ha : thirdTriadAxisDot244 A p = 0)
    (hb : thirdTriadAxisDot244 B q = 0)
    (hc : thirdTriadAxisDot244 C r = 0)
    (hp : thirdTriadAxisDot244 p p ≠ 0)
    (hq : thirdTriadAxisDot244 q q ≠ 0)
    (hr : thirdTriadAxisDot244 r r ≠ 0) :
    thirdFullProjectedHermitianKernel244 p q r A B C (p,r) =
      thirdFullHermitianMomentumKernel244 A B C (p,r) := by
  have hMiddle : thirdFullMiddleFrequency244 (p,r) = q := by
    funext i
    dsimp [thirdFullMiddleFrequency244]
    linarith [hm i]
  unfold thirdFullProjectedHermitianKernel244
  rw [hMiddle,
    thirdFullFixedCenterTransverseGerm_at_center244 p A
      (by rw [thirdFullAxisDot_comm244]; exact ha) hp,
    thirdFullFixedCenterTransverseGerm_at_center244 q B
      (by rw [thirdFullAxisDot_comm244]; exact hb) hq,
    thirdFullFixedCenterTransverseGerm_at_center244 r C
      (by rw [thirdFullAxisDot_comm244]; exact hc) hr]

/-- Strictly signed neighborhoods survive exact frequency-dependent
incompressibility, not only fixed transverse polarizations. -/
theorem thirdFullProjectedHermitianKernel_exists_negative_closedBall244
    (p q r A B C : A3 → ℝ)
    (hm : ∀ i, p i + q i + r i = 0)
    (ha : thirdTriadAxisDot244 A p = 0)
    (hb : thirdTriadAxisDot244 B q = 0)
    (hc : thirdTriadAxisDot244 C r = 0)
    (hp : thirdTriadAxisDot244 p p ≠ 0)
    (hq : thirdTriadAxisDot244 q q ≠ 0)
    (hr : thirdTriadAxisDot244 r r ≠ 0)
    (hNeg : thirdFullHermitianMomentumKernel244 A B C (p,r) < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ Metric.closedBall (p,r) ρ,
        thirdFullProjectedHermitianKernel244 p q r A B C z < 0 := by
  have hAt : thirdFullProjectedHermitianKernel244 p q r A B C (p,r) < 0 := by
    rw [thirdFullProjectedHermitianKernel_at_center244 p q r A B C
      hm ha hb hc hp hq hr]
    exact hNeg
  have hOpen : IsOpen {z : Pair244 |
      thirdFullProjectedHermitianKernel244 p q r A B C z < 0} :=
    isOpen_lt (thirdFullProjectedHermitianKernel_continuous244 p q r A B C)
      continuous_const
  obtain ⟨ε, hε, hSub⟩ := Metric.mem_nhds_iff.mp
    (hOpen.mem_nhds hAt)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro z hz
  exact hSub (Metric.closedBall_subset_ball (half_lt_self hε) hz)

/-- Insert an arbitrary real scalar Fourier cutoff at EACH of the three
momenta, without changing the Hermitian phase. This is the precise algebraic
kernel for three windowed transverse polarization germs; a globally defined
Schwartz velocity is not yet constructed here. -/
noncomputable def thirdFullWindowedProjectedHermitianKernel244
    (p₀ q₀ r₀ A B C : A3 → ℝ)
    (w : (A3 → ℝ) → ℝ) (z : Pair244) : ℝ :=
  thirdFullHermitianMomentumKernel244
    (fun i => w z.1 * thirdFullFixedCenterTransverseGerm244 p₀ z.1 A i)
    (fun i => w (thirdFullMiddleFrequency244 z) *
      thirdFullFixedCenterTransverseGerm244 q₀
        (thirdFullMiddleFrequency244 z) B i)
    (fun i => w z.2 * thirdFullFixedCenterTransverseGerm244 r₀ z.2 C i) z

/-- Exact trilinear window factorization, with the original sixth-order
permutation sum and seventh-order odd Fourier phase preserved. -/
theorem thirdFullWindowedProjectedHermitianKernel_factor244
    (p₀ q₀ r₀ A B C : A3 → ℝ)
    (w : (A3 → ℝ) → ℝ) (z : Pair244) :
    thirdFullWindowedProjectedHermitianKernel244 p₀ q₀ r₀ A B C w z =
      (w z.1 * w (thirdFullMiddleFrequency244 z) * w z.2) *
        thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z := by
  simp only [thirdFullWindowedProjectedHermitianKernel244,
    thirdFullProjectedHermitianKernel244,
    thirdFullHermitianMomentumKernel_eq244,
    thirdFullPhysicalSixSymbol_pol_scaling244]
  ring

/-- A strictly negative projected coefficient remains strictly negative
whenever all three scalar cutoffs are strictly positive. -/
theorem thirdFullWindowedProjectedHermitianKernel_negative244
    (p₀ q₀ r₀ A B C : A3 → ℝ)
    (w : (A3 → ℝ) → ℝ) (z : Pair244)
    (hp : 0 < w z.1)
    (hq : 0 < w (thirdFullMiddleFrequency244 z))
    (hr : 0 < w z.2)
    (hNeg : thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z < 0) :
    thirdFullWindowedProjectedHermitianKernel244 p₀ q₀ r₀ A B C w z < 0 := by
  rw [thirdFullWindowedProjectedHermitianKernel_factor244]
  exact mul_neg_of_pos_of_neg (mul_pos (mul_pos hp hq) hr) hNeg

/-- Noncoherent triples with a vanishing Fourier cutoff contribute exactly
zero, an algebraic precondition for the eventual support-exclusion proof. -/
theorem thirdFullWindowedProjectedHermitianKernel_zero_of_first_window244
    (p₀ q₀ r₀ A B C : A3 → ℝ)
    (w : (A3 → ℝ) → ℝ) (z : Pair244)
    (hw : w z.1 = 0) :
    thirdFullWindowedProjectedHermitianKernel244 p₀ q₀ r₀ A B C w z = 0 := by
  rw [thirdFullWindowedProjectedHermitianKernel_factor244, hw]
  ring

/-- The previous explicit -192 triad yields an UNCONDITIONAL strictly
negative tube of fully frequency-transverse polarizations. The centers are
reconstructed because their definitions in the symbol module are private. -/
theorem thirdFullProjectedHermitianKernel_exists_solenoidal_negative_tube244 :
    ∃ (p q r A B C : A3 → ℝ) (ρ : ℝ),
      (∀ i, p i + q i + r i = 0) ∧
      thirdTriadAxisDot244 A p = 0 ∧
      thirdTriadAxisDot244 B q = 0 ∧
      thirdTriadAxisDot244 C r = 0 ∧
      0 < ρ ∧
      (∀ z ∈ Metric.closedBall (p,r) ρ,
        thirdFullProjectedHermitianKernel244 p q r A B C z < 0) := by
  let coord (x y z : ℝ) (i : A3) : ℝ :=
    if axisRank i = 0 then x else if axisRank i = 1 then y else z
  let p : A3 → ℝ := coord 1 0 0
  let q : A3 → ℝ := coord 1 1 0
  let r : A3 → ℝ := coord (-2) (-1) 0
  let A : A3 → ℝ := coord 0 1 0
  let B : A3 → ℝ := coord 1 (-1) 0
  let C : A3 → ℝ := coord 1 (-2) 0
  have hTriad :
      (∀ i, p i + q i + r i = 0) ∧
      thirdTriadAxisDot244 A p = 0 ∧
      thirdTriadAxisDot244 B q = 0 ∧
      thirdTriadAxisDot244 C r = 0 := by
    exact thirdFullPhysicalTriad_solenoidal244
  have hpNorm : thirdTriadAxisDot244 p p = 1 := by
    unfold thirdTriadAxisDot244
    rw [axis_sum_three]
    norm_num [p, coord, axisRank, xAxis, yAxis, zAxis]
  have hqNorm : thirdTriadAxisDot244 q q = 2 := by
    unfold thirdTriadAxisDot244
    rw [axis_sum_three]
    norm_num [q, coord, axisRank, xAxis, yAxis, zAxis]
  have hrNorm : thirdTriadAxisDot244 r r = 5 := by
    unfold thirdTriadAxisDot244
    rw [axis_sum_three]
    norm_num [r, coord, axisRank, xAxis, yAxis, zAxis]
  have hp : thirdTriadAxisDot244 p p ≠ 0 := by rw [hpNorm]; norm_num
  have hq : thirdTriadAxisDot244 q q ≠ 0 := by rw [hqNorm]; norm_num
  have hr : thirdTriadAxisDot244 r r ≠ 0 := by rw [hrNorm]; norm_num
  have hValue : thirdFullHermitianMomentumKernel244 A B C (p,r) = -192 := by
    rw [thirdFullHermitianMomentumKernel_at_conserving_triad244
      p q r A B C hTriad.1]
    exact thirdFullPhysicalHermitianOrbit_explicit244
  obtain ⟨ρ, hρ, hBall⟩ :=
    thirdFullProjectedHermitianKernel_exists_negative_closedBall244
      p q r A B C hTriad.1 hTriad.2.1 hTriad.2.2.1
      hTriad.2.2.2 hp hq hr (by rw [hValue]; norm_num)
  exact ⟨p, q, r, A, B, C, ρ,
    hTriad.1, hTriad.2.1, hTriad.2.2.1, hTriad.2.2.2, hρ, hBall⟩

/-- The projected solenoidal symbol has a strictly negative integral over
an actual positive-measure subset of the six-dimensional momentum plane.
This is still the POLYNOMIAL kernel, before Schwartz frequency windows. -/
theorem thirdFullProjectedHermitianKernel_exists_negative_local_integral244 :
    ∃ (p q r A B C : A3 → ℝ) (ρ : ℝ),
      0 < ρ ∧
      (∫ z in Metric.closedBall (p,r) ρ,
        thirdFullProjectedHermitianKernel244 p q r A B C z
          ∂(volume.prod volume)) < 0 := by
  obtain ⟨p, q, r, A, B, C, ρ, hm, ha, hb, hc, hρ, hNeg⟩ :=
    thirdFullProjectedHermitianKernel_exists_solenoidal_negative_tube244
  let K : Pair244 → ℝ := thirdFullProjectedHermitianKernel244 p q r A B C
  let s : Set Pair244 := Metric.closedBall (p,r) ρ
  have hCompact : IsCompact s := isCompact_closedBall _ _
  have hMeas : MeasurableSet s := measurableSet_closedBall
  have hInt : IntegrableOn (fun z => -K z) s (volume.prod volume) :=
    (thirdFullProjectedHermitianKernel_continuous244 p q r A B C).neg.continuousOn.integrableOn_compact
      hCompact
  have hNonneg : 0 ≤ᵐ[(volume.prod volume).restrict s] (fun z => -K z) := by
    filter_upwards [ae_restrict_mem hMeas] with z hz
    exact (neg_pos.mpr (hNeg z hz)).le
  have hBall : Metric.ball (p,r) ρ ⊆ Function.support (fun z => -K z) ∩ s := by
    intro z hz
    constructor
    · change -K z ≠ 0
      exact ne_of_gt (neg_pos.mpr (hNeg z (Metric.ball_subset_closedBall hz)))
    · exact Metric.ball_subset_closedBall hz
  have hMeasure :
      0 < (volume.prod volume) (Function.support (fun z => -K z) ∩ s) :=
    (Metric.measure_ball_pos (volume.prod volume) (p,r) hρ).trans_le
      (measure_mono hBall)
  have hIntegral : 0 < ∫ z in s, -K z ∂(volume.prod volume) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hMeasure
  simp only [integral_neg] at hIntegral
  refine ⟨p, q, r, A, B, C, ρ, hρ, ?_⟩
  change (∫ z in s, K z ∂(volume.prod volume)) < 0
  exact neg_pos.mp hIntegral

end
end PrimeTensor.FirstMonomialTriad

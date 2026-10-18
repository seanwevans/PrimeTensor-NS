import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealFourierIdentification244
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
# Genuine open momentum-plane sign for the corrected full-third Fourier symbol

The earlier finite-dimensional proof computes the complete corrected six-order
third-transport derivative symbol at a momentum-conserving solenoidal triad,
then includes its seven-derivative Fourier phase and Hermitian reflection.
Its exact signed orbit coefficient is -192.

Here the dependent momentum q=-(p+r) is enforced on the actual positive-depth
three-axis Fourier carrier. We prove that the phase-correct orbit coefficient
is continuous in both free momenta, that the explicit solenoidal resonant
triad belongs to a strictly negative OPEN neighborhood, and that a sufficiently
small closed six-dimensional momentum-pair ball has strictly negative signed
integral. Unlike a pointwise coefficient, this last integral is not supported
on a measure-zero set.

This is the UNWEIGHTED finite-polynomial sign kernel, not yet the Schwartz
Fourier-amplitude integral. Genuine compactly supported Hermitian solenoidal
Schwartz Fourier packets and exclusion of all other resonances remain to be
proved; no static absorption counterexample is asserted in this module.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set Filter PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 600000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Pair244 := (A3 → ℝ) × (A3 → ℝ)

noncomputable local instance axisFintypeLocalTube244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Euclidean dot on PrimeTensor's actual positive-depth axis carrier is
jointly continuous in any continuously parameterized pair of vectors. -/
theorem thirdTriadAxisDot_continuous_of_continuous244
    {X : Type*} [TopologicalSpace X]
    (v w : X → A3 → ℝ) (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x => thirdTriadAxisDot244 (v x) (w x)) := by
  classical
  change Continuous (fun x => ∑ i : A3, v x i * w x i)
  apply continuous_finsetSum Finset.univ
  intro i _
  exact ((continuous_apply i).comp hv).mul ((continuous_apply i).comp hw)

/-- Continuity of the *corrected* ordered physical symbol, retaining the
distinct polarization contractions of its four gradient channels. -/
theorem thirdFullPhysicalOrderedSymbol_continuous244
    {X : Type*} [TopologicalSpace X]
    (p q r A B C : X → A3 → ℝ)
    (hp : Continuous p) (hq : Continuous q) (hr : Continuous r)
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) :
    Continuous (fun x => thirdFullPhysicalOrderedSymbol244
      (p x) (q x) (r x) (A x) (B x) (C x)) := by
  have ha := thirdTriadAxisDot_continuous_of_continuous244 p q hp hq
  have hb := thirdTriadAxisDot_continuous_of_continuous244 p r hp hr
  have hAC := thirdTriadAxisDot_continuous_of_continuous244 A C hA hC
  have hBr := thirdTriadAxisDot_continuous_of_continuous244 B r hB hr
  have hAB := thirdTriadAxisDot_continuous_of_continuous244 A B hA hB
  have hCq := thirdTriadAxisDot_continuous_of_continuous244 C q hC hq
  change Continuous (fun x =>
    (thirdTriadAxisDot244 (A x) (C x) * thirdTriadAxisDot244 (B x) (r x)) *
      ((thirdTriadAxisDot244 (p x) (q x)) ^ 3 +
        3 * (thirdTriadAxisDot244 (p x) (q x)) ^ 2 *
          thirdTriadAxisDot244 (p x) (r x)) +
    (thirdTriadAxisDot244 (A x) (B x) * thirdTriadAxisDot244 (C x) (q x)) *
      (3 * (thirdTriadAxisDot244 (p x) (q x)) ^ 2 *
        thirdTriadAxisDot244 (p x) (r x)))
  exact ((hAC.mul hBr).mul ((ha.pow 3).add
    ((continuous_const.mul (ha.pow 2)).mul hb))).add
    ((hAB.mul hCq).mul ((continuous_const.mul (ha.pow 2)).mul hb))

/-- Exact six-order continuity. No solenoidal or momentum hypotheses are
needed, so the sign is stable under simultaneous perturbations. -/
theorem thirdFullPhysicalSixSymbol_continuous244
    {X : Type*} [TopologicalSpace X]
    (p q r A B C : X → A3 → ℝ)
    (hp : Continuous p) (hq : Continuous q) (hr : Continuous r)
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) :
    Continuous (fun x => thirdFullPhysicalSixSymbol244
      (p x) (q x) (r x) (A x) (B x) (C x)) := by
  have h1 := thirdFullPhysicalOrderedSymbol_continuous244
    p q r A B C hp hq hr hA hB hC
  have h2 := thirdFullPhysicalOrderedSymbol_continuous244
    p r q A C B hp hr hq hA hC hB
  have h3 := thirdFullPhysicalOrderedSymbol_continuous244
    q p r B A C hq hp hr hB hA hC
  have h4 := thirdFullPhysicalOrderedSymbol_continuous244
    q r p B C A hq hr hp hB hC hA
  have h5 := thirdFullPhysicalOrderedSymbol_continuous244
    r p q C A B hr hp hq hC hA hB
  have h6 := thirdFullPhysicalOrderedSymbol_continuous244
    r q p C B A hr hq hp hC hB hA
  have hSum := ((((h1.add h2).add h3).add h4).add h5).add h6
  convert hSum using 1 <;>
    (funext x; simp only [thirdFullPhysicalSixSymbol244, Pi.add_apply])

/-- The third momentum is always chosen from the actual conservation law. -/
def thirdFullMiddleFrequency244 (z : Pair244) : A3 → ℝ :=
  fun i => -(z.1 i + z.2 i)

theorem thirdFullMiddleFrequency_continuous244 :
    Continuous thirdFullMiddleFrequency244 := by
  apply continuous_pi
  intro i
  exact (((continuous_apply i).comp continuous_fst).add
    ((continuous_apply i).comp continuous_snd)).neg

/-- The phase-correct Hermitian pair restricted to the physical momentum
plane, with fixed three polarizations. -/
noncomputable def thirdFullHermitianMomentumKernel244
    (A B C : A3 → ℝ) (z : Pair244) : ℝ :=
  thirdFullPhysicalHermitianOrbit244
    z.1 (thirdFullMiddleFrequency244 z) z.2 A B C Complex.I

/-- No hidden or sign-adjusted phase: the kernel is exactly twice the
six-permutation polynomial because `(Complex.I).im = 1`. -/
theorem thirdFullHermitianMomentumKernel_eq244
    (A B C : A3 → ℝ) (z : Pair244) :
    thirdFullHermitianMomentumKernel244 A B C z =
      2 * thirdFullPhysicalSixSymbol244
        z.1 (thirdFullMiddleFrequency244 z) z.2 A B C := by
  unfold thirdFullHermitianMomentumKernel244
  rw [thirdFullPhysicalHermitianOrbit_eq244]
  norm_num [Complex.I_im]

/-- The full phase-correct polynomial, not only one ordered monomial, is
continuous on the *six-dimensional* momentum-pair plane. -/
theorem thirdFullHermitianMomentumKernel_continuous244
    (A B C : A3 → ℝ) :
    Continuous (thirdFullHermitianMomentumKernel244 A B C) := by
  have hSix := thirdFullPhysicalSixSymbol_continuous244
    (fun z : Pair244 => z.1)
    thirdFullMiddleFrequency244
    (fun z : Pair244 => z.2)
    (fun _ : Pair244 => A) (fun _ : Pair244 => B) (fun _ : Pair244 => C)
    continuous_fst thirdFullMiddleFrequency_continuous244 continuous_snd
    continuous_const continuous_const continuous_const
  have hCont : Continuous (fun z : Pair244 =>
      2 * thirdFullPhysicalSixSymbol244
        z.1 (thirdFullMiddleFrequency244 z) z.2 A B C) :=
    continuous_const.mul hSix
  convert hCont using 1
  funext z
  exact thirdFullHermitianMomentumKernel_eq244 A B C z

/-- Substitute the momentum equation before evaluating the signed orbit;
this avoids identifying the independent q with `-(p+r)` by fiat. -/
theorem thirdFullHermitianMomentumKernel_at_conserving_triad244
    (p q r A B C : A3 → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0) :
    thirdFullHermitianMomentumKernel244 A B C (p,r) =
      thirdFullPhysicalHermitianOrbit244 p q r A B C Complex.I := by
  have hq : thirdFullMiddleFrequency244 (p,r) = q := by
    funext i
    dsimp [thirdFullMiddleFrequency244]
    have hi := hMomentum i
    linarith
  simp only [thirdFullHermitianMomentumKernel244, hq]

/-- The committed explicit solenoidal triad has the phase-correct orbit
value -192. We extract it without changing its private constructor data. -/
theorem thirdFullHermitianMomentumKernel_exists_negative_center244 :
    ∃ (p q r A B C : A3 → ℝ),
      (∀ i, p i + q i + r i = 0) ∧
      thirdTriadAxisDot244 A p = 0 ∧
      thirdTriadAxisDot244 B q = 0 ∧
      thirdTriadAxisDot244 C r = 0 ∧
      thirdFullHermitianMomentumKernel244 A B C (p,r) = -192 := by
  -- Reconstruct the six explicit witnesses using the same positive-axis
  -- coordinate formula as the committed physical-symbol theorem.  Its
  -- witness names are private in that imported module, so metavariable
  -- placeholders cannot infer them from the closed theorems.
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
  have hOrbit :
      thirdFullPhysicalHermitianOrbit244 p q r A B C Complex.I = -192 := by
    exact thirdFullPhysicalHermitianOrbit_explicit244
  refine ⟨p, q, r, A, B, C,
    hTriad.1, hTriad.2.1, hTriad.2.2.1, hTriad.2.2.2, ?_⟩
  rw [thirdFullHermitianMomentumKernel_at_conserving_triad244
    p q r A B C hTriad.1]
  exact hOrbit

/-- Continuity promotes a genuinely negative center value to strict
negative sign throughout an OPEN momentum-pair neighborhood. -/
theorem thirdFullHermitianMomentumKernel_eventually_negative244
    (A B C : A3 → ℝ) (z₀ : Pair244)
    (hNeg : thirdFullHermitianMomentumKernel244 A B C z₀ < 0) :
    ∀ᶠ z in 𝓝 z₀, thirdFullHermitianMomentumKernel244 A B C z < 0 := by
  have hOpen : IsOpen {z : Pair244 |
      thirdFullHermitianMomentumKernel244 A B C z < 0} :=
    isOpen_lt (thirdFullHermitianMomentumKernel_continuous244 A B C)
      continuous_const
  exact hOpen.mem_nhds hNeg

/-- A strictly signed six-dimensional closed ball exists for every negative
center; the radius is chosen INSIDE the open sign neighborhood. -/
theorem thirdFullHermitianMomentumKernel_exists_negative_closedBall244
    (A B C : A3 → ℝ) (z₀ : Pair244)
    (hNeg : thirdFullHermitianMomentumKernel244 A B C z₀ < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ Metric.closedBall z₀ ρ,
        thirdFullHermitianMomentumKernel244 A B C z < 0 := by
  obtain ⟨ε, hε, hSub⟩ := Metric.mem_nhds_iff.mp
    (thirdFullHermitianMomentumKernel_eventually_negative244 A B C z₀ hNeg)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro z hz
  exact hSub (Metric.closedBall_subset_ball (half_lt_self hε) hz)

/-- Thus the explicit -192 center has a whole strictly negative OPEN tube.
The same computation survives a nonzero-volume neighborhood in the actual
momentum-conserving frequency space. -/
theorem thirdFullHermitianMomentumKernel_exists_negative_tube244 :
    ∃ (A B C : A3 → ℝ) (z₀ : Pair244) (ρ : ℝ),
      0 < ρ ∧
      (∀ z ∈ Metric.closedBall z₀ ρ,
        thirdFullHermitianMomentumKernel244 A B C z < 0) := by
  obtain ⟨p, q, r, A, B, C, hm, ha, hb, hc, hValue⟩ :=
    thirdFullHermitianMomentumKernel_exists_negative_center244
  obtain ⟨ρ, hρ, hBall⟩ :=
    thirdFullHermitianMomentumKernel_exists_negative_closedBall244
      A B C (p,r) (by rw [hValue]; norm_num)
  exact ⟨A, B, C, (p,r), ρ, hρ, hBall⟩


/-- A genuinely positive-measure local Fourier-pair integral has the same
strict sign as the full-third phase-correct six-order center. This does not
extend the sign to the unlocalized Schwartz amplitude integral. -/
theorem thirdFullHermitianMomentumKernel_exists_negative_local_integral244 :
    ∃ (A B C : A3 → ℝ) (z₀ : Pair244) (ρ : ℝ),
      0 < ρ ∧
      (∫ z in Metric.closedBall z₀ ρ,
        thirdFullHermitianMomentumKernel244 A B C z
          ∂(volume.prod volume)) < 0 := by
  obtain ⟨A, B, C, z₀, ρ, hρ, hNeg⟩ :=
    thirdFullHermitianMomentumKernel_exists_negative_tube244
  let s : Set Pair244 := Metric.closedBall z₀ ρ
  let K : Pair244 → ℝ := thirdFullHermitianMomentumKernel244 A B C
  have hCompact : IsCompact s := isCompact_closedBall _ _
  have hMeas : MeasurableSet s := measurableSet_closedBall
  have hInt : IntegrableOn (fun z => -K z) s (volume.prod volume) :=
    (thirdFullHermitianMomentumKernel_continuous244 A B C).neg.continuousOn.integrableOn_compact
      hCompact
  have hNonneg : 0 ≤ᵐ[(volume.prod volume).restrict s] (fun z => -K z) := by
    filter_upwards [ae_restrict_mem hMeas] with z hz
    exact (neg_pos.mpr (hNeg z hz)).le
  have hBall : Metric.ball z₀ ρ ⊆ Function.support (fun z => -K z) ∩ s := by
    intro z hz
    constructor
    · change -K z ≠ 0
      exact ne_of_gt (neg_pos.mpr (hNeg z (Metric.ball_subset_closedBall hz)))
    · exact Metric.ball_subset_closedBall hz
  have hMeasure :
      0 < (volume.prod volume) (Function.support (fun z => -K z) ∩ s) :=
    (Metric.measure_ball_pos (volume.prod volume) z₀ hρ).trans_le
      (measure_mono hBall)
  have hIntegral : 0 < ∫ z in s, -K z ∂(volume.prod volume) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hMeasure
  simp only [integral_neg] at hIntegral
  refine ⟨A, B, C, z₀, ρ, hρ, ?_⟩
  change (∫ z in s, K z ∂(volume.prod volume)) < 0
  exact neg_pos.mp hIntegral

/-- Polynomial Leray numerator on PrimeTensor's positive-depth axis carrier:
there is NO division by a possibly vanishing frequency norm. -/
noncomputable def thirdFullTransversePolynomial244
    (ξ a : A3 → ℝ) (i : A3) : ℝ :=
  thirdTriadAxisDot244 ξ ξ * a i -
    thirdTriadAxisDot244 ξ a * ξ i

private theorem thirdFullDot_sub244
    (ξ a b : A3 → ℝ) :
    thirdTriadAxisDot244 ξ (fun i => a i - b i) =
      thirdTriadAxisDot244 ξ a - thirdTriadAxisDot244 ξ b := by
  unfold thirdTriadAxisDot244
  simp only [mul_sub, Finset.sum_sub_distrib]

private theorem thirdFullDot_const_mul244
    (ξ a : A3 → ℝ) (t : ℝ) :
    thirdTriadAxisDot244 ξ (fun i => t * a i) =
      t * thirdTriadAxisDot244 ξ a := by
  unfold thirdTriadAxisDot244
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The polynomial Leray lift preserves solenoidality for every frequency,
including ξ=0. This is the frequency-varying transverse germ needed for
localizing the strict-sign tube into a genuine divergence-free packet. -/
theorem thirdFullTransversePolynomial_solenoidal244
    (ξ a : A3 → ℝ) :
    thirdTriadAxisDot244 ξ (thirdFullTransversePolynomial244 ξ a) = 0 := by
  change thirdTriadAxisDot244 ξ (fun i =>
    (thirdTriadAxisDot244 ξ ξ) * a i -
      (thirdTriadAxisDot244 ξ a) * ξ i) = 0
  rw [thirdFullDot_sub244, thirdFullDot_const_mul244,
    thirdFullDot_const_mul244]
  ring

/-- At a solenoidal center the polynomial lift reproduces the original
polarization multiplied by the center's nonnegative squared frequency norm. -/
theorem thirdFullTransversePolynomial_at_transverse244
    (ξ a : A3 → ℝ)
    (ha : thirdTriadAxisDot244 ξ a = 0) :
    thirdFullTransversePolynomial244 ξ a =
      fun i => thirdTriadAxisDot244 ξ ξ * a i := by
  funext i
  simp only [thirdFullTransversePolynomial244, ha, zero_mul, sub_zero]

/-- The transverse polynomial lift is continuous in the carrier frequency.
This is a key analytical input for the future compact Schwartz cutoff. -/
theorem thirdFullTransversePolynomial_continuous244
    (a : A3 → ℝ) :
    Continuous (fun ξ : A3 → ℝ => thirdFullTransversePolynomial244 ξ a) := by
  have hNorm := thirdTriadAxisDot_continuous_of_continuous244
    (fun ξ : A3 → ℝ => ξ) (fun ξ : A3 → ℝ => ξ)
    continuous_id continuous_id
  have hMixed := thirdTriadAxisDot_continuous_of_continuous244
    (fun ξ : A3 → ℝ => ξ) (fun _ : A3 → ℝ => a)
    continuous_id continuous_const
  apply continuous_pi
  intro i
  exact (hNorm.mul continuous_const).sub
    (hMixed.mul (continuous_apply i))

end
end PrimeTensor.FirstMonomialTriad

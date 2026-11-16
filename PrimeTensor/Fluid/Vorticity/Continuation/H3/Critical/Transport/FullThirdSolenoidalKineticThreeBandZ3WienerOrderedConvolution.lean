import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandWienerKineticCharge
import Mathlib.Tactic

/-!
# Actual Z3 Fourier geometry and untruncated ordered Wiener convolution

This module replaces the arbitrary index set in the preceding finite ordered
kernel lemma with the actual periodic Fourier frequency lattice Z^3.

The exponential weight exp(r * m(n)), where m(n) = sum |n_j|, is
submultiplicative for r >= 0.  Its submultiplicativity yields two universal
finite-support estimates: the ordinary convolution and the advection kernel
with the full differentiated frequency m(q).  The estimates involve all
ordered input pairs and contain NO cardinality or Galerkin cutoff constant.

This is the finite Fourier algebra required by the shrinking-radius Wiener
method.  It is not yet a formal construction of periodic Navier--Stokes
solutions.  Identifying the actual complex Leray-projected quadratic symbol
with the real nonnegative kernel below, differentiating the time-varying
weighted norm, and passing to a common infinite-dimensional solution remain
separate and explicit obligations.

The real bridge is used only for Fourier arithmetic; no native
PrimeMultiset or PrimeRatio additive structure is introduced.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- The genuine integer three-dimensional Fourier lattice. -/
abbrev thirdFullThreeBandZ3Index244 := Fin 3 → ℤ

/-- Real-valued Fourier l1-degree, equal to a nonnegative integer on Z^3. -/
def thirdFullThreeBandZ3Degree244
    (n : thirdFullThreeBandZ3Index244) : ℝ :=
  ∑ j : Fin 3, |(n j : ℝ)|

/-- Analytic Fourier weight. For r=log(R), this is R^m(n). -/
def thirdFullThreeBandZ3Weight244
    (r : ℝ) (n : thirdFullThreeBandZ3Index244) : ℝ :=
  Real.exp (r * thirdFullThreeBandZ3Degree244 n)

theorem thirdFullThreeBand_z3Degree_nonneg244
    (n : thirdFullThreeBandZ3Index244) :
    0 ≤ thirdFullThreeBandZ3Degree244 n := by
  unfold thirdFullThreeBandZ3Degree244
  apply Finset.sum_nonneg
  intro j hj
  exact abs_nonneg _

/-- Exact lattice triangle inequality, not an abstract kernel assumption. -/
theorem thirdFullThreeBand_z3Degree_add_le244
    (p q : thirdFullThreeBandZ3Index244) :
    thirdFullThreeBandZ3Degree244 (p + q) ≤
      thirdFullThreeBandZ3Degree244 p +
        thirdFullThreeBandZ3Degree244 q := by
  unfold thirdFullThreeBandZ3Degree244
  calc
    (∑ j : Fin 3, |((p + q) j : ℝ)|) ≤
        ∑ j : Fin 3, (|(p j : ℝ)| + |(q j : ℝ)|) := by
          apply Finset.sum_le_sum
          intro j hj
          simpa only [Pi.add_apply, Int.cast_add] using
            (abs_add_le (p j : ℝ) (q j : ℝ))
    _ = (∑ j : Fin 3, |(p j : ℝ)|) +
          (∑ j : Fin 3, |(q j : ℝ)|) := by
            rw [Finset.sum_add_distrib]

theorem thirdFullThreeBand_z3Weight_pos244
    (r : ℝ) (n : thirdFullThreeBandZ3Index244) :
    0 < thirdFullThreeBandZ3Weight244 r n := by
  unfold thirdFullThreeBandZ3Weight244
  exact Real.exp_pos _

theorem thirdFullThreeBand_z3Weight_monotone244
    (r : ℝ) (hr : 0 ≤ r)
    (p q : thirdFullThreeBandZ3Index244)
    (hDegree : thirdFullThreeBandZ3Degree244 p ≤
      thirdFullThreeBandZ3Degree244 q) :
    thirdFullThreeBandZ3Weight244 r p ≤
      thirdFullThreeBandZ3Weight244 r q := by
  unfold thirdFullThreeBandZ3Weight244
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hDegree hr)

/-- All Z3 frequency sums obey the analytic convolution weight inequality. -/
theorem thirdFullThreeBand_z3Weight_add_le_mul244
    (r : ℝ) (hr : 0 ≤ r)
    (p q : thirdFullThreeBandZ3Index244) :
    thirdFullThreeBandZ3Weight244 r (p + q) ≤
      thirdFullThreeBandZ3Weight244 r p *
        thirdFullThreeBandZ3Weight244 r q := by
  have hDegree := thirdFullThreeBand_z3Degree_add_le244 p q
  calc
    thirdFullThreeBandZ3Weight244 r (p + q) =
        Real.exp (r * thirdFullThreeBandZ3Degree244 (p + q)) := rfl
    _ ≤ Real.exp (r * (thirdFullThreeBandZ3Degree244 p +
          thirdFullThreeBandZ3Degree244 q)) :=
        Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hDegree hr)
    _ = thirdFullThreeBandZ3Weight244 r p *
          thirdFullThreeBandZ3Weight244 r q := by
        simp [thirdFullThreeBandZ3Weight244, mul_add, Real.exp_add]

/-- Complete ordered convolution for arbitrary finite frequency supports.
No assumption is made that the output frequency is in either support. -/
theorem thirdFullThreeBand_z3OrderedWienerBound244
    (r : ℝ) (hr : 0 ≤ r)
    (s t : Finset thirdFullThreeBandZ3Index244)
    (a b : thirdFullThreeBandZ3Index244 → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hb : ∀ q, 0 ≤ b q) :
    (∑ p ∈ s, ∑ q ∈ t,
        thirdFullThreeBandZ3Weight244 r (p + q) * a p * b q) ≤
      (∑ p ∈ s, thirdFullThreeBandZ3Weight244 r p * a p) *
      (∑ q ∈ t, thirdFullThreeBandZ3Weight244 r q * b q) := by
  classical
  have hpair (p q : thirdFullThreeBandZ3Index244) :
      thirdFullThreeBandZ3Weight244 r (p + q) * a p * b q ≤
        (thirdFullThreeBandZ3Weight244 r p * a p) *
        (thirdFullThreeBandZ3Weight244 r q * b q) := by
    have hw := thirdFullThreeBand_z3Weight_add_le_mul244 r hr p q
    have hprod : 0 ≤ a p * b q := mul_nonneg (ha p) (hb q)
    calc
      thirdFullThreeBandZ3Weight244 r (p + q) * a p * b q =
          thirdFullThreeBandZ3Weight244 r (p + q) * (a p * b q) := by ring
      _ ≤ (thirdFullThreeBandZ3Weight244 r p *
              thirdFullThreeBandZ3Weight244 r q) * (a p * b q) :=
            mul_le_mul_of_nonneg_right hw hprod
      _ = (thirdFullThreeBandZ3Weight244 r p * a p) *
            (thirdFullThreeBandZ3Weight244 r q * b q) := by ring
  calc
    _ ≤ ∑ p ∈ s, ∑ q ∈ t,
          (thirdFullThreeBandZ3Weight244 r p * a p) *
          (thirdFullThreeBandZ3Weight244 r q * b q) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        exact hpair p q
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- The differentiated variable q receives its true l1-frequency factor.
This majorizes all ordered Fourier transport interactions without silently
assuming six-mode closure or restricting newly generated output modes. -/
theorem thirdFullThreeBand_z3OrderedDerivativeWienerBound244
    (r : ℝ) (hr : 0 ≤ r)
    (s t : Finset thirdFullThreeBandZ3Index244)
    (a b : thirdFullThreeBandZ3Index244 → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hb : ∀ q, 0 ≤ b q) :
    (∑ p ∈ s, ∑ q ∈ t,
        thirdFullThreeBandZ3Weight244 r (p + q) *
          thirdFullThreeBandZ3Degree244 q * a p * b q) ≤
      (∑ p ∈ s, thirdFullThreeBandZ3Weight244 r p * a p) *
      (∑ q ∈ t, thirdFullThreeBandZ3Weight244 r q *
          thirdFullThreeBandZ3Degree244 q * b q) := by
  classical
  have hpair (p q : thirdFullThreeBandZ3Index244) :
      thirdFullThreeBandZ3Weight244 r (p + q) *
          thirdFullThreeBandZ3Degree244 q * a p * b q ≤
        (thirdFullThreeBandZ3Weight244 r p * a p) *
        (thirdFullThreeBandZ3Weight244 r q *
          thirdFullThreeBandZ3Degree244 q * b q) := by
    have hw := thirdFullThreeBand_z3Weight_add_le_mul244 r hr p q
    have hprod : 0 ≤ thirdFullThreeBandZ3Degree244 q *
        (a p * b q) :=
      mul_nonneg (thirdFullThreeBand_z3Degree_nonneg244 q)
        (mul_nonneg (ha p) (hb q))
    calc
      thirdFullThreeBandZ3Weight244 r (p + q) *
          thirdFullThreeBandZ3Degree244 q * a p * b q =
          thirdFullThreeBandZ3Weight244 r (p + q) *
            (thirdFullThreeBandZ3Degree244 q * (a p * b q)) := by ring
      _ ≤ (thirdFullThreeBandZ3Weight244 r p *
              thirdFullThreeBandZ3Weight244 r q) *
            (thirdFullThreeBandZ3Degree244 q * (a p * b q)) :=
          mul_le_mul_of_nonneg_right hw hprod
      _ = (thirdFullThreeBandZ3Weight244 r p * a p) *
            (thirdFullThreeBandZ3Weight244 r q *
              thirdFullThreeBandZ3Degree244 q * b q) := by ring
  calc
    _ ≤ ∑ p ∈ s, ∑ q ∈ t,
          (thirdFullThreeBandZ3Weight244 r p * a p) *
          (thirdFullThreeBandZ3Weight244 r q *
            thirdFullThreeBandZ3Degree244 q * b q) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        exact hpair p q
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- A finite Galerkin-kernel interface: once the Euclidean/Leray source of
an ordered pair is controlled by |q|_1 a(p)b(q), the ACTUAL lattice weight
forces a uniform W_r * D_r majorant. The remaining source identification is
not hidden as an axiom. -/
theorem thirdFullThreeBand_z3GalerkinSourceMajorant244
    (r : ℝ) (hr : 0 ≤ r)
    (s t : Finset thirdFullThreeBandZ3Index244)
    (a b : thirdFullThreeBandZ3Index244 → ℝ)
    (K : thirdFullThreeBandZ3Index244 →
        thirdFullThreeBandZ3Index244 → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hb : ∀ q, 0 ≤ b q)
    (hSymbol : ∀ p ∈ s, ∀ q ∈ t,
       K p q ≤ thirdFullThreeBandZ3Weight244 r (p + q) *
         thirdFullThreeBandZ3Degree244 q * a p * b q) :
    (∑ p ∈ s, ∑ q ∈ t, K p q) ≤
      (∑ p ∈ s, thirdFullThreeBandZ3Weight244 r p * a p) *
      (∑ q ∈ t, thirdFullThreeBandZ3Weight244 r q *
          thirdFullThreeBandZ3Degree244 q * b q) := by
  classical
  calc
    _ ≤ ∑ p ∈ s, ∑ q ∈ t,
        thirdFullThreeBandZ3Weight244 r (p + q) *
          thirdFullThreeBandZ3Degree244 q * a p * b q := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        exact hSymbol p hp q hq
    _ ≤ _ := thirdFullThreeBand_z3OrderedDerivativeWienerBound244
      r hr s t a b ha hb

end
end PrimeTensor.FirstMonomialTriad

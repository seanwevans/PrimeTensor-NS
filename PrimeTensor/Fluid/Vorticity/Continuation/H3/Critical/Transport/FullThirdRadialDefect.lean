import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalPhaseOrbit244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadCancellation
import Mathlib.Tactic

/-!
# The complete signed third-order Fourier orbit factors through radial defects

The CORRECTED complete third-order gradient-plus-interpolation six-permutation
symbol is exactly a sum of three terms, each containing a DIFFERENCE of the
squared lengths of two frequencies. This is a genuine cancellation of the
entire physical full-third symbol, not merely the first monomial.

No denominator, radial cutoff, or smoothness assumption is introduced. The
only hypotheses are momentum conservation and the three exact solenoidal
polarization constraints. The identity gives vanishing on balanced frequency
spheres and a quantitative near-balanced radial-defect estimate.

A same-sphere cancellation alone does not prove H3 regularity. The next
analytic frontier is to integrate the radial-defect factor over physical
Fourier triads without discarding the gain in absolute-value estimates.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 1800000

private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeFullThirdRadialDefect
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Cubic divided difference of x ↦ x³ + 3zx² + 3z²x. -/
def thirdFullRadialDefectMultiplier244 (x y z : ℝ) : ℝ :=
  x ^ 2 + x * y + y ^ 2 + 3 * z * (x + y) + 3 * z ^ 2

/-- The actual three-axis dot agrees with the generic finite-dimensional
Euclidean pairing used by the original triad cancellation. -/
private theorem fullThirdDot_comm (x y : A3 → ℝ) :
    thirdTriadAxisDot244 x y = thirdTriadAxisDot244 y x := by
  simpa only [thirdTriadAxisDot244, dot] using
    (dot_comm x y)

/-- No division by a frequency: contract the exact momentum law against
an arbitrary polarization. -/
private theorem fullThirdDot_momentum
    (p q r x : A3 → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0) :
    thirdTriadAxisDot244 p x + thirdTriadAxisDot244 q x +
      thirdTriadAxisDot244 r x = 0 := by
  simpa only [thirdTriadAxisDot244, dot] using
    (momentum_dot p q r x hMomentum)

/-- The complete physical six-symbol is made entirely from squared-radius
differences, once the actual incompressibility and momentum constraints are
used. The two gradient polarization contractions stay DISTINCT: no false
single-order gradient simplification is made. -/
theorem thirdFullPhysicalSix_radialDefect_factorization244
    (p q r A B C : A3 → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (hA : thirdTriadAxisDot244 A p = 0)
    (hB : thirdTriadAxisDot244 B q = 0)
    (hC : thirdTriadAxisDot244 C r = 0) :
    thirdFullPhysicalSixSymbol244 p q r A B C =
      (thirdTriadAxisDot244 A C * thirdTriadAxisDot244 B r) *
        (thirdTriadAxisDot244 r r - thirdTriadAxisDot244 p p) *
        thirdFullRadialDefectMultiplier244
          (thirdTriadAxisDot244 p q)
          (thirdTriadAxisDot244 q r)
          (thirdTriadAxisDot244 p r) +
      (thirdTriadAxisDot244 A B * thirdTriadAxisDot244 C q) *
        (thirdTriadAxisDot244 q q - thirdTriadAxisDot244 p p) *
        thirdFullRadialDefectMultiplier244
          (thirdTriadAxisDot244 p r)
          (thirdTriadAxisDot244 q r)
          (thirdTriadAxisDot244 p q) +
      (thirdTriadAxisDot244 B C * thirdTriadAxisDot244 A r) *
        (thirdTriadAxisDot244 r r - thirdTriadAxisDot244 q q) *
        thirdFullRadialDefectMultiplier244
          (thirdTriadAxisDot244 p q)
          (thirdTriadAxisDot244 p r)
          (thirdTriadAxisDot244 q r) := by
  have hP := fullThirdDot_momentum p q r p hMomentum
  have hQ := fullThirdDot_momentum p q r q hMomentum
  have hR := fullThirdDot_momentum p q r r hMomentum
  rw [fullThirdDot_comm q p, fullThirdDot_comm r p] at hP
  rw [fullThirdDot_comm r q] at hQ
  have hRadRP : thirdTriadAxisDot244 p q - thirdTriadAxisDot244 q r =
      thirdTriadAxisDot244 r r - thirdTriadAxisDot244 p p := by
    linarith only [hP, hR]
  have hRadQP : thirdTriadAxisDot244 p r - thirdTriadAxisDot244 q r =
      thirdTriadAxisDot244 q q - thirdTriadAxisDot244 p p := by
    linarith only [hP, hQ]
  have hRadRQ : thirdTriadAxisDot244 p q - thirdTriadAxisDot244 p r =
      thirdTriadAxisDot244 r r - thirdTriadAxisDot244 q q := by
    linarith only [hQ, hR]
  have hmA := fullThirdDot_momentum p q r A hMomentum
  have hmB := fullThirdDot_momentum p q r B hMomentum
  have hmC := fullThirdDot_momentum p q r C hMomentum
  rw [fullThirdDot_comm p A, fullThirdDot_comm q A,
    fullThirdDot_comm r A] at hmA
  rw [fullThirdDot_comm p B, fullThirdDot_comm q B,
    fullThirdDot_comm r B] at hmB
  rw [fullThirdDot_comm p C, fullThirdDot_comm q C,
    fullThirdDot_comm r C] at hmC
  have hAq : thirdTriadAxisDot244 A q = -thirdTriadAxisDot244 A r := by
    linarith only [hmA, hA]
  have hBp : thirdTriadAxisDot244 B p = -thirdTriadAxisDot244 B r := by
    linarith only [hmB, hB]
  have hCp : thirdTriadAxisDot244 C p = -thirdTriadAxisDot244 C q := by
    linarith only [hmC, hC]
  have hqp := fullThirdDot_comm q p
  have hrp := fullThirdDot_comm r p
  have hrq := fullThirdDot_comm r q
  have hBA := fullThirdDot_comm B A
  have hCA := fullThirdDot_comm C A
  have hCB := fullThirdDot_comm C B
  rw [← hRadRP, ← hRadQP, ← hRadRQ]
  unfold thirdFullPhysicalSixSymbol244 thirdFullPhysicalOrderedSymbol244
  simp only [hqp, hrp, hrq, hBA, hCA, hCB, hAq, hBp, hCp,
    thirdFullRadialDefectMultiplier244]
  ring

/-- The COMPLETE six-order H3 transport symbol cancels whenever the three
momenta have identical squared radius, even with non-planar polarization.
Pairwise shell equality alone is not enough; all three radii are matched. -/
theorem thirdFullPhysicalSix_equalRadius_cancellation244
    (p q r A B C : A3 → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (hA : thirdTriadAxisDot244 A p = 0)
    (hB : thirdTriadAxisDot244 B q = 0)
    (hC : thirdTriadAxisDot244 C r = 0)
    (hPQ : thirdTriadAxisDot244 p p = thirdTriadAxisDot244 q q)
    (hPR : thirdTriadAxisDot244 p p = thirdTriadAxisDot244 r r) :
    thirdFullPhysicalSixSymbol244 p q r A B C = 0 := by
  rw [thirdFullPhysicalSix_radialDefect_factorization244
    p q r A B C hMomentum hA hB hC]
  have hRP : thirdTriadAxisDot244 r r - thirdTriadAxisDot244 p p = 0 :=
    sub_eq_zero.mpr hPR.symm
  have hQP : thirdTriadAxisDot244 q q - thirdTriadAxisDot244 p p = 0 :=
    sub_eq_zero.mpr hPQ.symm
  have hRQ : thirdTriadAxisDot244 r r - thirdTriadAxisDot244 q q = 0 :=
    sub_eq_zero.mpr (hPR.symm.trans hPQ)
  rw [hRP, hQP, hRQ]
  ring

/-- The actual seven-derivative Hermitian reflection also vanishes on a
balanced-radius triad; no phase selection can restore that interaction. -/
theorem thirdFullHermitianOrbit_equalRadius_cancellation244
    (p q r A B C : A3 → ℝ) (z : ℂ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (hA : thirdTriadAxisDot244 A p = 0)
    (hB : thirdTriadAxisDot244 B q = 0)
    (hC : thirdTriadAxisDot244 C r = 0)
    (hPQ : thirdTriadAxisDot244 p p = thirdTriadAxisDot244 q q)
    (hPR : thirdTriadAxisDot244 p p = thirdTriadAxisDot244 r r) :
    thirdFullPhysicalHermitianOrbit244 p q r A B C z = 0 := by
  rw [thirdFullPhysicalHermitianOrbit_eq244,
    thirdFullPhysicalSix_equalRadius_cancellation244
      p q r A B C hMomentum hA hB hC hPQ hPR]
  ring

/-- Elementary three-defect estimate. This is deliberately linear in the
largest radial discrepancy, not a scalar Riccati or terminal-clock bound. -/
private theorem fullThird_threeDefect_abs_le
    (x y z a b c ρ : ℝ)
    (ha : |a| ≤ ρ) (hb : |b| ≤ ρ) (hc : |c| ≤ ρ) :
    |x * a + y * b + z * c| ≤
      ρ * (|x| + |y| + |z|) := by
  have h1 := abs_add_le (x * a) (y * b)
  have h2 := abs_add_le (x * a + y * b) (z * c)
  have hTri : |x * a + y * b + z * c| ≤
      |x * a| + |y * b| + |z * c| := by
    linarith only [h1, h2]
  have hxa := mul_le_mul_of_nonneg_left ha (abs_nonneg x)
  have hyb := mul_le_mul_of_nonneg_left hb (abs_nonneg y)
  have hzc := mul_le_mul_of_nonneg_left hc (abs_nonneg z)
  calc
    _ ≤ |x * a| + |y * b| + |z * c| := hTri
    _ = |x| * |a| + |y| * |b| + |z| * |c| := by
      simp only [abs_mul]
    _ ≤ |x| * ρ + |y| * ρ + |z| * ρ := by
      linarith only [hxa, hyb, hzc]
    _ = ρ * (|x| + |y| + |z|) := by ring

/-- The full signed six-order coefficient has an EXPLICIT near-equal-shell
smallness factor. The remaining prefactor is still a cubic derivative and
polarization polynomial; its integrability is a distinct physical task. -/
theorem thirdFullPhysicalSix_nearEqualRadius_bound244
    (p q r A B C : A3 → ℝ) (ρ : ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (hA : thirdTriadAxisDot244 A p = 0)
    (hB : thirdTriadAxisDot244 B q = 0)
    (hC : thirdTriadAxisDot244 C r = 0)
    (hRP : |thirdTriadAxisDot244 r r - thirdTriadAxisDot244 p p| ≤ ρ)
    (hQP : |thirdTriadAxisDot244 q q - thirdTriadAxisDot244 p p| ≤ ρ)
    (hRQ : |thirdTriadAxisDot244 r r - thirdTriadAxisDot244 q q| ≤ ρ) :
    |thirdFullPhysicalSixSymbol244 p q r A B C| ≤
      ρ * (
        |thirdTriadAxisDot244 A C * thirdTriadAxisDot244 B r *
          thirdFullRadialDefectMultiplier244
            (thirdTriadAxisDot244 p q)
            (thirdTriadAxisDot244 q r)
            (thirdTriadAxisDot244 p r)| +
        |thirdTriadAxisDot244 A B * thirdTriadAxisDot244 C q *
          thirdFullRadialDefectMultiplier244
            (thirdTriadAxisDot244 p r)
            (thirdTriadAxisDot244 q r)
            (thirdTriadAxisDot244 p q)| +
        |thirdTriadAxisDot244 B C * thirdTriadAxisDot244 A r *
          thirdFullRadialDefectMultiplier244
            (thirdTriadAxisDot244 p q)
            (thirdTriadAxisDot244 p r)
            (thirdTriadAxisDot244 q r)|) := by
  let X : ℝ :=
    thirdTriadAxisDot244 A C * thirdTriadAxisDot244 B r *
      thirdFullRadialDefectMultiplier244
        (thirdTriadAxisDot244 p q)
        (thirdTriadAxisDot244 q r)
        (thirdTriadAxisDot244 p r)
  let Y : ℝ :=
    thirdTriadAxisDot244 A B * thirdTriadAxisDot244 C q *
      thirdFullRadialDefectMultiplier244
        (thirdTriadAxisDot244 p r)
        (thirdTriadAxisDot244 q r)
        (thirdTriadAxisDot244 p q)
  let Z : ℝ :=
    thirdTriadAxisDot244 B C * thirdTriadAxisDot244 A r *
      thirdFullRadialDefectMultiplier244
        (thirdTriadAxisDot244 p q)
        (thirdTriadAxisDot244 p r)
        (thirdTriadAxisDot244 q r)
  have hFactor := thirdFullPhysicalSix_radialDefect_factorization244
    p q r A B C hMomentum hA hB hC
  have hReassoc : thirdFullPhysicalSixSymbol244 p q r A B C =
      X * (thirdTriadAxisDot244 r r - thirdTriadAxisDot244 p p) +
      Y * (thirdTriadAxisDot244 q q - thirdTriadAxisDot244 p p) +
      Z * (thirdTriadAxisDot244 r r - thirdTriadAxisDot244 q q) := by
    rw [hFactor]
    dsimp only [X, Y, Z]
    ring
  rw [hReassoc]
  simpa only [X, Y, Z] using
    (fullThird_threeDefect_abs_le X Y Z
      (thirdTriadAxisDot244 r r - thirdTriadAxisDot244 p p)
      (thirdTriadAxisDot244 q q - thirdTriadAxisDot244 p p)
      (thirdTriadAxisDot244 r r - thirdTriadAxisDot244 q q)
      ρ hRP hQP hRQ)

end
end PrimeTensor.FirstMonomialTriad

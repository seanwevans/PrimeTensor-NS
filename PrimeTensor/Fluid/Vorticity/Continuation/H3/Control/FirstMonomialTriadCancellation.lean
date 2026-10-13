import Mathlib

/-!
# Incompressible triad cancellation in the first interpolation monomial

For frequencies p + q + r = 0 and polarization q · b = 0, exchanging
the two j-component factors of the physical D³u · (D²u D²u) monomial
gives the coefficient identity

 (p·r) ((p·q)^2 (r·b) + (r·q)^2 (p·b))
   = (p·r) (p·b) (q·q) ((r·r) - (p·p)).

The common velocity-component contraction and Fourier derivative constants
are omitted from this scalar coefficient. This is finite-dimensional algebra,
not yet a Fourier integral representation of the project's physical pairing.
In particular, no terminal bound or sign of the aggregate is asserted.
-/

namespace PrimeTensor
namespace FirstMonomialTriad

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Bilinear frequency/polarization contraction. -/
def dot (p q : ι → ℝ) : ℝ := ∑ i, p i * q i

theorem dot_comm (p q : ι → ℝ) : dot p q = dot q p := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Momentum conservation contracts against any vector, without positivity. -/
theorem momentum_dot
    (p q r b : ι → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0) :
    dot p b + dot q b + dot r b = 0 := by
  calc
    dot p b + dot q b + dot r b =
        ∑ i, (p i + q i + r i) * b i := by
      simp only [dot, add_mul, Finset.sum_add_distrib]
    _ = 0 := by simp only [hMomentum, zero_mul, Finset.sum_const_zero]

/-- The unsymmetrized coefficient after contracting derivative indices. -/
def coefficient (p q r b : ι → ℝ) : ℝ :=
  dot p r * (dot p q) ^ 2 * dot r b

/-- Explicit derivative-index contraction, before any triangle inequality.
The common sum over the repeated velocity-component index is external. -/
def derivativeContraction (p q r b : ι → ℝ) : ℝ :=
  ∑ i, ∑ k, ∑ l, ∑ v,
    p i * p k * p l * q k * q l * r i * r v * b v

theorem derivativeContraction_eq_coefficient (p q r b : ι → ℝ) :
    derivativeContraction p q r b = coefficient p q r b := by
  calc
    derivativeContraction p q r b =
        ∑ i, ∑ k, ∑ l, ∑ v,
          (p i * r i) * ((p k * q k) * ((p l * q l) * (r v * b v))) := by
      unfold derivativeContraction
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = dot p r * (dot p q * (dot p q * dot r b)) := by
      simp only [dot, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = coefficient p q r b := by
      unfold coefficient
      ring

/-- Exchange the two factors carrying the same velocity component. -/
noncomputable def symmetrizedCoefficient (p q r b : ι → ℝ) : ℝ :=
  (coefficient p q r b + coefficient r q p b) / 2

/-- Incompressibility removes the common polarization contribution; momentum
then converts the difference of squared dot products to a shell difference. -/
theorem exchanged_coefficient
    (p q r b : ι → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (hDivergence : dot q b = 0) :
    coefficient p q r b + coefficient r q p b =
      dot p r * dot p b * dot q q * (dot r r - dot p p) := by
  have hPolarization : dot r b = -dot p b := by
    have h := momentum_dot p q r b hMomentum
    linarith
  have hSum : dot r q + dot p q = -dot q q := by
    have h := momentum_dot p q r q hMomentum
    linarith
  have hP := momentum_dot p q r p hMomentum
  have hR := momentum_dot p q r r hMomentum
  rw [dot_comm q p, dot_comm r p] at hP
  rw [dot_comm q r] at hR
  have hDifference : dot r q - dot p q = dot p p - dot r r := by
    linarith
  have hFactor :
      (dot p q) ^ 2 * dot r b + (dot r q) ^ 2 * dot p b =
        dot p b * dot q q * (dot r r - dot p p) := by
    rw [hPolarization]
    calc
      (dot p q) ^ 2 * (-dot p b) + (dot r q) ^ 2 * dot p b =
          (dot r q - dot p q) * (dot r q + dot p q) * dot p b := by ring
      _ = (dot p p - dot r r) * (-dot q q) * dot p b := by
        rw [hDifference, hSum]
      _ = dot p b * dot q q * (dot r r - dot p p) := by ring
  unfold coefficient
  rw [dot_comm r p]
  calc
    dot p r * (dot p q) ^ 2 * dot r b +
        dot p r * (dot r q) ^ 2 * dot p b =
        dot p r * ((dot p q) ^ 2 * dot r b + (dot r q) ^ 2 * dot p b) := by ring
    _ = dot p r * (dot p b * dot q q * (dot r r - dot p p)) := by
      rw [hFactor]
    _ = dot p r * dot p b * dot q q * (dot r r - dot p p) := by ring

theorem symmetrized_coefficient
    (p q r b : ι → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (hDivergence : dot q b = 0) :
    symmetrizedCoefficient p q r b =
      (dot p r * dot p b * dot q q * (dot r r - dot p p)) / 2 := by
  unfold symmetrizedCoefficient
  rw [exchanged_coefficient p q r b hMomentum hDivergence]

/-- Equal-length outer frequencies cancel, regardless of their angle. -/
theorem equal_shell_cancellation
    (p q r b : ι → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (hDivergence : dot q b = 0)
    (hShell : dot r r = dot p p) :
    symmetrizedCoefficient p q r b = 0 := by
  rw [symmetrized_coefficient p q r b hMomentum hDivergence, hShell]
  ring

/-- The exact defect retains both polarization alignment and shell separation.
Turning this identity into an integrable PDE estimate remains a separate task. -/
theorem abs_symmetrized_coefficient
    (p q r b : ι → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (hDivergence : dot q b = 0) :
    |symmetrizedCoefficient p q r b| =
      (|dot p r| * |dot p b| * |dot q q| * |dot r r - dot p p|) / 2 := by
  rw [symmetrized_coefficient p q r b hMomentum hDivergence]
  rw [abs_div]
  simp only [abs_mul]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]

end FirstMonomialTriad
end PrimeTensor

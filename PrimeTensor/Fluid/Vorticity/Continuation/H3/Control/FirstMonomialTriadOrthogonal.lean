import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPlaneGeometry

/-!
# Orthogonal covariance of the complex triad coefficient

Apply the same real Euclidean isometry to frequencies and separately to
the real and imaginary parts of polarizations. This preserves the real,
mixed, and complex bilinear contractions. Consequently the complete
six-order coefficient and the planar cancellation survive every orthogonal
coordinate change, including reflections.
-/

namespace PrimeTensor.FirstMonomialTriad

open scoped BigOperators

noncomputable section

section General

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Orthogonal action on a coordinate frequency. -/
def orthogonalFrequency (O : E ≃ₗᵢ[ℝ] E) (p : ι → ℝ) : ι → ℝ :=
  WithLp.ofLp (O (WithLp.toLp 2 p))

/-- Complexification of the same real orthogonal action. -/
def orthogonalPolarization (O : E ≃ₗᵢ[ℝ] E) (a : ι → ℂ) : ι → ℂ :=
  fun i => ⟨(O (WithLp.toLp 2 (fun j => (a j).re))) i,
    (O (WithLp.toLp 2 (fun j => (a j).im))) i⟩

private theorem dot_eq_euclidean_inner (p q : ι → ℝ) :
    dot p q = inner ℝ (WithLp.toLp 2 p : E) (WithLp.toLp 2 q : E) := by
  simp only [dot, PiLp.inner_apply, Real.inner_apply]

theorem dot_orthogonal (O : E ≃ₗᵢ[ℝ] E) (p q : ι → ℝ) :
    dot (orthogonalFrequency O p) (orthogonalFrequency O q) = dot p q := by
  rw [dot_eq_euclidean_inner, dot_eq_euclidean_inner]
  change inner ℝ (O (WithLp.toLp 2 p)) (O (WithLp.toLp 2 q)) =
    inner ℝ (WithLp.toLp 2 p : E) (WithLp.toLp 2 q : E)
  exact O.inner_map_map _ _

theorem mixedDot_orthogonal (O : E ≃ₗᵢ[ℝ] E) (p : ι → ℝ) (a : ι → ℂ) :
    mixedDot (orthogonalFrequency O p) (orthogonalPolarization O a) = mixedDot p a := by
  apply Complex.ext
  · simp only [mixedDot_re]
    change dot (orthogonalFrequency O p) (orthogonalFrequency O (fun i => (a i).re)) = _
    exact dot_orthogonal O p (fun i => (a i).re)
  · simp only [mixedDot_im]
    change dot (orthogonalFrequency O p) (orthogonalFrequency O (fun i => (a i).im)) = _
    exact dot_orthogonal O p (fun i => (a i).im)

theorem amplitudeDot_re (a c : ι → ℂ) :
    (amplitudeDot a c).re = dot (fun i => (a i).re) (fun i => (c i).re) -
      dot (fun i => (a i).im) (fun i => (c i).im) := by
  simp [amplitudeDot, dot, Complex.mul_re, Finset.sum_sub_distrib]

theorem amplitudeDot_im (a c : ι → ℂ) :
    (amplitudeDot a c).im = dot (fun i => (a i).re) (fun i => (c i).im) +
      dot (fun i => (a i).im) (fun i => (c i).re) := by
  simp [amplitudeDot, dot, Complex.mul_im, Finset.sum_add_distrib]

/-- Real orthogonal maps preserve the complex bilinear pairing as well as
the usual Hermitian pairing. The triad uses the former. -/
theorem amplitudeDot_orthogonal (O : E ≃ₗᵢ[ℝ] E) (a c : ι → ℂ) :
    amplitudeDot (orthogonalPolarization O a) (orthogonalPolarization O c) = amplitudeDot a c := by
  apply Complex.ext
  · simp only [amplitudeDot_re]
    change dot (orthogonalFrequency O (fun i => (a i).re))
        (orthogonalFrequency O (fun i => (c i).re)) -
      dot (orthogonalFrequency O (fun i => (a i).im))
        (orthogonalFrequency O (fun i => (c i).im)) = _
    rw [dot_orthogonal, dot_orthogonal]
  · simp only [amplitudeDot_im]
    change dot (orthogonalFrequency O (fun i => (a i).re))
        (orthogonalFrequency O (fun i => (c i).im)) +
      dot (orthogonalFrequency O (fun i => (a i).im))
        (orthogonalFrequency O (fun i => (c i).re)) = _
    rw [dot_orthogonal, dot_orthogonal]

/-- Momentum conservation is transported by linearity. -/
theorem momentum_orthogonal (O : E ≃ₗᵢ[ℝ] E) (p q r : ι → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0) :
    ∀ i, orthogonalFrequency O p i + orthogonalFrequency O q i +
      orthogonalFrequency O r i = 0 := by
  have hz : (WithLp.toLp 2 p : E) + WithLp.toLp 2 q + WithLp.toLp 2 r = 0 := by
    ext i
    exact hMomentum i
  have h := congrArg O hz
  rw [map_add, map_add, map_zero] at h
  intro i
  exact congrArg (fun v : E => v i) h

theorem incompressible_orthogonal (O : E ≃ₗᵢ[ℝ] E) (p : ι → ℝ) (a : ι → ℂ)
    (h : mixedDot p a = 0) :
    mixedDot (orthogonalFrequency O p) (orthogonalPolarization O a) = 0 := by
  rw [mixedDot_orthogonal, h]

theorem complexCoefficient_orthogonal (O : E ≃ₗᵢ[ℝ] E)
    (p q r : ι → ℝ) (b : ι → ℂ) :
    complexCoefficient (orthogonalFrequency O p) (orthogonalFrequency O q)
      (orthogonalFrequency O r) (orthogonalPolarization O b) = complexCoefficient p q r b := by
  simp only [complexCoefficient, dot_orthogonal, mixedDot_orthogonal]

/-- Orthogonal covariance requires no momentum or divergence hypotheses;
those hypotheses are preserved separately when needed. -/
theorem sixOrderTriadCoefficient_orthogonal (O : E ≃ₗᵢ[ℝ] E)
    (p q r : ι → ℝ) (a b c : ι → ℂ) :
    sixOrderTriadCoefficient (orthogonalFrequency O p) (orthogonalFrequency O q)
      (orthogonalFrequency O r) (orthogonalPolarization O a)
      (orthogonalPolarization O b) (orthogonalPolarization O c) =
      sixOrderTriadCoefficient p q r a b c := by
  simp only [sixOrderTriadCoefficient, orderedTriadCoefficient,
    complexCoefficient_orthogonal, amplitudeDot_orthogonal]

end General

/-- The planar cancellation holds after any real orthogonal change of the
three-dimensional frame. No orientation restriction is imposed. -/
theorem sixOrderTriadCoefficient_rotated_planar_zero
    (O : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (x y z w : ℝ) (α β γ : ℂ) :
    sixOrderTriadCoefficient
      (orthogonalFrequency O (planeFrequency x y))
      (orthogonalFrequency O (planeFrequency z w))
      (orthogonalFrequency O (planeFrequency (-x-z) (-y-w)))
      (orthogonalPolarization O (planePolarization x y α 0))
      (orthogonalPolarization O (planePolarization z w β 0))
      (orthogonalPolarization O (planePolarization (-x-z) (-y-w) γ 0)) = 0 := by
  rw [sixOrderTriadCoefficient_orthogonal]
  exact sixOrderTriadCoefficient_planar_zero x y z w α β γ

end
end PrimeTensor.FirstMonomialTriad

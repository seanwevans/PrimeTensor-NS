import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadFrame

/-!
# Intrinsic normal-amplitude remainder of the complete triad coefficient

The complete incompressible coefficient is a sum of three shell coefficients
weighted by pairs of normal amplitudes. The final identity has no inverse
frequencies and includes zero frequencies. A unit common normal exists for
every momentum triad; only pointwise existence is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

section General
variable {ι : Type*} [Fintype ι]

/-- Three shell channels with only the paired normal amplitudes retained. -/
def normalShellSum (p q r : ι → ℝ) (a b c : ι → ℂ) (A B C : ℂ) : ℂ :=
  complexShellCoefficient p q r b * (A * C) +
  complexShellCoefficient p r q c * (A * B) +
  complexShellCoefficient q p r a * (B * C)

theorem complexShellCoefficient_orthogonal
    (O : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (p q r : ι → ℝ) (b : ι → ℂ) :
    complexShellCoefficient (orthogonalFrequency O p) (orthogonalFrequency O q)
      (orthogonalFrequency O r) (orthogonalPolarization O b) =
      complexShellCoefficient p q r b := by
  simp only [complexShellCoefficient, dot_orthogonal, mixedDot_orthogonal]

theorem normalShellSum_orthogonal
    (O : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (p q r : ι → ℝ) (a b c : ι → ℂ) (A B C : ℂ) :
    normalShellSum (orthogonalFrequency O p) (orthogonalFrequency O q)
      (orthogonalFrequency O r) (orthogonalPolarization O a)
      (orthogonalPolarization O b) (orthogonalPolarization O c) A B C =
      normalShellSum p q r a b c A B C := by
  simp only [normalShellSum, complexShellCoefficient_orthogonal]

/-- At a zero frequency both sides vanish, without incompressibility. -/
theorem sixOrderTriadCoefficient_eq_normalShellSum_of_zero
    (p q r : ι → ℝ) (a b c : ι → ℂ) (A B C : ℂ)
    (hZero : p = 0 ∨ q = 0 ∨ r = 0) :
    sixOrderTriadCoefficient p q r a b c = normalShellSum p q r a b c A B C := by
  rcases hZero with rfl | rfl | rfl <;>
    simp [sixOrderTriadCoefficient, orderedTriadCoefficient, complexCoefficient,
      normalShellSum, complexShellCoefficient, dot, mixedDot]

end General

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000 in
/-- The plane geometry identity expressed using the original shell coefficients. -/
theorem sixOrderTriadCoefficient_plane_normal_shells
    (x y z w : ℝ) (α β γ A B C : ℂ) :
    sixOrderTriadCoefficient
      (planeFrequency x y) (planeFrequency z w) (planeFrequency (-x-z) (-y-w))
      (planePolarization x y α A) (planePolarization z w β B)
      (planePolarization (-x-z) (-y-w) γ C) =
    normalShellSum
      (planeFrequency x y) (planeFrequency z w) (planeFrequency (-x-z) (-y-w))
      (planePolarization x y α A) (planePolarization z w β B)
      (planePolarization (-x-z) (-y-w) γ C) A B C := by
  rw [sixOrderTriadCoefficient_plane_geometry]
  norm_num [normalShellSum, complexShellCoefficient, dot, mixedDot,
    planeFrequency, planePolarization, Fin.sum_univ_succ]
  push_cast
  ring

private theorem planeFrequency_zero_of_sq_zero (x y : ℝ) (h : x^2 + y^2 = 0) :
    planeFrequency x y = 0 := by
  have hx : x = 0 := by nlinarith [sq_nonneg y, sq_nonneg x]
  have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  subst x
  subst y
  funext i
  fin_cases i <;> simp [planeFrequency]

/-- Arbitrary planar incompressible amplitudes satisfy the normal-shell
identity. Zero frequencies are handled directly, before reconstruction. -/
theorem sixOrderTriadCoefficient_plane_normal_shells_of_incompressible
    (x y z w : ℝ) (a b c : Fin 3 → ℂ)
    (ha : mixedDot (planeFrequency x y) a = 0)
    (hb : mixedDot (planeFrequency z w) b = 0)
    (hc : mixedDot (planeFrequency (-x-z) (-y-w)) c = 0) :
    sixOrderTriadCoefficient (planeFrequency x y) (planeFrequency z w)
      (planeFrequency (-x-z) (-y-w)) a b c =
    normalShellSum (planeFrequency x y) (planeFrequency z w)
      (planeFrequency (-x-z) (-y-w)) a b c (a 2) (b 2) (c 2) := by
  by_cases hp : x^2 + y^2 = 0
  · exact sixOrderTriadCoefficient_eq_normalShellSum_of_zero _ _ _ _ _ _ _ _ _
      (Or.inl (planeFrequency_zero_of_sq_zero x y hp))
  by_cases hq : z^2 + w^2 = 0
  · exact sixOrderTriadCoefficient_eq_normalShellSum_of_zero _ _ _ _ _ _ _ _ _
      (Or.inr (Or.inl (planeFrequency_zero_of_sq_zero z w hq)))
  by_cases hr : (-x-z)^2 + (-y-w)^2 = 0
  · exact sixOrderTriadCoefficient_eq_normalShellSum_of_zero _ _ _ _ _ _ _ _ _
      (Or.inr (Or.inr (planeFrequency_zero_of_sq_zero (-x-z) (-y-w) hr)))
  have ea := planePolarization_reconstruct x y a hp ha
  have eb := planePolarization_reconstruct z w b hq hb
  have ec := planePolarization_reconstruct (-x-z) (-y-w) c hr hc
  have h := sixOrderTriadCoefficient_plane_normal_shells x y z w
    (planeTangentCoefficient x y a) (planeTangentCoefficient z w b)
    (planeTangentCoefficient (-x-z) (-y-w) c) (a 2) (b 2) (c 2)
  simp only [ea, eb, ec] at h
  exact h

/-- The normal coordinate of an amplitude pulled back to a frame is its
complex bilinear contraction with the frame's real unit normal. -/
theorem mixedDot_frame_normal (O : E3 ≃ₗᵢ[ℝ] E3) (a : Fin 3 → ℂ) :
    mixedDot (orthogonalFrequency O ![0, 0, 1]) a =
      orthogonalPolarization O.symm a 2 := by
  have h := mixedDot_orthogonal O (![0, 0, 1] : Fin 3 → ℝ)
    (orthogonalPolarization O.symm a)
  rw [orthogonalPolarization_apply_symm] at h
  calc
    mixedDot (orthogonalFrequency O ![0, 0, 1]) a =
        mixedDot ![0, 0, 1] (orthogonalPolarization O.symm a) := h
    _ = orthogonalPolarization O.symm a 2 := by
      norm_num [mixedDot, Fin.sum_univ_succ]

/-- The full incompressible coefficient has an intrinsic normal-shell
representation, with a real unit common normal. No nonzero-frequency
hypothesis or inverse-frequency factor occurs in this statement. -/
theorem exists_unit_normal_shell_decomposition
    (p q r : Fin 3 → ℝ) (a b c : Fin 3 → ℂ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (ha : mixedDot p a = 0) (hb : mixedDot q b = 0) (hc : mixedDot r c = 0) :
    ∃ n : Fin 3 → ℝ, dot n n = 1 ∧ dot n p = 0 ∧ dot n q = 0 ∧ dot n r = 0 ∧
      sixOrderTriadCoefficient p q r a b c =
        normalShellSum p q r a b c (mixedDot n a) (mixedDot n b) (mixedDot n c) := by
  obtain ⟨O, x, y, z, w, hp, hq, hr⟩ := exists_common_plane_frame p q r hMomentum
  let n : Fin 3 → ℝ := orthogonalFrequency O ![0, 0, 1]
  have ha' : mixedDot (planeFrequency x y) (orthogonalPolarization O.symm a) = 0 :=
    mixedDot_inverse_frame O _ a (by rw [hp]; exact ha)
  have hb' : mixedDot (planeFrequency z w) (orthogonalPolarization O.symm b) = 0 :=
    mixedDot_inverse_frame O _ b (by rw [hq]; exact hb)
  have hc' : mixedDot (planeFrequency (-x-z) (-y-w)) (orthogonalPolarization O.symm c) = 0 :=
    mixedDot_inverse_frame O _ c (by rw [hr]; exact hc)
  refine ⟨n, ?_, ?_, ?_, ?_, ?_⟩
  · change dot (orthogonalFrequency O ![0, 0, 1])
      (orthogonalFrequency O ![0, 0, 1]) = 1
    rw [dot_orthogonal]
    norm_num [dot, Fin.sum_univ_succ]
  · rw [← hp]
    change dot (orthogonalFrequency O ![0, 0, 1])
      (orthogonalFrequency O (planeFrequency x y)) = 0
    rw [dot_orthogonal]
    norm_num [dot, planeFrequency, Fin.sum_univ_succ]
  · rw [← hq]
    change dot (orthogonalFrequency O ![0, 0, 1])
      (orthogonalFrequency O (planeFrequency z w)) = 0
    rw [dot_orthogonal]
    norm_num [dot, planeFrequency, Fin.sum_univ_succ]
  · rw [← hr]
    change dot (orthogonalFrequency O ![0, 0, 1])
      (orthogonalFrequency O (planeFrequency (-x-z) (-y-w))) = 0
    rw [dot_orthogonal]
    norm_num [dot, planeFrequency, Fin.sum_univ_succ]
  · have hcoeff := sixOrderTriadCoefficient_orthogonal O
      (planeFrequency x y) (planeFrequency z w) (planeFrequency (-x-z) (-y-w))
      (orthogonalPolarization O.symm a) (orthogonalPolarization O.symm b)
      (orthogonalPolarization O.symm c)
    simp only [hp, hq, hr, orthogonalPolarization_apply_symm] at hcoeff
    have hshell := normalShellSum_orthogonal O
      (planeFrequency x y) (planeFrequency z w) (planeFrequency (-x-z) (-y-w))
      (orthogonalPolarization O.symm a) (orthogonalPolarization O.symm b)
      (orthogonalPolarization O.symm c)
      (orthogonalPolarization O.symm a 2) (orthogonalPolarization O.symm b 2)
      (orthogonalPolarization O.symm c 2)
    simp only [hp, hq, hr, orthogonalPolarization_apply_symm] at hshell
    change sixOrderTriadCoefficient p q r a b c =
      normalShellSum p q r a b c
        (mixedDot (orthogonalFrequency O ![0, 0, 1]) a)
        (mixedDot (orthogonalFrequency O ![0, 0, 1]) b)
        (mixedDot (orthogonalFrequency O ![0, 0, 1]) c)
    rw [mixedDot_frame_normal, mixedDot_frame_normal, mixedDot_frame_normal, hcoeff, hshell]
    exact sixOrderTriadCoefficient_plane_normal_shells_of_incompressible
      x y z w _ _ _ ha' hb' hc'

end
end PrimeTensor.FirstMonomialTriad

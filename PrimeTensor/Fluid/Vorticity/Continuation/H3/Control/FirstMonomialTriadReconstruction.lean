import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadOrthogonal

/-!
# Reconstruction of incompressible polarizations in a supplied frame

Every polarization perpendicular to a nonzero planar frequency has the
planar/normal form used by the six-order geometry identity. The same statement
holds in any supplied real orthogonal frame. Frame existence and estimates
uniform near zero frequency are separate questions.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- Coefficient of the unnormalized planar perpendicular direction. -/
def planeTangentCoefficient (x y : ℝ) (a : Fin 3 → ℂ) : ℂ :=
  ((x : ℂ) * a 1 - (y : ℂ) * a 0) / ((x : ℂ)^2 + (y : ℂ)^2)

/-- Incompressibility reconstructs the two planar coordinates; the normal
coordinate is free. The nonzero-frequency hypothesis is essential here. -/
theorem planePolarization_reconstruct (x y : ℝ) (a : Fin 3 → ℂ)
    (hNonzero : x^2 + y^2 ≠ 0)
    (hDiv : mixedDot (planeFrequency x y) a = 0) :
    planePolarization x y (planeTangentCoefficient x y a) (a 2) = a := by
  have hd : (x : ℂ)^2 + (y : ℂ)^2 ≠ 0 := by exact_mod_cast hNonzero
  have h : (x : ℂ) * a 0 + (y : ℂ) * a 1 = 0 := by
    simpa [mixedDot, planeFrequency, Fin.sum_univ_succ] using hDiv
  funext i
  fin_cases i
  · change -(y : ℂ) * (((x : ℂ) * a 1 - (y : ℂ) * a 0) /
        ((x : ℂ)^2 + (y : ℂ)^2)) = a 0
    field_simp [hd]
    linear_combination -(x : ℂ) * h
  · change (x : ℂ) * (((x : ℂ) * a 1 - (y : ℂ) * a 0) /
        ((x : ℂ)^2 + (y : ℂ)^2)) = a 1
    field_simp [hd]
    linear_combination -(y : ℂ) * h
  · rfl

/-- The complexified orthogonal action has the expected inverse. -/
theorem orthogonalPolarization_apply_symm {ι : Type*} [Fintype ι]
    (O : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (a : ι → ℂ) :
    orthogonalPolarization O (orthogonalPolarization O.symm a) = a := by
  funext i
  apply Complex.ext
  · change (O (O.symm (WithLp.toLp 2 (fun j => (a j).re)))) i = (a i).re
    simp
  · change (O (O.symm (WithLp.toLp 2 (fun j => (a j).im)))) i = (a i).im
    simp

/-- Pulling an incompressible polarization back to the frequency frame
preserves its divergence constraint. -/
theorem mixedDot_inverse_frame
    (O : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (hDiv : mixedDot (orthogonalFrequency O p) a = 0) :
    mixedDot p (orthogonalPolarization O.symm a) = 0 := by
  have h := mixedDot_orthogonal O p (orthogonalPolarization O.symm a)
  rw [orthogonalPolarization_apply_symm] at h
  exact h.symm.trans hDiv

/-- Reconstruction in a supplied orthogonal frame for arbitrary amplitudes. -/
theorem orthogonal_planePolarization_reconstruct
    (O : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (x y : ℝ) (a : Fin 3 → ℂ) (hNonzero : x^2 + y^2 ≠ 0)
    (hDiv : mixedDot (orthogonalFrequency O (planeFrequency x y)) a = 0) :
    orthogonalPolarization O
      (planePolarization x y
        (planeTangentCoefficient x y (orthogonalPolarization O.symm a))
        (orthogonalPolarization O.symm a 2)) = a := by
  rw [planePolarization_reconstruct x y _ hNonzero
    (mixedDot_inverse_frame O _ a hDiv), orthogonalPolarization_apply_symm]

/-- Planar cancellation for arbitrary divergence-free amplitudes with zero
normal coordinate, rather than amplitudes supplied in parameterized form. -/
theorem sixOrderTriadCoefficient_planar_zero_of_incompressible
    (x y z w : ℝ) (a b c : Fin 3 → ℂ)
    (hp : x^2 + y^2 ≠ 0) (hq : z^2 + w^2 ≠ 0)
    (hr : (-x-z)^2 + (-y-w)^2 ≠ 0)
    (ha : mixedDot (planeFrequency x y) a = 0)
    (hb : mixedDot (planeFrequency z w) b = 0)
    (hc : mixedDot (planeFrequency (-x-z) (-y-w)) c = 0)
    (hAn : a 2 = 0) (hBn : b 2 = 0) (hCn : c 2 = 0) :
    sixOrderTriadCoefficient (planeFrequency x y) (planeFrequency z w)
      (planeFrequency (-x-z) (-y-w)) a b c = 0 := by
  have ea := planePolarization_reconstruct x y a hp ha
  have eb := planePolarization_reconstruct z w b hq hb
  have ec := planePolarization_reconstruct (-x-z) (-y-w) c hr hc
  rw [hAn] at ea
  rw [hBn] at eb
  rw [hCn] at ec
  rw [← ea, ← eb, ← ec]
  exact sixOrderTriadCoefficient_planar_zero x y z w _ _ _

/-- Intrinsic amplitudes may be tested for planarity in any supplied frame. -/
theorem sixOrderTriadCoefficient_frame_planar_zero_of_incompressible
    (O : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (x y z w : ℝ) (a b c : Fin 3 → ℂ)
    (hp : x^2 + y^2 ≠ 0) (hq : z^2 + w^2 ≠ 0)
    (hr : (-x-z)^2 + (-y-w)^2 ≠ 0)
    (ha : mixedDot (orthogonalFrequency O (planeFrequency x y)) a = 0)
    (hb : mixedDot (orthogonalFrequency O (planeFrequency z w)) b = 0)
    (hc : mixedDot (orthogonalFrequency O (planeFrequency (-x-z) (-y-w))) c = 0)
    (hAn : orthogonalPolarization O.symm a 2 = 0)
    (hBn : orthogonalPolarization O.symm b 2 = 0)
    (hCn : orthogonalPolarization O.symm c 2 = 0) :
    sixOrderTriadCoefficient
      (orthogonalFrequency O (planeFrequency x y))
      (orthogonalFrequency O (planeFrequency z w))
      (orthogonalFrequency O (planeFrequency (-x-z) (-y-w))) a b c = 0 := by
  have h := sixOrderTriadCoefficient_orthogonal O
    (planeFrequency x y) (planeFrequency z w) (planeFrequency (-x-z) (-y-w))
    (orthogonalPolarization O.symm a) (orthogonalPolarization O.symm b)
    (orthogonalPolarization O.symm c)
  simp only [orthogonalPolarization_apply_symm] at h
  rw [h]
  exact sixOrderTriadCoefficient_planar_zero_of_incompressible x y z w _ _ _ hp hq hr
    (mixedDot_inverse_frame O _ a ha) (mixedDot_inverse_frame O _ b hb)
    (mixedDot_inverse_frame O _ c hc) hAn hBn hCn

end
end PrimeTensor.FirstMonomialTriad

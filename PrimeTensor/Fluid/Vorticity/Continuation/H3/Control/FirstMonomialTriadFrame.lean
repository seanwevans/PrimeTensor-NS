import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadCollinear
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# A common orthogonal plane frame for every momentum triad

The span of two vectors in three dimensions has a nonzero orthogonal
complement. Normalize a vector in that complement and use a reflection
sending the third coordinate axis to it. This proves pointwise existence
of a common frame, including degenerate triads. No measurable choice of
frames as a function of the frequencies is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Any two real three-dimensional vectors have a common unit normal. -/
theorem exists_unit_common_normal (p q : E3) :
    ∃ n : E3, ‖n‖ = 1 ∧ inner ℝ n p = 0 ∧ inner ℝ n q = 0 := by
  classical
  let K : Submodule ℝ E3 := Submodule.span ℝ {p, q}
  have hdim : Module.finrank ℝ K ≤ 2 := by
    calc
      Module.finrank ℝ K ≤ ({p, q} : Set E3).toFinset.card :=
        finrank_span_le_card ({p, q} : Set E3)
      _ ≤ 2 := by
        by_cases h : p = q <;> simp [h]
  have htotal := K.finrank_add_finrank_orthogonal
  have hthree : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  haveI : Nontrivial Kᗮ := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨w, hw⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0
  have hwE : (w : E3) ≠ 0 := fun h => hw (Subtype.ext h)
  have hpK : p ∈ K := Submodule.subset_span (by simp)
  have hqK : q ∈ K := Submodule.subset_span (by simp)
  have hwp : inner ℝ (w : E3) p = 0 := by
    rw [real_inner_comm]
    exact w.property p hpK
  have hwq : inner ℝ (w : E3) q = 0 := by
    rw [real_inner_comm]
    exact w.property q hqK
  refine ⟨‖(w : E3)‖⁻¹ • (w : E3), ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwE)]
  · simp [inner_smul_left, hwp]
  · simp [inner_smul_left, hwq]

/-- A reflection gives a common frame whose inverse sends both vectors to
zero third coordinate. No linear-independence hypothesis is needed. -/
theorem exists_orthogonal_flatten_pair (p q : E3) :
    ∃ O : E3 ≃ₗᵢ[ℝ] E3, (O.symm p) 2 = 0 ∧ (O.symm q) 2 = 0 := by
  obtain ⟨n, hn, hnp, hnq⟩ := exists_unit_common_normal p q
  let e : E3 := EuclideanSpace.single 2 1
  let O : E3 ≃ₗᵢ[ℝ] E3 := ((ℝ ∙ (e - n))ᗮ).reflection
  have hO : O e = n := Submodule.reflection_sub (by simp [e, hn])
  have hcoord (v : E3) (hv : inner ℝ n v = 0) : (O.symm v) 2 = 0 := by
    calc
      (O.symm v) 2 = inner ℝ e (O.symm v) := by
        simp [e, EuclideanSpace.inner_single_left]
      _ = inner ℝ (O e) v := by
        simpa using (O.inner_map_map e (O.symm v)).symm
      _ = 0 := by rw [hO]; exact hv
  exact ⟨O, hcoord p hnp, hcoord q hnq⟩

/-- Every momentum-conserving triad is the orthogonal image of one common
coordinate-plane triad. This includes collinear and zero frequencies. -/
theorem exists_common_plane_frame (p q r : Fin 3 → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0) :
    ∃ (O : E3 ≃ₗᵢ[ℝ] E3) (x y z w : ℝ),
      orthogonalFrequency O (planeFrequency x y) = p ∧
      orthogonalFrequency O (planeFrequency z w) = q ∧
      orthogonalFrequency O (planeFrequency (-x-z) (-y-w)) = r := by
  obtain ⟨O, hp2, hq2⟩ := exists_orthogonal_flatten_pair
    (WithLp.toLp 2 p) (WithLp.toLp 2 q)
  let x := (O.symm (WithLp.toLp 2 p)) 0
  let y := (O.symm (WithLp.toLp 2 p)) 1
  let z := (O.symm (WithLp.toLp 2 q)) 0
  let w := (O.symm (WithLp.toLp 2 q)) 1
  have hpE : (WithLp.toLp 2 (planeFrequency x y) : E3) =
      O.symm (WithLp.toLp 2 p) := by
    ext i
    fin_cases i <;> simp [planeFrequency, x, y, hp2]
  have hqE : (WithLp.toLp 2 (planeFrequency z w) : E3) =
      O.symm (WithLp.toLp 2 q) := by
    ext i
    fin_cases i <;> simp [planeFrequency, z, w, hq2]
  have hP : O (WithLp.toLp 2 (planeFrequency x y)) = WithLp.toLp 2 p := by
    rw [hpE, O.apply_symm_apply]
  have hQ : O (WithLp.toLp 2 (planeFrequency z w)) = WithLp.toLp 2 q := by
    rw [hqE, O.apply_symm_apply]
  have hrE : (WithLp.toLp 2 r : E3) = -WithLp.toLp 2 p - WithLp.toLp 2 q := by
    ext i
    change r i = -p i - q i
    have h := hMomentum i
    linarith
  have hplane : (WithLp.toLp 2 (planeFrequency (-x-z) (-y-w)) : E3) =
      -WithLp.toLp 2 (planeFrequency x y) - WithLp.toLp 2 (planeFrequency z w) := by
    ext i
    fin_cases i <;> simp [planeFrequency]
  have hR : O (WithLp.toLp 2 (planeFrequency (-x-z) (-y-w))) = WithLp.toLp 2 r := by
    rw [hplane, map_sub, map_neg, hP, hQ, hrE]
  refine ⟨O, x, y, z, w, ?_, ?_, ?_⟩
  · exact congrArg WithLp.ofLp hP
  · exact congrArg WithLp.ofLp hQ
  · exact congrArg WithLp.ofLp hR

/-- The complete coefficient of any momentum triad can be evaluated in a
common plane frame, with its actual amplitudes pulled back by that frame. -/
theorem exists_plane_frame_coefficient (p q r : Fin 3 → ℝ) (a b c : Fin 3 → ℂ)
    (hMomentum : ∀ i, p i + q i + r i = 0) :
    ∃ (O : E3 ≃ₗᵢ[ℝ] E3) (x y z w : ℝ),
      orthogonalFrequency O (planeFrequency x y) = p ∧
      orthogonalFrequency O (planeFrequency z w) = q ∧
      orthogonalFrequency O (planeFrequency (-x-z) (-y-w)) = r ∧
      sixOrderTriadCoefficient p q r a b c =
        sixOrderTriadCoefficient (planeFrequency x y) (planeFrequency z w)
          (planeFrequency (-x-z) (-y-w)) (orthogonalPolarization O.symm a)
          (orthogonalPolarization O.symm b) (orthogonalPolarization O.symm c) := by
  obtain ⟨O, x, y, z, w, hp, hq, hr⟩ := exists_common_plane_frame p q r hMomentum
  refine ⟨O, x, y, z, w, hp, hq, hr, ?_⟩
  have h := sixOrderTriadCoefficient_orthogonal O
    (planeFrequency x y) (planeFrequency z w) (planeFrequency (-x-z) (-y-w))
    (orthogonalPolarization O.symm a) (orthogonalPolarization O.symm b)
    (orthogonalPolarization O.symm c)
  simpa only [hp, hq, hr, orthogonalPolarization_apply_symm] using h

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadSignAudit

/-!
# Plane geometry of the complete first-monomial triad coefficient

For frequencies in the xy plane, write each incompressible polarization
as a planar perpendicular component plus a normal component. The fully
planar cubic term cancels across the six orderings. The remainder contains
exactly two normal components and the oriented area of the frequency pair.
This is a coordinate-plane symbol identity, not yet a field integral theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- A frequency in the chosen plane. -/
def planeFrequency (x y : ℝ) : Fin 3 → ℝ := ![x, y, 0]

/-- alpha times the planar perpendicular direction, plus a normal component.
The planar basis is not normalized; no division by frequency is used. -/
def planePolarization (x y : ℝ) (α A : ℂ) : Fin 3 → ℂ :=
  ![-(y : ℂ) * α, (x : ℂ) * α, A]

theorem planePolarization_incompressible (x y : ℝ) (α A : ℂ) :
    mixedDot (planeFrequency x y) (planePolarization x y α A) = 0 := by
  norm_num [mixedDot, planeFrequency, planePolarization, Fin.sum_univ_succ] <;> ring

theorem planeFrequency_momentum (x y z w : ℝ) :
    ∀ i, planeFrequency x y i + planeFrequency z w i +
      planeFrequency (-x-z) (-y-w) i = 0 := by
  intro i
  fin_cases i <;> simp [planeFrequency] <;> ring

set_option maxHeartbeats 800000 in
/-- Explicit geometry of the six-order symbol. alpha,beta,gamma multiply
planar perpendicular directions; A,B,C are the normal amplitudes. -/
theorem sixOrderTriadCoefficient_plane_geometry
    (x y z w : ℝ) (α β γ A B C : ℂ) :
    sixOrderTriadCoefficient
      (planeFrequency x y) (planeFrequency z w) (planeFrequency (-x-z) (-y-w))
      (planePolarization x y α A) (planePolarization z w β B)
      (planePolarization (-x-z) (-y-w) γ C) =
    ((x*w-y*z : ℝ) : ℂ) *
      (α * B * C *
        ((dot (planeFrequency z w) (planeFrequency (-x-z) (-y-w)) *
          dot (planeFrequency x y) (planeFrequency x y) *
          (dot (planeFrequency (-x-z) (-y-w)) (planeFrequency (-x-z) (-y-w)) -
            dot (planeFrequency z w) (planeFrequency z w)) : ℝ) : ℂ) -
       β * A * C *
        ((dot (planeFrequency x y) (planeFrequency (-x-z) (-y-w)) *
          dot (planeFrequency z w) (planeFrequency z w) *
          (dot (planeFrequency (-x-z) (-y-w)) (planeFrequency (-x-z) (-y-w)) -
            dot (planeFrequency x y) (planeFrequency x y)) : ℝ) : ℂ) +
       γ * A * B *
        ((dot (planeFrequency x y) (planeFrequency z w) *
          dot (planeFrequency (-x-z) (-y-w)) (planeFrequency (-x-z) (-y-w)) *
          (dot (planeFrequency z w) (planeFrequency z w) -
            dot (planeFrequency x y) (planeFrequency x y)) : ℝ) : ℂ)) := by
  norm_num [sixOrderTriadCoefficient, orderedTriadCoefficient, complexCoefficient,
    dot, mixedDot, amplitudeDot, planeFrequency, planePolarization, Fin.sum_univ_succ]
  push_cast
  ring

/-- Fully planar incompressible polarizations cancel after all six orderings. -/
theorem sixOrderTriadCoefficient_planar_zero
    (x y z w : ℝ) (α β γ : ℂ) :
    sixOrderTriadCoefficient
      (planeFrequency x y) (planeFrequency z w) (planeFrequency (-x-z) (-y-w))
      (planePolarization x y α 0) (planePolarization z w β 0)
      (planePolarization (-x-z) (-y-w) γ 0) = 0 := by
  rw [sixOrderTriadCoefficient_plane_geometry]
  ring

/-- Purely normal polarizations also give zero. -/
theorem sixOrderTriadCoefficient_normal_zero
    (x y z w : ℝ) (A B C : ℂ) :
    sixOrderTriadCoefficient
      (planeFrequency x y) (planeFrequency z w) (planeFrequency (-x-z) (-y-w))
      (planePolarization x y 0 A) (planePolarization z w 0 B)
      (planePolarization (-x-z) (-y-w) 0 C) = 0 := by
  rw [sixOrderTriadCoefficient_plane_geometry]
  ring

/-- At least two nonzero normal amplitudes are required for a surviving term. -/
theorem sixOrderTriadCoefficient_zero_of_normal_products_zero
    (x y z w : ℝ) (α β γ A B C : ℂ)
    (hAB : A * B = 0) (hAC : A * C = 0) (hBC : B * C = 0) :
    sixOrderTriadCoefficient
      (planeFrequency x y) (planeFrequency z w) (planeFrequency (-x-z) (-y-w))
      (planePolarization x y α A) (planePolarization z w β B)
      (planePolarization (-x-z) (-y-w) γ C) = 0 := by
  have ha : α * B * C = 0 := by rw [mul_assoc, hBC, mul_zero]
  have hb : β * A * C = 0 := by rw [mul_assoc, hAC, mul_zero]
  have hc : γ * A * B = 0 := by rw [mul_assoc, hAB, mul_zero]
  rw [sixOrderTriadCoefficient_plane_geometry, ha, hb, hc]
  ring

/-- Collinear frequencies cancel in this parameterization, even with mixed
planar and normal polarizations. -/
theorem sixOrderTriadCoefficient_zero_of_plane_area_zero
    (x y z w : ℝ) (α β γ A B C : ℂ) (hArea : x*w-y*z = 0) :
    sixOrderTriadCoefficient
      (planeFrequency x y) (planeFrequency z w) (planeFrequency (-x-z) (-y-w))
      (planePolarization x y α A) (planePolarization z w β B)
      (planePolarization (-x-z) (-y-w) γ C) = 0 := by
  rw [sixOrderTriadCoefficient_plane_geometry, hArea]
  simp

end
end PrimeTensor.FirstMonomialTriad

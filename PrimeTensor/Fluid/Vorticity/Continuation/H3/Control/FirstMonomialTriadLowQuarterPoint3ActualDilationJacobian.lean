import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3ActualDilationDerivative
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Positive isotropic dilation: actual three-dimensional Schwartz integral scaling

This module crosses the volume-Jacobian bridge from the previously proved
real Schwartz differentiation laws to integrals on the actual three-dimensional
Euclidean H3 Fourier carrier.

For every positive scale, the integral of a measurable real-valued function
composed with `x ↦ scale • x` is multiplied by `(scale^3)⁻¹`. Mathlib's
additive Haar change-of-variables theorem supplies the underlying identity;
we identify the concrete EuclideanSpace dimension using PrimeTensor's three
positive axes. No informal substitution or extra measure normalization is used.

This gives exact integral scaling for squares of Schwartz derivatives of
orders zero through four. In particular the normalized factors are
`scale^(2*k) * (scale^3)⁻¹`. The finite H3 sums, spatial Point3 monomial
integral and divergence under physical dilation remain separate obligations.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeQuarterJacobian (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Identify the actual H3 Fourier carrier's real dimension, without replacing
`PrimeTensor.Axis` by a zero-based proxy. -/
theorem lowNormalH3Fourier_finrank_three : Module.finrank ℝ V3 = 3 := by
  classical
  change Module.finrank ℝ (EuclideanSpace ℝ A3) = 3
  rw [finrank_euclideanSpace]
  rw [← Finset.card_univ]
  rw [PrimeTensor.Bridge.Euclidean.axis_univ_three]
  change ({xAxis, yAxis, zAxis} : Finset A3).card = 3
  -- The project axes are positive-depth constructors, not `Fin 3` indices.
  have hxy : xAxis ≠ yAxis := by
    intro h
    change (PrimeTensor.Axis.first : PrimeTensor.Axis Depth.three) =
      PrimeTensor.Axis.next
        (PrimeTensor.Axis.first : PrimeTensor.Axis Depth.two) at h
    cases h
  have hxz : xAxis ≠ zAxis := by
    intro h
    change (PrimeTensor.Axis.first : PrimeTensor.Axis Depth.three) =
      PrimeTensor.Axis.next
        (PrimeTensor.Axis.next
          (PrimeTensor.Axis.first : PrimeTensor.Axis Depth.one)) at h
    cases h
  have hyz : yAxis ≠ zAxis := by
    intro h
    have hRank := congrArg
      (fun i : A3 => PrimeTensor.Bridge.Euclidean.axisRank i) h
    norm_num [PrimeTensor.Bridge.Euclidean.axisRank,
      PrimeTensor.Bridge.Euclidean.yAxis,
      PrimeTensor.Bridge.Euclidean.zAxis] at hRank
  have hxNotMem : xAxis ∉ ({yAxis, zAxis} : Finset A3) := by
    intro h
    rcases Finset.mem_insert.mp h with hxy' | hxz'
    · exact hxy hxy'
    · exact hxz (Finset.mem_singleton.mp hxz')
  have hyNotMem : yAxis ∉ ({zAxis} : Finset A3) := by
    intro h
    exact hyz (Finset.mem_singleton.mp h)
  rw [Finset.card_insert_of_notMem hxNotMem,
    Finset.card_insert_of_notMem hyNotMem,
    Finset.card_singleton]

/-- The exact Jacobian factor for a positive scalar dilation on the *actual*
three-dimensional Fourier carrier. No Schwartz or integrability restriction
is necessary for this Bochner-integral identity. -/
theorem lowNormalH3Fourier_integral_comp_positive_smul
    (scale : ℝ) (hscale : 0 < scale) (g : V3 → ℝ) :
    (∫ x : V3, g (scale • x)) =
      (scale ^ 3)⁻¹ * ∫ x : V3, g x := by
  have h := Measure.integral_comp_smul_of_nonneg
    (μ := (volume : Measure V3)) g scale (hR := hscale.le)
  simpa only [lowNormalH3Fourier_finrank_three, smul_eq_mul] using h

/-- The square of an actual real Schwartz component picks up the inverse
three-dimensional Jacobian, exactly. -/
theorem lowNormalSchwartzDilation_integral_sq
    (scale : ℝ) (hscale : 0 < scale) (f : SchwartzMap V3 ℝ) :
    (∫ x : V3, (lowNormalSchwartzDilation scale hscale f x) ^ 2) =
      (scale ^ 3)⁻¹ * ∫ x : V3, (f x) ^ 2 := by
  simpa only [lowNormalSchwartzDilation_apply] using
    (lowNormalH3Fourier_integral_comp_positive_smul scale hscale
      (fun x : V3 => (f x) ^ 2))

/-- A reusable integral lemma for an exact `k`th-order Schwartz dilation
identity. The coefficient is intentionally left as `(scale^k)^2` so that no
real-power manipulation is hidden in a dependent derivative induction. -/
private theorem lowNormalSchwartzDilation_integral_sq_of_eq
    (scale : ℝ) (hscale : 0 < scale) (k : ℕ)
    (f g : SchwartzMap V3 ℝ)
    (hg : g = scale ^ k • lowNormalSchwartzDilation scale hscale f) :
    (∫ x : V3, (g x) ^ 2) =
      (scale ^ k) ^ 2 * (scale ^ 3)⁻¹ * ∫ x : V3, (f x) ^ 2 := by
  rw [hg]
  simp only [smul_apply, smul_eq_mul, mul_pow, integral_const_mul]
  rw [lowNormalSchwartzDilation_integral_sq]
  ring

/-- Squared first directional derivatives scale by `scale² / scale³`. -/
theorem lowNormalSchwartzDilation_integral_sq_lineDeriv
    (scale : ℝ) (hscale : 0 < scale)
    (m : V3) (f : SchwartzMap V3 ℝ) :
    (∫ x : V3, ((∂_{m} (lowNormalSchwartzDilation scale hscale f)) x) ^ 2) =
      (scale ^ 2 * (scale ^ 3)⁻¹) *
        ∫ x : V3, ((∂_{m} f) x) ^ 2 := by
  have h := lowNormalSchwartzDilation_integral_sq_of_eq
    scale hscale 1 (∂_{m} f)
    (∂_{m} (lowNormalSchwartzDilation scale hscale f))
    (by simpa only [pow_one] using
      lowNormalSchwartzDilation_lineDeriv scale hscale m f)
  simpa only [pow_one, pow_two, mul_assoc] using h

/-- Squared second directional derivatives scale by `scale⁴ / scale³`. -/
theorem lowNormalSchwartzDilation_integral_sq_twoLineDerivs
    (scale : ℝ) (hscale : 0 < scale)
    (m n : V3) (f : SchwartzMap V3 ℝ) :
    (∫ x : V3, ((∂_{m} (∂_{n}
      (lowNormalSchwartzDilation scale hscale f))) x) ^ 2) =
      (scale ^ 4 * (scale ^ 3)⁻¹) *
        ∫ x : V3, ((∂_{m} (∂_{n} f)) x) ^ 2 := by
  calc
    _ = (scale ^ 2) ^ 2 * (scale ^ 3)⁻¹ *
        ∫ x : V3, ((∂_{m} (∂_{n} f)) x) ^ 2 :=
      lowNormalSchwartzDilation_integral_sq_of_eq
        scale hscale 2 (∂_{m} (∂_{n} f))
          (∂_{m} (∂_{n} (lowNormalSchwartzDilation scale hscale f)))
        (lowNormalSchwartzDilation_twoLineDerivs scale hscale m n f)
    _ = (scale ^ 4 * (scale ^ 3)⁻¹) *
        ∫ x : V3, ((∂_{m} (∂_{n} f)) x) ^ 2 := by
      simp only [← pow_mul, Nat.reduceMul]
  all_goals rfl

/-- Squared third directional derivatives scale by `scale⁶ / scale³`. -/
theorem lowNormalSchwartzDilation_integral_sq_threeLineDerivs
    (scale : ℝ) (hscale : 0 < scale)
    (m n p : V3) (f : SchwartzMap V3 ℝ) :
    (∫ x : V3, ((∂_{m} (∂_{n} (∂_{p}
      (lowNormalSchwartzDilation scale hscale f)))) x) ^ 2) =
      (scale ^ 6 * (scale ^ 3)⁻¹) *
        ∫ x : V3, ((∂_{m} (∂_{n} (∂_{p} f))) x) ^ 2 := by
  calc
    _ = (scale ^ 3) ^ 2 * (scale ^ 3)⁻¹ *
        ∫ x : V3, ((∂_{m} (∂_{n} (∂_{p} f))) x) ^ 2 :=
      lowNormalSchwartzDilation_integral_sq_of_eq
        scale hscale 3 (∂_{m} (∂_{n} (∂_{p} f)))
          (∂_{m} (∂_{n} (∂_{p} (lowNormalSchwartzDilation scale hscale f))))
        (lowNormalSchwartzDilation_threeLineDerivs scale hscale m n p f)
    _ = (scale ^ 6 * (scale ^ 3)⁻¹) *
        ∫ x : V3, ((∂_{m} (∂_{n} (∂_{p} f))) x) ^ 2 := by
      simp only [← pow_mul, Nat.reduceMul]
  all_goals rfl

/-- Squared fourth directional derivatives scale by `scale⁸ / scale³`. -/
theorem lowNormalSchwartzDilation_integral_sq_fourLineDerivs
    (scale : ℝ) (hscale : 0 < scale)
    (m n p q : V3) (f : SchwartzMap V3 ℝ) :
    (∫ x : V3, ((∂_{m} (∂_{n} (∂_{p} (∂_{q}
      (lowNormalSchwartzDilation scale hscale f))))) x) ^ 2) =
      (scale ^ 8 * (scale ^ 3)⁻¹) *
        ∫ x : V3, ((∂_{m} (∂_{n} (∂_{p} (∂_{q} f)))) x) ^ 2 := by
  calc
    _ = (scale ^ 4) ^ 2 * (scale ^ 3)⁻¹ *
        ∫ x : V3, ((∂_{m} (∂_{n} (∂_{p} (∂_{q} f)))) x) ^ 2 :=
      lowNormalSchwartzDilation_integral_sq_of_eq
        scale hscale 4 (∂_{m} (∂_{n} (∂_{p} (∂_{q} f))))
          (∂_{m} (∂_{n} (∂_{p} (∂_{q}
            (lowNormalSchwartzDilation scale hscale f)))))
        (lowNormalSchwartzDilation_fourLineDerivs scale hscale m n p q f)
    _ = (scale ^ 8 * (scale ^ 3)⁻¹) *
        ∫ x : V3, ((∂_{m} (∂_{n} (∂_{p} (∂_{q} f)))) x) ^ 2 := by
      simp only [← pow_mul, Nat.reduceMul]
  all_goals rfl

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SignReversal

/-!
# Cubic first-monomial scaling against quadratic top H3 dissipation

The actual 243-slot physical first-monomial is cubic in velocity amplitude,
whereas the four-spatial-derivative L2 quadratic form is homogeneous of
degree two. This module proves both exact identities for arbitrary real
Schwartz fields, then uses the already constructed strictly positive
solenoidal quarter packet to show that no velocity-independent constant
can dominate this signed monomial by that quadratic form for ALL amplitudes.

This is a sharp obstruction to a bare linear dissipation absorption
inequality. It is NOT a Navier--Stokes blowup or nonextension theorem, and
does not rule out bounds involving lower-order energies or other terms.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap FourierTransform LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeQuarterAmplitude (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Real scaling commutes with the existing Schwartz complexification. -/
theorem lowNormalSchwartzComplexify_real_smul
    (a : ℝ) (g : SchwartzMap V3 ℝ) :
    h3SchwartzComplexify (a • g) = a • h3SchwartzComplexify g := by
  change (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM) (a • g) =
    a • (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM) g
  exact map_smul _ a g

/-- Each of the three factors in a first-monomial slot contributes one
copy of the velocity-amplitude multiplier. -/
theorem lowNormalSchwartzFirstMonomialSlot_real_smul
    (a : ℝ) (F : A3 → SchwartzMap V3 ℂ) (i k l r j : A3) :
    h3SchwartzFirstMonomialSlot (fun b => a • F b) i k l r j =
      (a : ℂ) ^ 3 * h3SchwartzFirstMonomialSlot F i k l r j := by
  unfold h3SchwartzFirstMonomialSlot
  simp only [LineDeriv.lineDerivOp_smul, smul_apply,
    RCLike.real_smul_eq_coe_mul]
  -- Avoid elaborating a giant syntactic `calc` equality at this point.
  -- First pull the constant inside the right-hand integral, then use
  -- an almost-everywhere pointwise ring identity.
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  -- Normalize the scalar cube without expanding the Schwartz derivatives.
  have hCube : (a : ℂ) ^ 3 =
      (a : ℂ) * (a : ℂ) * (a : ℂ) := by
    ring
  rw [hCube]
  ac_rfl

/-- The full complex five-index aggregate is exactly cubic in a real
amplitude; summing the 243 slots introduces no extra factor. -/
theorem lowNormalSchwartzFirstMonomialAggregate_real_smul
    (a : ℝ) (F : A3 → SchwartzMap V3 ℂ) :
    h3SchwartzFirstMonomialAggregate (fun j => a • F j) =
      (a : ℂ) ^ 3 * h3SchwartzFirstMonomialAggregate F := by
  unfold h3SchwartzFirstMonomialAggregate
  simp_rw [lowNormalSchwartzFirstMonomialSlot_real_smul a F]
  simp only [← Finset.mul_sum]

/-- The actual physical 243-slot first-monomial is cubic in amplitude,
for every real Schwartz field (without any divergence hypothesis). -/
theorem lowNormalRealSchwartzPoint3Monomial_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzPoint3Monomial (fun j => a • f j) =
      a ^ 3 * lowNormalRealSchwartzPoint3Monomial f := by
  simp only [lowNormalRealSchwartzPoint3Monomial_eq_complex]
  simp_rw [lowNormalSchwartzComplexify_real_smul]
  rw [lowNormalSchwartzFirstMonomialAggregate_real_smul]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The full FOUR-derivative L2 square corresponding to top H3
viscous dissipation. No terms are selected or dropped. -/
noncomputable def lowNormalRealSchwartzH3TopDissipation
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ m : A3,
    ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k}
          (∂_{h3FourierAxisDirection l}
            (∂_{h3FourierAxisDirection m} (f j))))) x) ^ 2

/-- Unlike the cubic signed monomial, this genuine quadratic differential
form scales with the SQUARE of velocity amplitude. -/
theorem lowNormalRealSchwartzH3TopDissipation_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3TopDissipation (fun j => a • f j) =
      a ^ 2 * lowNormalRealSchwartzH3TopDissipation f := by
  unfold lowNormalRealSchwartzH3TopDissipation
  simp only [LineDeriv.lineDerivOp_smul, smul_apply, smul_eq_mul,
    mul_pow, integral_const_mul]
  simp only [← Finset.mul_sum]

/-- For an explicit strictly positive monomial witness, arbitrary
amplitude magnification defeats EVERY fixed linear coefficient in front
of the fourth-derivative quadratic form. -/
theorem lowNormalQuarter_exists_amplitude_exceeding_quadratic
    (C : ℝ) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ a : ℝ, 0 < a ∧
      C * lowNormalRealSchwartzH3TopDissipation
        (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j) <
      lowNormalRealSchwartzPoint3Monomial
        (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j) := by
  obtain ⟨ρ, hρ, _, hPos⟩ := lowNormalQuarterPoint3_exists_both_firstMonomial_signs
  let f : A3 → SchwartzMap V3 ℝ := lowNormalQuarterOppositeSchwartzVelocity ρ hρ
  let M : ℝ := lowNormalRealSchwartzPoint3Monomial f
  let Q : ℝ := lowNormalRealSchwartzH3TopDissipation f
  have hM : 0 < M := hPos
  let a : ℝ := (|C * Q| + 1) / M + 1
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hFormula : a * M = |C * Q| + 1 + M := by
    change ((|C * Q| + 1) / M + 1) * M = _
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hM), one_mul]
  have hStrict : C * Q < a * M := by
    rw [hFormula]
    have habs := le_abs_self (C * Q)
    linarith
  refine ⟨ρ, hρ, a, ha, ?_⟩
  change C * lowNormalRealSchwartzH3TopDissipation (fun j => a • f j) <
    lowNormalRealSchwartzPoint3Monomial (fun j => a • f j)
  rw [lowNormalRealSchwartzH3TopDissipation_real_smul,
    lowNormalRealSchwartzPoint3Monomial_real_smul]
  have hAmplified := mul_lt_mul_of_pos_left hStrict (pow_pos ha 2)
  calc
    C * (a ^ 2 * Q) = a ^ 2 * (C * Q) := by ring
    _ < a ^ 2 * (a * M) := hAmplified
    _ = a ^ 3 * M := by ring

end
end PrimeTensor.FirstMonomialTriad

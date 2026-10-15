import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3CriticalHalfThreshold

/-!
# Critical-half uniformity under a single isotropic spatial dilation

The previous module characterizes the sharp coefficient on one amplitude ray.
An independent question is whether varying the spatial *length scale* of one
fixed profile can by itself force the critical coefficient to infinity.

The genuine spatial-scaling exponents in dimension three are:
  cubic seven-derivative first monomial: λ^4;
  L² derivative-energy order k: λ^(2*k - 3), k = 0, 1, 2, 3;
  quadratic fourth-derivative dissipation: λ^5.

Squaring the θ=1/2 bound and cancelling positive common powers of λ
reduces the scalar model to
  M² * λ ≤ C² D² * (E0 + λ² E1 + λ⁴ E2 + λ⁶ E3).

We prove a bound for every λ ≥ 0, provided E0 > 0, E3 > 0 and D > 0.
This means isotropic dilations of one fixed shape cannot *on their own*
refute an endpoint estimate. No spatial-dilation identity for the actual
Schwartz carrier is claimed here; this is a scalar scaling-profile theorem.
The uniform estimate over ALL divergence-free Schwartz shapes is still open.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- The zeroth and third energy orders bound the middle spatial powers
from below, uniformly for nonnegative dilation parameter scale. -/
theorem criticalHalfDilation_energyPolynomial_lower
    (E0 E1 E2 E3 scale : ℝ)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1)
    (hE2 : 0 ≤ E2) (hE3 : 0 ≤ E3)
    (hscale : 0 ≤ scale) :
    scale * min E0 E3 ≤ E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3 := by
  have hm : 0 ≤ min E0 E3 := le_min hE0 hE3
  have hp2 : 0 ≤ scale ^ 2 * E1 := mul_nonneg (pow_nonneg hscale _) hE1
  have hp4 : 0 ≤ scale ^ 4 * E2 := mul_nonneg (pow_nonneg hscale _) hE2
  have hp6 : 0 ≤ scale ^ 6 * E3 := mul_nonneg (pow_nonneg hscale _) hE3
  by_cases hsmall : scale ≤ 1
  · calc
      scale * min E0 E3 ≤ 1 * min E0 E3 :=
        mul_le_mul_of_nonneg_right hsmall hm
      _ = min E0 E3 := one_mul _
      _ ≤ E0 := min_le_left _ _
      _ ≤ E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3 := by
        have hsum : 0 ≤ scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3 := by
          linarith only [hp2, hp4, hp6]
        linarith only [hsum]
  · have hscaleone : 1 ≤ scale := (lt_of_not_ge hsmall).le
    have hSix : scale ≤ scale ^ 6 := by
      have hp : scale ^ 1 ≤ scale ^ 6 := pow_le_pow_right₀ hscaleone (by norm_num)
      simpa only [pow_one] using hp
    calc
      scale * min E0 E3 ≤ scale ^ 6 * min E0 E3 :=
        mul_le_mul_of_nonneg_right hSix hm
      _ ≤ scale ^ 6 * E3 :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg hscale _)
      _ ≤ E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3 := by
        have hsum : 0 ≤ E0 + scale ^ 2 * E1 + scale ^ 4 * E2 := by
          linarith only [hE0, hp2, hp4]
        linarith only [hsum]

/-- A single squared coefficient bound for the two extreme energy orders
suffices for the full four-order dilation polynomial at every scale. -/
theorem criticalHalfDilation_uniform_squared_bound
    (M C D E0 E1 E2 E3 scale : ℝ)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1)
    (hE2 : 0 ≤ E2) (hE3 : 0 ≤ E3)
    (hscale : 0 ≤ scale)
    (hCoefficient : M ^ 2 ≤ C ^ 2 * D ^ 2 * min E0 E3) :
    M ^ 2 * scale ≤
      C ^ 2 * D ^ 2 * (E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3) := by
  have hProfile := criticalHalfDilation_energyPolynomial_lower
    E0 E1 E2 E3 scale hE0 hE1 hE2 hE3 hscale
  have hCoefNonneg : 0 ≤ C ^ 2 * D ^ 2 := by positivity
  calc
    M ^ 2 * scale ≤ (C ^ 2 * D ^ 2 * min E0 E3) * scale :=
      mul_le_mul_of_nonneg_right hCoefficient hscale
    _ = (C ^ 2 * D ^ 2) * (scale * min E0 E3) := by ring
    _ ≤ (C ^ 2 * D ^ 2) *
        (E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3) :=
      mul_le_mul_of_nonneg_left hProfile hCoefNonneg
    _ = C ^ 2 * D ^ 2 *
        (E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3) := by ring

/-- With strictly positive zeroth and third energies and dissipation,
one finite coefficient works at EVERY spatial dilation of a single scalar
profile. The coefficient is selected explicitly, not merely asserted. -/
theorem criticalHalfDilation_exists_uniform_coefficient
    (M D E0 E1 E2 E3 : ℝ)
    (hD : 0 < D) (hE0 : 0 < E0) (hE3 : 0 < E3)
    (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ scale : ℝ, 0 ≤ scale →
        M ^ 2 * scale ≤
          C ^ 2 * D ^ 2 *
            (E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3) := by
  have hm : 0 < min E0 E3 := lt_min hE0 hE3
  let T : ℝ := D ^ 2 * min E0 E3
  have hT : 0 < T := mul_pos (pow_pos hD 2) hm
  let C : ℝ := (M ^ 2 + 1) / T + 1
  have hC1 : 1 ≤ C := by
    dsimp [C]
    have hDiv : 0 ≤ (M ^ 2 + 1) / T :=
      div_nonneg (by positivity) hT.le
    linarith
  have hC2 : C ≤ C ^ 2 := by
    nlinarith [sq_nonneg (C - 1)]
  have hCT : C * T = M ^ 2 + 1 + T := by
    dsimp [C]
    rw [add_mul, div_mul_cancel₀ _ hT.ne', one_mul]
  have hCoefficient : M ^ 2 ≤ C ^ 2 * D ^ 2 * min E0 E3 := by
    calc
      M ^ 2 ≤ C * T := by rw [hCT]; linarith
      _ ≤ C ^ 2 * T := mul_le_mul_of_nonneg_right hC2 hT.le
      _ = C ^ 2 * D ^ 2 * min E0 E3 := by dsimp [T]; ring
  refine ⟨C, (zero_le_one.trans hC1), ?_⟩
  intro scale hscale
  exact criticalHalfDilation_uniform_squared_bound
    M C D E0 E1 E2 E3 scale
    hE0.le hE1 hE2 hE3.le hscale hCoefficient

end
end PrimeTensor.FirstMonomialTriad

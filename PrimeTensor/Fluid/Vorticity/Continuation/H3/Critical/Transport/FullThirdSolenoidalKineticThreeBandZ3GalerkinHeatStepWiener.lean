import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinOutputWiener
import Mathlib.Tactic

/-!
# Heat-damped finite Galerkin Wiener budget, including zero Fourier coefficients

The full-output complex Leray estimate from the imported module applies to
all ordered input pairs even when several pairs produce the same output.
Here the actual Euclidean Fourier Laplacian factor at frequency n is
`exp (-nu * h * ‖n‖₂²)`. An exponential-Euler Galerkin step is

  u⁺(n) = exp(-nu*h*‖n‖₂²) u(n) + h B_S(u,u)(n).

No assumption that any u(n) is nonzero is used. The ordinary norm triangle
inequality gives a one-step Wiener budget with a NONNEGATIVE viscous debt:

  W_r(u⁺) + Σ_{n∈S} e^(r|n|₁) (1-exp(-nu*h*‖n‖₂²)) ‖u(n)‖₂
    ≤ W_r(u) + h W_r(u) D_r(u).

The constant is one for every finite Galerkin set S and all r,nu,h ≥ 0.
The output can be a newly created mode with u(n)=0 initially.

This is a rigorous discrete exponential-Euler estimate, NOT the time
 derivative of a Galerkin ODE. Passing to continuous time and then to an
infinite Fourier solution requires further argument. No regularity or
terminal H3 continuation claim follows from this file alone.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

private abbrev Z3GalerkinBand244 := EuclideanSpace ℂ (Fin 3)

/-- Exact heat multiplier for the physical Euclidean Fourier Laplacian. -/
def thirdFullThreeBandZ3GalerkinHeatFactor244
    (nu h : ℝ) (n : thirdFullThreeBandZ3Index244) : ℝ :=
  Real.exp (-(nu * h *
    ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2))

/-- On a nonnegative time step, the physical heat multiplier lies in (0,1]. -/
theorem thirdFullThreeBand_z3GalerkinHeatFactor_bounds244
    (nu h : ℝ) (hnu : 0 ≤ nu) (hh : 0 ≤ h)
    (n : thirdFullThreeBandZ3Index244) :
    0 < thirdFullThreeBandZ3GalerkinHeatFactor244 nu h n ∧
    thirdFullThreeBandZ3GalerkinHeatFactor244 nu h n ≤ 1 := by
  constructor
  · unfold thirdFullThreeBandZ3GalerkinHeatFactor244
    exact Real.exp_pos _
  · have hx : -(nu * h *
          ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2) ≤ 0 := by
      apply neg_nonpos.mpr
      exact mul_nonneg (mul_nonneg hnu hh) (sq_nonneg _)
    unfold thirdFullThreeBandZ3GalerkinHeatFactor244
    calc
      Real.exp (-(nu * h *
          ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) ≤
          Real.exp (0 : ℝ) := Real.exp_le_exp.mpr hx
      _ = 1 := Real.exp_zero

/-- Exact exponential-Euler step: all ordered pairs contribute to each
selected output, including those whose coefficient was zero initially. -/
def thirdFullThreeBandZ3GalerkinHeatStep244
    (nu h : ℝ) (s : Finset thirdFullThreeBandZ3Index244)
    (u : thirdFullThreeBandZ3Index244 → Z3GalerkinBand244)
    (n : thirdFullThreeBandZ3Index244) : Z3GalerkinBand244 :=
  (thirdFullThreeBandZ3GalerkinHeatFactor244 nu h n) • (u n) +
    h • thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n

/-- Weighted Wiener norm and its single Fourier derivative cost. -/
def thirdFullThreeBandZ3GalerkinWienerMass244
    (r : ℝ) (s : Finset thirdFullThreeBandZ3Index244)
    (u : thirdFullThreeBandZ3Index244 → Z3GalerkinBand244) : ℝ :=
  ∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n * ‖u n‖

def thirdFullThreeBandZ3GalerkinWienerDerivative244
    (r : ℝ) (s : Finset thirdFullThreeBandZ3Index244)
    (u : thirdFullThreeBandZ3Index244 → Z3GalerkinBand244) : ℝ :=
  ∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
    thirdFullThreeBandZ3Degree244 n * ‖u n‖

/-- Viscosity paid during the heat part of a single finite step. -/
def thirdFullThreeBandZ3GalerkinHeatDebt244
    (nu h r : ℝ) (s : Finset thirdFullThreeBandZ3Index244)
    (u : thirdFullThreeBandZ3Index244 → Z3GalerkinBand244) : ℝ :=
  ∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
    ((1 - thirdFullThreeBandZ3GalerkinHeatFactor244 nu h n) * ‖u n‖)

/-- The norm budget never divides by ‖x‖; it remains valid at x=0.
This is the core replacement for an invalid pointwise derivative of norm. -/
theorem thirdFullThreeBand_normHeatPlusSource_budget244
    (x y : Z3GalerkinBand244) (sigma h : ℝ)
    (hsigma : 0 ≤ sigma) (hh : 0 ≤ h) :
    ‖sigma • x + h • y‖ + (1 - sigma) * ‖x‖ ≤
      ‖x‖ + h * ‖y‖ := by
  have hσ : ‖sigma • x‖ = sigma * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsigma]
  have hH : ‖h • y‖ = h * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  calc
    ‖sigma • x + h • y‖ + (1 - sigma) * ‖x‖ ≤
        (‖sigma • x‖ + ‖h • y‖) + (1 - sigma) * ‖x‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ = ‖x‖ + h * ‖y‖ := by rw [hσ, hH]; ring

/-- The exact heat debt is nonnegative on every finite Galerkin set. -/
theorem thirdFullThreeBand_z3GalerkinHeatDebt_nonneg244
    (nu h r : ℝ) (s : Finset thirdFullThreeBandZ3Index244)
    (u : thirdFullThreeBandZ3Index244 → Z3GalerkinBand244)
    (hnu : 0 ≤ nu) (hh : 0 ≤ h) :
    0 ≤ thirdFullThreeBandZ3GalerkinHeatDebt244 nu h r s u := by
  unfold thirdFullThreeBandZ3GalerkinHeatDebt244
  apply Finset.sum_nonneg
  intro n hn
  have hfactor := (thirdFullThreeBand_z3GalerkinHeatFactor_bounds244
    nu h hnu hh n).2
  exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le
    (mul_nonneg (sub_nonneg.mpr hfactor) (norm_nonneg (u n)))

/-- Uniform complete-output finite-Galerkin step estimate with its actual
nonnegative viscous payment. No coefficient is required to be nonzero. -/
theorem thirdFullThreeBand_z3GalerkinHeatStepWienerBudget244
    (nu h r : ℝ) (hnu : 0 ≤ nu) (hh : 0 ≤ h) (hr : 0 ≤ r)
    (s : Finset thirdFullThreeBandZ3Index244)
    (u : thirdFullThreeBandZ3Index244 → Z3GalerkinBand244) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s
      (thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u) +
      thirdFullThreeBandZ3GalerkinHeatDebt244 nu h r s u ≤
    thirdFullThreeBandZ3GalerkinWienerMass244 r s u +
      h * (thirdFullThreeBandZ3GalerkinWienerMass244 r s u *
        thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u) := by
  classical
  have hcomponent (n : thirdFullThreeBandZ3Index244) :
      thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖ +
      thirdFullThreeBandZ3Weight244 r n *
        ((1 - thirdFullThreeBandZ3GalerkinHeatFactor244 nu h n) * ‖u n‖) ≤
      thirdFullThreeBandZ3Weight244 r n * ‖u n‖ +
        h * (thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖) := by
    have hfac := (thirdFullThreeBand_z3GalerkinHeatFactor_bounds244
      nu h hnu hh n).1.le
    have hbasic := thirdFullThreeBand_normHeatPlusSource_budget244
      (u n) (thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n)
      (thirdFullThreeBandZ3GalerkinHeatFactor244 nu h n) h hfac hh
    calc
      thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖ +
        thirdFullThreeBandZ3Weight244 r n *
          ((1 - thirdFullThreeBandZ3GalerkinHeatFactor244 nu h n) * ‖u n‖) =
        thirdFullThreeBandZ3Weight244 r n *
          (‖(thirdFullThreeBandZ3GalerkinHeatFactor244 nu h n) • u n +
              h • thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖ +
            (1 - thirdFullThreeBandZ3GalerkinHeatFactor244 nu h n) * ‖u n‖) := by
          unfold thirdFullThreeBandZ3GalerkinHeatStep244
          ring
      _ ≤ thirdFullThreeBandZ3Weight244 r n *
          (‖u n‖ + h *
            ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖) :=
          mul_le_mul_of_nonneg_left hbasic
            (thirdFullThreeBand_z3Weight_pos244 r n).le
      _ = thirdFullThreeBandZ3Weight244 r n * ‖u n‖ +
          h * (thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖) := by ring
  have hsum :
      thirdFullThreeBandZ3GalerkinWienerMass244 r s
          (thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u) +
        thirdFullThreeBandZ3GalerkinHeatDebt244 nu h r s u ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 r s u +
        h * (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖) := by
    unfold thirdFullThreeBandZ3GalerkinWienerMass244
      thirdFullThreeBandZ3GalerkinHeatDebt244
    calc
      (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
           ‖thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖) +
        (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
           ((1 - thirdFullThreeBandZ3GalerkinHeatFactor244 nu h n) * ‖u n‖)) =
        ∑ n ∈ s, (thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖ +
          thirdFullThreeBandZ3Weight244 r n *
            ((1 - thirdFullThreeBandZ3GalerkinHeatFactor244 nu h n) * ‖u n‖)) := by
          rw [Finset.sum_add_distrib]
      _ ≤ ∑ n ∈ s, (thirdFullThreeBandZ3Weight244 r n * ‖u n‖ +
            h * (thirdFullThreeBandZ3Weight244 r n *
              ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖)) := by
          apply Finset.sum_le_sum
          intro n hn
          exact hcomponent n
      _ = (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n * ‖u n‖) +
          h * (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hQ :
      (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖) ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 r s u *
        thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u := by
    exact thirdFullThreeBand_z3GalerkinAllOutputWienerBound244 r hr s s s u u
  exact hsum.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hQ hh)
    (thirdFullThreeBandZ3GalerkinWienerMass244 r s u))

/-- Dropping a NONNEGATIVE heat debt yields the practical norm-growth bound. -/
theorem thirdFullThreeBand_z3GalerkinHeatStepWienerGrowth244
    (nu h r : ℝ) (hnu : 0 ≤ nu) (hh : 0 ≤ h) (hr : 0 ≤ r)
    (s : Finset thirdFullThreeBandZ3Index244)
    (u : thirdFullThreeBandZ3Index244 → Z3GalerkinBand244) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s
      (thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u) ≤
    thirdFullThreeBandZ3GalerkinWienerMass244 r s u +
      h * (thirdFullThreeBandZ3GalerkinWienerMass244 r s u *
        thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u) := by
  have hBudget := thirdFullThreeBand_z3GalerkinHeatStepWienerBudget244
    nu h r hnu hh hr s u
  have hDebt := thirdFullThreeBand_z3GalerkinHeatDebt_nonneg244
    nu h r s u hnu hh
  linarith

/-- A zero input coefficient is allowed; nonlinear ordered interactions can
create it immediately. No quotient by the old amplitude is formed. -/
theorem thirdFullThreeBand_z3GalerkinHeatStep_at_zero244
    (nu h : ℝ) (hh : 0 ≤ h)
    (s : Finset thirdFullThreeBandZ3Index244)
    (u : thirdFullThreeBandZ3Index244 → Z3GalerkinBand244)
    (n : thirdFullThreeBandZ3Index244) (hzero : u n = 0) :
    ‖thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖ =
      h * ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n‖ := by
  unfold thirdFullThreeBandZ3GalerkinHeatStep244
  rw [hzero, smul_zero, zero_add, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hh]

end
end PrimeTensor.FirstMonomialTriad

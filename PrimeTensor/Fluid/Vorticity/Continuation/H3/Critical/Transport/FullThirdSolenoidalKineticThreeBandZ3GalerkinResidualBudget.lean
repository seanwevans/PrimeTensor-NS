import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinHeatStepWiener
import Mathlib.Tactic

/-!
# Residual-stable Galerkin Wiener budgets and the ODE-consistency gate

The preceding theorem controls one *exact* heat-damped Galerkin step.
Here we remove the assumption that the next coefficient equals that step:
its full weighted residual appears with coefficient one. This gives a
cumulative estimate along ANY finite sequence of approximate states, with
all old zero Fourier coefficients and newly generated modes allowed.

If a path has per-step weighted residual at most C*h_i^2 and its mesh is at
most hMax, the ENTIRE accumulated error is at most C*hMax*sum_i h_i.
Consequently the discrete heat debts survive the O(hMax) consistency
passage, provided the usual finite-dimensional ODE local truncation bound
is established. This module does not assert that bound or an ODE solution.

The final theorem identifies an explicit, support-independent analytic
reserve condition sufficient to control TWO frequency derivatives of the
actual complete Leray output. It isolates the precise strengthened Wiener
weight needed for a Galerkin-uniform exponential-Euler residual bound.

No Fourier coefficient is ever divided by its amplitude, and no native
prime-multiset addition or Fourier PDE existence theorem is introduced.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

private abbrev Z3ResidualBand244 := EuclideanSpace ℂ (Fin 3)

/-- Exact weighted error between an arbitrary next state and the genuine
full-output exponential-Euler Galerkin step. No equality of states is assumed. -/
def thirdFullThreeBandZ3GalerkinStepResidual244
    (nu h r : ℝ) (s : Finset thirdFullThreeBandZ3Index244)
    (u v : thirdFullThreeBandZ3Index244 → Z3ResidualBand244) : ℝ :=
  ∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
    ‖v n - thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖

/-- A weighted residual is nonnegative at every radius and every state. -/
theorem thirdFullThreeBand_z3GalerkinStepResidual_nonneg244
    (nu h r : ℝ) (s : Finset thirdFullThreeBandZ3Index244)
    (u v : thirdFullThreeBandZ3Index244 → Z3ResidualBand244) :
    0 ≤ thirdFullThreeBandZ3GalerkinStepResidual244 nu h r s u v := by
  unfold thirdFullThreeBandZ3GalerkinStepResidual244
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le (norm_nonneg _)

/-- The full Wiener norm is Lipschitz with constant one in the sum of
componentwise errors. This also holds when the comparison coefficient is 0. -/
theorem thirdFullThreeBand_z3GalerkinMass_le_step_add_residual244
    (nu h r : ℝ) (s : Finset thirdFullThreeBandZ3Index244)
    (u v : thirdFullThreeBandZ3Index244 → Z3ResidualBand244) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s v ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 r s
        (thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u) +
      thirdFullThreeBandZ3GalerkinStepResidual244 nu h r s u v := by
  classical
  unfold thirdFullThreeBandZ3GalerkinWienerMass244
    thirdFullThreeBandZ3GalerkinStepResidual244
  calc
    (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n * ‖v n‖) ≤
      ∑ n ∈ s,
        (thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖ +
         thirdFullThreeBandZ3Weight244 r n *
            ‖v n - thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖) := by
      apply Finset.sum_le_sum
      intro n hn
      have hTriangle :
          ‖v n‖ ≤
            ‖thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖ +
            ‖v n - thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖ := by
        have hNormAdd := norm_add_le
          (thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n)
          (v n - thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n)
        have heq :
            thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n +
              (v n - thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n) =
                v n := by abel
        rw [heq] at hNormAdd
        exact hNormAdd
      calc
        thirdFullThreeBandZ3Weight244 r n * ‖v n‖ ≤
          thirdFullThreeBandZ3Weight244 r n *
            (‖thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖ +
             ‖v n - thirdFullThreeBandZ3GalerkinHeatStep244 nu h s u n‖) :=
          mul_le_mul_of_nonneg_left hTriangle
            (thirdFullThreeBand_z3Weight_pos244 r n).le
        _ = _ := by ring
    _ = _ := by rw [Finset.sum_add_distrib]

/-- A robust version of the real full-output heat-step theorem: an
arbitrary next state costs exactly its weighted local consistency residual. -/
theorem thirdFullThreeBand_z3GalerkinResidualHeatBudget244
    (nu h r : ℝ) (hnu : 0 ≤ nu) (hh : 0 ≤ h) (hr : 0 ≤ r)
    (s : Finset thirdFullThreeBandZ3Index244)
    (u v : thirdFullThreeBandZ3Index244 → Z3ResidualBand244) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s v +
      thirdFullThreeBandZ3GalerkinHeatDebt244 nu h r s u ≤
    thirdFullThreeBandZ3GalerkinWienerMass244 r s u +
      h * (thirdFullThreeBandZ3GalerkinWienerMass244 r s u *
        thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u) +
      thirdFullThreeBandZ3GalerkinStepResidual244 nu h r s u v := by
  have hTriangle := thirdFullThreeBand_z3GalerkinMass_le_step_add_residual244
    nu h r s u v
  have hStep := thirdFullThreeBand_z3GalerkinHeatStepWienerBudget244
    nu h r hnu hh hr s u
  linarith

/-- The cumulative Wiener balance telescopes for arbitrarily many steps,
including zero coefficients and independent residuals at every step. -/
theorem thirdFullThreeBand_z3GalerkinCumulativeResidualBudget244
    (N : ℕ) (nu r : ℝ) (hnu : 0 ≤ nu) (hr : 0 ≤ r)
    (s : Finset thirdFullThreeBandZ3Index244)
    (h : ℕ → ℝ)
    (u : ℕ → thirdFullThreeBandZ3Index244 → Z3ResidualBand244)
    (hh : ∀ i, 0 ≤ h i) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s (u N) +
      (∑ i ∈ Finset.range N,
        thirdFullThreeBandZ3GalerkinHeatDebt244 nu (h i) r s (u i)) ≤
    thirdFullThreeBandZ3GalerkinWienerMass244 r s (u 0) +
      (∑ i ∈ Finset.range N,
        (h i * (thirdFullThreeBandZ3GalerkinWienerMass244 r s (u i) *
          thirdFullThreeBandZ3GalerkinWienerDerivative244 r s (u i)) +
         thirdFullThreeBandZ3GalerkinStepResidual244
           nu (h i) r s (u i) (u (i + 1)))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hStep := thirdFullThreeBand_z3GalerkinResidualHeatBudget244
      nu (h N) r hnu (hh N) hr s (u N) (u (N + 1))
    simp only [Finset.sum_range_succ]
    linarith

/-- All accumulated viscous heat debts are genuinely nonnegative. -/
theorem thirdFullThreeBand_z3GalerkinCumulativeHeatDebt_nonneg244
    (N : ℕ) (nu r : ℝ) (hnu : 0 ≤ nu)
    (s : Finset thirdFullThreeBandZ3Index244)
    (h : ℕ → ℝ)
    (u : ℕ → thirdFullThreeBandZ3Index244 → Z3ResidualBand244)
    (hh : ∀ i, 0 ≤ h i) :
    0 ≤ ∑ i ∈ Finset.range N,
      thirdFullThreeBandZ3GalerkinHeatDebt244 nu (h i) r s (u i) := by
  apply Finset.sum_nonneg
  intro i hi
  exact thirdFullThreeBand_z3GalerkinHeatDebt_nonneg244
    nu (h i) r s (u i) hnu (hh i)

/-- The finite-Galerkin ODE consistency gate: if each weighted local
exponential-Euler residual is O(h_i^2), then the TOTAL error is O(hMax*T).
Neither the estimate nor its coefficient depends on the number of steps. -/
theorem thirdFullThreeBand_z3GalerkinResidualSum_quadraticMesh244
    (N : ℕ) (nu r C hMax : ℝ)
    (s : Finset thirdFullThreeBandZ3Index244)
    (h : ℕ → ℝ)
    (u : ℕ → thirdFullThreeBandZ3Index244 → Z3ResidualBand244)
    (hC : 0 ≤ C) (hh : ∀ i, 0 ≤ h i)
    (hMesh : ∀ i ∈ Finset.range N, h i ≤ hMax)
    (hLocal : ∀ i ∈ Finset.range N,
      thirdFullThreeBandZ3GalerkinStepResidual244
        nu (h i) r s (u i) (u (i + 1)) ≤ C * (h i) ^ 2) :
    (∑ i ∈ Finset.range N,
      thirdFullThreeBandZ3GalerkinStepResidual244
        nu (h i) r s (u i) (u (i + 1))) ≤
      C * hMax * (∑ i ∈ Finset.range N, h i) := by
  calc
    _ ≤ ∑ i ∈ Finset.range N, (C * hMax) * h i := by
      apply Finset.sum_le_sum
      intro i hi
      have hm := hMesh i hi
      have hlow := hh i
      have hSq : (h i) ^ 2 ≤ hMax * h i := by
        have hp := mul_nonneg (sub_nonneg.mpr hm) hlow
        nlinarith
      calc
        _ ≤ C * (h i) ^ 2 := hLocal i hi
        _ ≤ C * (hMax * h i) :=
          mul_le_mul_of_nonneg_left hSq hC
        _ = (C * hMax) * h i := by ring
    _ = C * hMax * (∑ i ∈ Finset.range N, h i) := by
      rw [Finset.mul_sum]

/-- The decisive uniform-mesh form of the telescoping budget.
A genuine Galerkin ODE path with a cutoff-uniform local residual constant C
inherits this estimate, so the consistency error disappears as hMax→0.
The analytic estimate needed to establish that uniform C is not assumed away. -/
theorem thirdFullThreeBand_z3GalerkinCumulativeOmeshBudget244
    (N : ℕ) (nu r C hMax : ℝ) (hnu : 0 ≤ nu)
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (s : Finset thirdFullThreeBandZ3Index244)
    (h : ℕ → ℝ)
    (u : ℕ → thirdFullThreeBandZ3Index244 → Z3ResidualBand244)
    (hh : ∀ i, 0 ≤ h i)
    (hMesh : ∀ i ∈ Finset.range N, h i ≤ hMax)
    (hLocal : ∀ i ∈ Finset.range N,
      thirdFullThreeBandZ3GalerkinStepResidual244
        nu (h i) r s (u i) (u (i + 1)) ≤ C * (h i) ^ 2) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s (u N) +
      (∑ i ∈ Finset.range N,
        thirdFullThreeBandZ3GalerkinHeatDebt244 nu (h i) r s (u i)) ≤
    thirdFullThreeBandZ3GalerkinWienerMass244 r s (u 0) +
      (∑ i ∈ Finset.range N,
        h i * (thirdFullThreeBandZ3GalerkinWienerMass244 r s (u i) *
          thirdFullThreeBandZ3GalerkinWienerDerivative244 r s (u i))) +
      C * hMax * (∑ i ∈ Finset.range N, h i) := by
  have hBudget := thirdFullThreeBand_z3GalerkinCumulativeResidualBudget244
    N nu r hnu hr s h u hh
  have hError := thirdFullThreeBand_z3GalerkinResidualSum_quadraticMesh244
    N nu r C hMax s h u hC hh hMesh hLocal
  have hSplit :
      (∑ i ∈ Finset.range N,
        (h i * (thirdFullThreeBandZ3GalerkinWienerMass244 r s (u i) *
          thirdFullThreeBandZ3GalerkinWienerDerivative244 r s (u i)) +
         thirdFullThreeBandZ3GalerkinStepResidual244
           nu (h i) r s (u i) (u (i + 1)))) =
      (∑ i ∈ Finset.range N,
        h i * (thirdFullThreeBandZ3GalerkinWienerMass244 r s (u i) *
          thirdFullThreeBandZ3GalerkinWienerDerivative244 r s (u i))) +
      (∑ i ∈ Finset.range N,
        thirdFullThreeBandZ3GalerkinStepResidual244
          nu (h i) r s (u i) (u (i + 1))) := by
    rw [Finset.sum_add_distrib]
  rw [hSplit] at hBudget
  linarith

/-- The actual Fourier Laplacian multiplier cannot exceed the square of
the genuine integer-lattice l1 frequency degree. -/
theorem thirdFullThreeBand_z3Laplacian_le_degreeSquare244
    (n : thirdFullThreeBandZ3Index244) :
    ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 ≤
      (thirdFullThreeBandZ3Degree244 n) ^ 2 := by
  have h := thirdFullThreeBand_z3ComplexFrequency_norm_le_degree244 n
  have hn := norm_nonneg (thirdFullThreeBandZ3ComplexFrequency244 n)
  have hd := thirdFullThreeBand_z3Degree_nonneg244 n
  have hp : 0 ≤
      (thirdFullThreeBandZ3Degree244 n -
        ‖thirdFullThreeBandZ3ComplexFrequency244 n‖) *
      (thirdFullThreeBandZ3Degree244 n +
        ‖thirdFullThreeBandZ3ComplexFrequency244 n‖) :=
    mul_nonneg (sub_nonneg.mpr h) (add_nonneg hd hn)
  nlinarith

/-- Analytic-radius reserve for TWO frequency derivatives of the full
projected quadratic output. This includes all collision frequencies.
A uniform envelope on the two exponential weights gives a cutoff-free
source bound, which is precisely the spatial input needed for a uniform
second-order Galerkin exponential-Euler consistency estimate. -/
theorem thirdFullThreeBand_z3GalerkinAnalyticReserveSource244
    (r R C : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (outputs s t : Finset thirdFullThreeBandZ3Index244)
    (u v : thirdFullThreeBandZ3Index244 → Z3ResidualBand244)
    (hReserve : ∀ n ∈ outputs,
       ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
         thirdFullThreeBandZ3Weight244 r n ≤
       C * thirdFullThreeBandZ3Weight244 R n) :
    (∑ n ∈ outputs,
      ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
        thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n‖) ≤
      C * ((∑ p ∈ s, thirdFullThreeBandZ3Weight244 R p * ‖u p‖) *
        (∑ q ∈ t, thirdFullThreeBandZ3Weight244 R q *
          thirdFullThreeBandZ3Degree244 q * ‖v q‖)) := by
  classical
  have hOutput := thirdFullThreeBand_z3GalerkinAllOutputWienerBound244
    R hR outputs s t u v
  have hWeighted :
      (∑ n ∈ outputs,
        ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
          thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n‖) ≤
      ∑ n ∈ outputs,
        C * (thirdFullThreeBandZ3Weight244 R n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n‖) := by
    apply Finset.sum_le_sum
    intro n hn
    have h := mul_le_mul_of_nonneg_right (hReserve n hn)
      (norm_nonneg (thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n))
    calc
      _ ≤ (C * thirdFullThreeBandZ3Weight244 R n) *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n‖ := h
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ outputs,
        C * (thirdFullThreeBandZ3Weight244 R n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n‖) := hWeighted
    _ = C * (∑ n ∈ outputs, thirdFullThreeBandZ3Weight244 R n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n‖) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hOutput hC

end
end PrimeTensor.FirstMonomialTriad

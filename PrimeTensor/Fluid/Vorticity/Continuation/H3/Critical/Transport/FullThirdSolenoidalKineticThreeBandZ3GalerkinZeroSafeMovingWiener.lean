import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinMovingAnalyticRadius
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Zero-safe moving analytic Wiener derivative for the actual Z³ Galerkin ODE

The ordinary norm is not differentiable when a Fourier coefficient vanishes.
The usual formal derivative of the moving Wiener sum is therefore invalid.
We replace each coefficient norm with its genuinely smooth amplitude

    A_ε(x) = sqrt (‖x‖² + ε²),  ε > 0.

Its derivative exists at *every* coefficient, including 0, and contains the
real inner product with the actual Galerkin field. The viscous Laplacian
contributes a nonpositive term without dividing by ‖x‖.

For the actual three-complex-coordinate full-Leray Galerkin ODE and the moving
radius r_a(t) = log 2 - 100(t-a), the finite regularized Wiener mass M_ε(t)
satisfies the differential inequality

    M_ε'(t) ≤ (M_ε(t) - 100) D_ε(t).

This is exact for each finite output set and has no Fourier cardinality or
frequency-cutoff constant. The regularization is performed only at finite S;
its initial excess is at most ε times the total analytic weight, which may
depend on S and is not represented as a uniform error.

This module does not construct the ODE flow or prove the global-in-time
comparison theorem M_ε ≤ 100. The analytic first-exit / Gronwall comparison,
then passage ε↓0 and ODE existence, remain separate obligations.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Set
open scoped Interval

noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev ZeroIndex244 := thirdFullThreeBandZ3Index244
private abbrev ZeroBand244 := EuclideanSpace ℂ (Fin 3)

/-- A strictly positive, smooth replacement of the complex Euclidean norm. -/
noncomputable def thirdFullThreeBandZ3SmoothAmplitude244
    (epsilon : ℝ) (x : ZeroBand244) : ℝ :=
  Real.sqrt (‖x‖ ^ 2 + epsilon ^ 2)

/-- The regularized mass of the complete retained Fourier spectrum. -/
noncomputable def thirdFullThreeBandZ3GalerkinSmoothWienerMass244
    (epsilon r : ℝ) (s : Finset ZeroIndex244)
    (u : ZeroIndex244 → ZeroBand244) : ℝ :=
  ∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
    thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u n)

/-- Its differentiated-radius cost; no division by old amplitudes. -/
noncomputable def thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244
    (epsilon r : ℝ) (s : Finset ZeroIndex244)
    (u : ZeroIndex244 → ZeroBand244) : ℝ :=
  ∑ n ∈ s, thirdFullThreeBandZ3Degree244 n *
    thirdFullThreeBandZ3Weight244 r n *
    thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u n)

/-- Positive even for the zero Fourier coefficient x = 0. -/
theorem thirdFullThreeBand_z3SmoothAmplitude_pos244
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (x : ZeroBand244) :
    0 < thirdFullThreeBandZ3SmoothAmplitude244 epsilon x := by
  unfold thirdFullThreeBandZ3SmoothAmplitude244
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg (‖x‖), sq_pos_of_pos hepsilon]

/-- The regularization majorizes the true norm, uniformly at zero. -/
theorem thirdFullThreeBand_z3Norm_le_smoothAmplitude244
    (epsilon : ℝ) (x : ZeroBand244) :
    ‖x‖ ≤ thirdFullThreeBandZ3SmoothAmplitude244 epsilon x := by
  unfold thirdFullThreeBandZ3SmoothAmplitude244
  apply (Real.le_sqrt (norm_nonneg x) (by positivity)).2
  nlinarith [sq_nonneg epsilon]

/-- Its pointwise excess over the true norm is at most epsilon ≥ 0. -/
theorem thirdFullThreeBand_z3SmoothAmplitude_le_norm_add244
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (x : ZeroBand244) :
    thirdFullThreeBandZ3SmoothAmplitude244 epsilon x ≤ ‖x‖ + epsilon := by
  unfold thirdFullThreeBandZ3SmoothAmplitude244
  apply (Real.sqrt_le_iff).2
  constructor
  · exact add_nonneg (norm_nonneg x) hepsilon
  · nlinarith [mul_nonneg (norm_nonneg x) hepsilon]

/-- Every finite true Wiener mass is bounded by its smooth counterpart. -/
theorem thirdFullThreeBand_z3WienerMass_le_smooth244
    (epsilon r : ℝ) (s : Finset ZeroIndex244)
    (u : ZeroIndex244 → ZeroBand244) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s u ≤
      thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon r s u := by
  classical
  unfold thirdFullThreeBandZ3GalerkinWienerMass244
    thirdFullThreeBandZ3GalerkinSmoothWienerMass244
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_left
    (thirdFullThreeBand_z3Norm_le_smoothAmplitude244 epsilon (u n))
    (thirdFullThreeBand_z3Weight_pos244 r n).le

/-- The differentiated Fourier norm is also bounded by its smooth version. -/
theorem thirdFullThreeBand_z3WienerDerivative_le_smooth244
    (epsilon r : ℝ) (s : Finset ZeroIndex244)
    (u : ZeroIndex244 → ZeroBand244) :
    thirdFullThreeBandZ3GalerkinWienerDerivative244 r s u ≤
      thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244 epsilon r s u := by
  classical
  unfold thirdFullThreeBandZ3GalerkinWienerDerivative244
    thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244
  apply Finset.sum_le_sum
  intro n hn
  have hWeightDegree : 0 ≤
      thirdFullThreeBandZ3Weight244 r n * thirdFullThreeBandZ3Degree244 n :=
    mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le
      (thirdFullThreeBand_z3Degree_nonneg244 n)
  have h := mul_le_mul_of_nonneg_left
    (thirdFullThreeBand_z3Norm_le_smoothAmplitude244 epsilon (u n))
    hWeightDegree
  calc
    _ ≤ (thirdFullThreeBandZ3Weight244 r n *
          thirdFullThreeBandZ3Degree244 n) *
          thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u n) := h
    _ = _ := by ring

/-- The regularized differentiated mass is nonnegative, even at zero modes. -/
theorem thirdFullThreeBand_z3SmoothWienerDerivative_nonneg244
    (epsilon r : ℝ) (s : Finset ZeroIndex244)
    (u : ZeroIndex244 → ZeroBand244) :
    0 ≤ thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244 epsilon r s u := by
  unfold thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg
    (mul_nonneg (thirdFullThreeBand_z3Degree_nonneg244 n)
      (thirdFullThreeBand_z3Weight_pos244 r n).le)
    (Real.sqrt_nonneg _)

/-- The initial regularization excess is explicitly proportional to ε
and the finite analytic weight sum. That sum need NOT be cutoff-uniform;
ε may be chosen separately for each finite Galerkin set. -/
theorem thirdFullThreeBand_z3SmoothWienerMass_le_true_add_error244
    (epsilon r : ℝ) (hepsilon : 0 ≤ epsilon)
    (s : Finset ZeroIndex244) (u : ZeroIndex244 → ZeroBand244) :
    thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon r s u ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 r s u +
      epsilon * (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n) := by
  classical
  unfold thirdFullThreeBandZ3GalerkinSmoothWienerMass244
    thirdFullThreeBandZ3GalerkinWienerMass244
  calc
    _ ≤ ∑ n ∈ s,
        (thirdFullThreeBandZ3Weight244 r n * ‖u n‖ +
          epsilon * thirdFullThreeBandZ3Weight244 r n) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := mul_le_mul_of_nonneg_left
        (thirdFullThreeBand_z3SmoothAmplitude_le_norm_add244 epsilon hepsilon (u n))
        (thirdFullThreeBand_z3Weight_pos244 r n).le
      calc
        _ ≤ thirdFullThreeBandZ3Weight244 r n * (‖u n‖ + epsilon) := h
        _ = _ := by ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Smooth differentiation of the true complex Euclidean amplitude.
Unlike deriv ‖F‖, this remains valid when F(t)=0. -/
theorem thirdFullThreeBand_z3SmoothAmplitude_hasDerivAt244
    (epsilon t : ℝ) (hepsilon : 0 < epsilon)
    (F : ℝ → ZeroBand244) (v : ZeroBand244)
    (hF : HasDerivAt F v t) :
    HasDerivAt
      (fun z : ℝ => thirdFullThreeBandZ3SmoothAmplitude244 epsilon (F z))
      ((inner ℝ (F t) v) /
        thirdFullThreeBandZ3SmoothAmplitude244 epsilon (F t)) t := by
  have hArgument : 0 < ‖F t‖ ^ 2 + epsilon ^ 2 := by
    nlinarith [sq_nonneg (‖F t‖), sq_pos_of_pos hepsilon]
  have hSq : HasDerivAt
      (fun z : ℝ => ‖F z‖ ^ 2 + epsilon ^ 2)
      (2 * inner ℝ (F t) v) t :=
    (hF.norm_sq).add_const (epsilon ^ 2)
  have hRoot := hSq.sqrt (ne_of_gt hArgument)
  have hDenom : Real.sqrt (‖F t‖ ^ 2 + epsilon ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hArgument)
  have hCoeff :
      (2 * inner ℝ (F t) v) /
          (2 * Real.sqrt (‖F t‖ ^ 2 + epsilon ^ 2)) =
        (inner ℝ (F t) v) /
          Real.sqrt (‖F t‖ ^ 2 + epsilon ^ 2) := by
    field_simp [hDenom] <;> ring
  exact hRoot.congr_deriv (by simpa only [thirdFullThreeBandZ3SmoothAmplitude244] using hCoeff)

/-- Viscous damping is nonpositive in the regularized norm derivative.
The full real-inner-product forcing costs no more than its Euclidean norm.
No coefficient is assumed nonzero. -/
theorem thirdFullThreeBand_z3SmoothDampedDerivative_le_source244
    (lambda epsilon : ℝ) (hlambda : 0 ≤ lambda)
    (hepsilon : 0 < epsilon) (x q : ZeroBand244) :
    inner ℝ x ((-lambda) • x + q) /
      thirdFullThreeBandZ3SmoothAmplitude244 epsilon x ≤ ‖q‖ := by
  have hAmpPos := thirdFullThreeBand_z3SmoothAmplitude_pos244 epsilon hepsilon x
  have hAmp : ‖x‖ ≤ thirdFullThreeBandZ3SmoothAmplitude244 epsilon x :=
    thirdFullThreeBand_z3Norm_le_smoothAmplitude244 epsilon x
  have hInner : inner ℝ x ((-lambda) • x + q) ≤ ‖x‖ * ‖q‖ := by
    have hInnerSource : inner ℝ x q ≤ ‖x‖ * ‖q‖ := real_inner_le_norm x q
    have hDamp : 0 ≤ lambda * ‖x‖ ^ 2 := mul_nonneg hlambda (sq_nonneg _)
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    nlinarith
  apply (div_le_iff₀ hAmpPos).2
  calc
    inner ℝ x ((-lambda) • x + q) ≤ ‖x‖ * ‖q‖ := hInner
    _ ≤ thirdFullThreeBandZ3SmoothAmplitude244 epsilon x * ‖q‖ :=
      mul_le_mul_of_nonneg_right hAmp (norm_nonneg q)
    _ = ‖q‖ * thirdFullThreeBandZ3SmoothAmplitude244 epsilon x := by ring

/-- One exact moving-weighted Galerkin coefficient, including zeros.
Its strong derivative is bounded by source gain minus the analytic-radius
expense, while the physical viscous Laplacian is dissipative. -/
theorem thirdFullThreeBand_z3ZeroSafeMovingMode_hasDerivAt244
    (mu a t epsilon : ℝ) (hmu : 0 ≤ mu) (hepsilon : 0 < epsilon)
    (s : Finset ZeroIndex244) (u : ℝ → ZeroIndex244 → ZeroBand244)
    (n : ZeroIndex244)
    (hODE : HasDerivAt (fun z : ℝ => u z n)
      (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t) :
    HasDerivAt
      (fun z : ℝ =>
        thirdFullThreeBandZ3Weight244
          (thirdFullThreeBandZ3GalerkinMovingRadius244 a z) n *
        thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u z n))
      ((-100 * thirdFullThreeBandZ3Degree244 n) *
          thirdFullThreeBandZ3Weight244
            (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) n *
          thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u t n) +
        thirdFullThreeBandZ3Weight244
          (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) n *
          (inner ℝ (u t n)
            (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) /
            thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u t n))) t := by
  have hWeight := thirdFullThreeBand_z3MovingWeight_hasDerivAt244 a t n
  have hAmp := thirdFullThreeBand_z3SmoothAmplitude_hasDerivAt244
    epsilon t hepsilon (fun z : ℝ => u z n)
    (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) hODE
  exact hWeight.mul hAmp

/-- Actual moving-radius smooth Wiener Dini control. The function is
*ordinary differentiable*, not merely Dini differentiable, at every zero
coefficient. The full projected quadratic source and Laplacian are retained.

Crucially the RHS (Mε - 100) Dε has NO Fourier-cutoff constant. -/
theorem thirdFullThreeBand_z3ZeroSafeMovingWiener_differential244
    (mu a t epsilon : ℝ) (hmu : 0 ≤ mu) (hepsilon : 0 < epsilon)
    (s : Finset ZeroIndex244) (u : ℝ → ZeroIndex244 → ZeroBand244)
    (hRadius : 0 ≤ thirdFullThreeBandZ3GalerkinMovingRadius244 a t)
    (hODE : ∀ n ∈ s, HasDerivAt (fun z : ℝ => u z n)
      (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t) :
    ∃ d : ℝ,
      HasDerivAt
        (fun z : ℝ =>
          thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon
            (thirdFullThreeBandZ3GalerkinMovingRadius244 a z) s (u z))
        d t ∧
      d ≤ (thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon
              (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t) - 100) *
            thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244 epsilon
              (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t) := by
  classical
  let r := thirdFullThreeBandZ3GalerkinMovingRadius244 a t
  let w : ZeroIndex244 → ℝ := thirdFullThreeBandZ3Weight244 r
  let A : ZeroIndex244 → ℝ := fun n =>
    thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u t n)
  let Q : ZeroIndex244 → ZeroBand244 :=
    thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t)
  let c : ZeroIndex244 → ℝ := fun n =>
    (-100 * thirdFullThreeBandZ3Degree244 n) * w n * A n +
      w n * (inner ℝ (u t n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) / A n)
  let d := ∑ n ∈ s, c n
  refine ⟨d, ?_, ?_⟩
  · unfold thirdFullThreeBandZ3GalerkinSmoothWienerMass244
    exact HasDerivAt.fun_sum (fun n hn =>
      thirdFullThreeBand_z3ZeroSafeMovingMode_hasDerivAt244
        mu a t epsilon hmu hepsilon s u n (hODE n hn))
  have hModeBound (n : ZeroIndex244) :
      c n ≤ w n * ‖Q n‖ -
        100 * (thirdFullThreeBandZ3Degree244 n * w n * A n) := by
    have hLambda : 0 ≤ mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 :=
      mul_nonneg hmu (sq_nonneg _)
    have hInner :
        inner ℝ (u t n)
            (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) / A n ≤
          ‖Q n‖ := by
      change inner ℝ (u t n)
          ((-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
            u t n + Q n) /
          thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u t n) ≤ ‖Q n‖
      exact thirdFullThreeBand_z3SmoothDampedDerivative_le_source244
        _ epsilon hLambda hepsilon (u t n) (Q n)
    have h := mul_le_mul_of_nonneg_left hInner
      (thirdFullThreeBand_z3Weight_pos244 r n).le
    dsimp only [c]
    calc
      _ ≤ (-100 * thirdFullThreeBandZ3Degree244 n) * w n * A n +
          w n * ‖Q n‖ := add_le_add_right h _
      _ = _ := by ring
  have hBound :
      d ≤ thirdFullThreeBandZ3GalerkinWienerMass244 r s Q -
        100 * thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244 epsilon r s (u t) := by
    calc
      d ≤ ∑ n ∈ s, (w n * ‖Q n‖ -
          100 * (thirdFullThreeBandZ3Degree244 n * w n * A n)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hModeBound n
      _ = (∑ n ∈ s, w n * ‖Q n‖) -
          100 * (∑ n ∈ s,
            thirdFullThreeBandZ3Degree244 n * w n * A n) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := rfl
  have hQ : thirdFullThreeBandZ3GalerkinWienerMass244 r s Q ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 r s (u t) *
        thirdFullThreeBandZ3GalerkinWienerDerivative244 r s (u t) := by
    simpa only [Q, thirdFullThreeBandZ3GalerkinWienerMass244,
      thirdFullThreeBandZ3GalerkinWienerDerivative244] using
      (thirdFullThreeBand_z3GalerkinAllOutputWienerBound244
        r hRadius s s s (u t) (u t))
  have hMassDom := thirdFullThreeBand_z3WienerMass_le_smooth244
    epsilon r s (u t)
  have hDerivativeDom := thirdFullThreeBand_z3WienerDerivative_le_smooth244
    epsilon r s (u t)
  have hMassNonneg : 0 ≤ thirdFullThreeBandZ3GalerkinSmoothWienerMass244
      epsilon r s (u t) := by
    unfold thirdFullThreeBandZ3GalerkinSmoothWienerMass244
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le
      (Real.sqrt_nonneg _)
  have hDerivativeNonneg : 0 ≤ thirdFullThreeBandZ3GalerkinWienerDerivative244
      r s (u t) := by
    unfold thirdFullThreeBandZ3GalerkinWienerDerivative244
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg
      (mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le
        (thirdFullThreeBand_z3Degree_nonneg244 n)) (norm_nonneg _)
  have hSource : thirdFullThreeBandZ3GalerkinWienerMass244 r s Q ≤
      thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon r s (u t) *
        thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244 epsilon r s (u t) := by
    calc
      _ ≤ thirdFullThreeBandZ3GalerkinWienerMass244 r s (u t) *
          thirdFullThreeBandZ3GalerkinWienerDerivative244 r s (u t) := hQ
      _ ≤ thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon r s (u t) *
          thirdFullThreeBandZ3GalerkinWienerDerivative244 r s (u t) :=
        mul_le_mul_of_nonneg_right hMassDom hDerivativeNonneg
      _ ≤ _ := mul_le_mul_of_nonneg_left hDerivativeDom hMassNonneg
  dsimp only [d]
  calc
    _ ≤ thirdFullThreeBandZ3GalerkinWienerMass244 r s Q -
          100 * thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244 epsilon r s (u t) := hBound
    _ ≤ thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon r s (u t) *
          thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244 epsilon r s (u t) -
          100 * thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244 epsilon r s (u t) :=
      sub_le_sub_right hSource _
    _ = _ := by ring

/-- A nonpositive actual strong derivative on the smooth 100-ball,
including when some or every retained Fourier coefficient is zero. -/
theorem thirdFullThreeBand_z3ZeroSafeMovingWiener_nonpos_on_ball244
    (mu a t epsilon : ℝ) (hmu : 0 ≤ mu) (hepsilon : 0 < epsilon)
    (s : Finset ZeroIndex244) (u : ℝ → ZeroIndex244 → ZeroBand244)
    (hRadius : 0 ≤ thirdFullThreeBandZ3GalerkinMovingRadius244 a t)
    (hODE : ∀ n ∈ s, HasDerivAt (fun z : ℝ => u z n)
      (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hBall : thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t) ≤ 100) :
    ∃ d : ℝ,
      HasDerivAt
        (fun z : ℝ =>
          thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon
            (thirdFullThreeBandZ3GalerkinMovingRadius244 a z) s (u z))
        d t ∧ d ≤ 0 := by
  obtain ⟨d, hd, hBound⟩ :=
    thirdFullThreeBand_z3ZeroSafeMovingWiener_differential244
      mu a t epsilon hmu hepsilon s u hRadius hODE
  refine ⟨d, hd, ?_⟩
  have hD := thirdFullThreeBand_z3SmoothWienerDerivative_nonneg244
    epsilon (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t)
  exact hBound.trans (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hBall) hD)

end
end PrimeTensor.FirstMonomialTriad

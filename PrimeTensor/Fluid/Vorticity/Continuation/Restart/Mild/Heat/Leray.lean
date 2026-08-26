import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild

/-!
# Small-time heat--Leray mild estimate

This file turns the analytic estimate used in the three-dimensional
Navier--Stokes mild formulation into the quantitative Picard data proved in
`Restart.Mild`.

The intended path space is a Banach space such as
`C([0, τ], H³)`.  The free heat evolution has norm at most `A`, while the
Leray-projected Duhamel bilinear term gains a square-root of time:

    ‖Bτ(x,y)‖ ≤ C √τ ‖x‖ ‖y‖.

The single scalar condition

    8 C A √τ ≤ 1

then suffices for the closed ball of radius `2 A` to be invariant and for the
mild map to contract there with constant `1/2`.

Thus after this file the local-existence analysis is reduced to the actual
operator estimates: construct the heat evolution and Leray--Duhamel operator
on the chosen H³ path space and prove the displayed bounds and bilinear
difference identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

universe u

/--
Analytic heat--Leray input at one local time window.

`free` is the heat evolution of the restart datum.  `duhamel τ` is the
Leray-projected quadratic Duhamel operator on the path space.  The constant
`A` bounds the free evolution and `C` is the time-independent bilinear
constant in the standard `√τ` estimate.
-/
structure H3HeatLerayEstimateData
    (X : Type u)
    [NormedAddCommGroup X] where
  free : X
  duhamel : ℝ → X → X → X
  A : ℝ
  C : ℝ
  A_pos : 0 < A
  C_nonneg : 0 ≤ C
  free_bound : ‖free‖ ≤ A
  duhamel_bound :
    ∀ τ : ℝ,
      0 ≤ τ →
        ∀ x y : X,
          ‖duhamel τ x y‖ ≤
            (C * Real.sqrt τ) * ‖x‖ * ‖y‖
  diagonal_sub :
    ∀ τ : ℝ,
      ∀ x y : X,
        duhamel τ x x - duhamel τ y y =
          duhamel τ (x - y) x + duhamel τ y (x - y)

namespace H3HeatLerayEstimateData

noncomputable section

variable
    {X : Type u}
    [NormedAddCommGroup X]

/-- The canonical Picard radius associated to a free bound `A`. -/
def radius
    (D : H3HeatLerayEstimateData X) : ℝ :=
  2 * D.A

/-- The effective bilinear constant on a time interval of length `τ`. -/
def effectiveK
    (D : H3HeatLerayEstimateData X)
    (τ : ℝ) : ℝ :=
  D.C * Real.sqrt τ

/-- The canonical contraction constant used in the small-time argument. -/
def halfContraction : NNReal :=
  1 / 2

@[simp]
theorem radius_eq
    (D : H3HeatLerayEstimateData X) :
    D.radius = 2 * D.A :=
  rfl

@[simp]
theorem effectiveK_eq
    (D : H3HeatLerayEstimateData X)
    (τ : ℝ) :
    D.effectiveK τ = D.C * Real.sqrt τ :=
  rfl

/-- The canonical radius is strictly positive. -/
theorem radius_pos
    (D : H3HeatLerayEstimateData X) :
    0 < D.radius := by
  unfold radius
  nlinarith [D.A_pos]

/-- The effective Duhamel constant is nonnegative for nonnegative time. -/
theorem effectiveK_nonneg
    (D : H3HeatLerayEstimateData X)
    {τ : ℝ}
    (_hτ : 0 ≤ τ) :
    0 ≤ D.effectiveK τ := by
  unfold effectiveK
  exact mul_nonneg D.C_nonneg (Real.sqrt_nonneg τ)

/-- The chosen universal contraction constant is genuinely below one. -/
theorem halfContraction_lt_one :
    halfContraction < 1 := by
  norm_num [halfContraction]

/--
The single small-time condition implies the contraction scalar inequality.
-/
theorem contraction_numeric_of_smallTime
    (D : H3HeatLerayEstimateData X)
    {τ : ℝ}
    (hτ : 0 ≤ τ)
    (hsmall : 8 * D.C * D.A * Real.sqrt τ ≤ 1) :
    2 * D.effectiveK τ * D.radius ≤
      (halfContraction : ℝ) := by
  have hsqrt : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have hhalf :
      4 * D.C * D.A * Real.sqrt τ ≤ (1 / 2 : ℝ) := by
    nlinarith
  unfold effectiveK radius halfContraction
  norm_num
  nlinarith

/--
The same small-time condition also makes the quadratic term consume at most
half of the Picard radius.
-/
theorem invariant_numeric_of_smallTime
    (D : H3HeatLerayEstimateData X)
    {τ : ℝ}
    (hτ : 0 ≤ τ)
    (hsmall : 8 * D.C * D.A * Real.sqrt τ ≤ 1) :
    D.effectiveK τ * D.radius ^ 2 ≤
      D.radius / 2 := by
  have hA0 : 0 ≤ D.A := D.A_pos.le
  have hsqrt : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have hhalf :
      4 * D.C * D.A * Real.sqrt τ ≤ (1 / 2 : ℝ) := by
    nlinarith
  have hmul :=
    mul_le_mul_of_nonneg_right hhalf hA0
  have hhalfA :
      (1 / 2 : ℝ) * D.A ≤ D.A := by
    nlinarith
  calc
    D.effectiveK τ * D.radius ^ 2
        = (4 * D.C * D.A * Real.sqrt τ) * D.A := by
          unfold effectiveK radius
          ring
    _ ≤ (1 / 2 : ℝ) * D.A := hmul
    _ ≤ D.A := hhalfA
    _ = D.radius / 2 := by
      unfold radius
      ring

/--
A heat bound and the `√τ` Leray--Duhamel estimate produce all quantitative
Picard data at once.
-/
def toMildQuadraticPicardData
    (D : H3HeatLerayEstimateData X)
    (τ : ℝ)
    (hτ : 0 ≤ τ)
    (hsmall : 8 * D.C * D.A * Real.sqrt τ ≤ 1) :
    MildQuadraticPicardData X where
  free := D.free
  duhamel := D.duhamel τ
  K := D.effectiveK τ
  radius := D.radius
  contraction := halfContraction
  K_nonneg := D.effectiveK_nonneg hτ
  radius_pos := D.radius_pos
  contraction_lt_one := halfContraction_lt_one
  free_bound := by
    calc
      ‖D.free‖ ≤ D.A := D.free_bound
      _ = D.radius / 2 := by
        unfold radius
        ring
  duhamel_bound := by
    intro x y
    exact D.duhamel_bound τ hτ x y
  diagonal_sub := by
    intro x y
    exact D.diagonal_sub τ x y
  invariant_numeric :=
    D.invariant_numeric_of_smallTime hτ hsmall
  contraction_numeric :=
    D.contraction_numeric_of_smallTime hτ hsmall

/--
Under the small-time condition, the heat--Leray estimates canonically produce
the complete invariant contracting Picard problem.
-/
def toRestartPicardProblem
    [CompleteSpace X]
    (D : H3HeatLerayEstimateData X)
    (τ : ℝ)
    (hτ : 0 ≤ τ)
    (hsmall : 8 * D.C * D.A * Real.sqrt τ ≤ 1) :
    RestartPicardProblem X :=
  (D.toMildQuadraticPicardData τ hτ hsmall).toRestartPicardProblem

/-- The selected Picard solution satisfies the heat--Leray mild equation. -/
theorem solution_satisfies_heatLeray_mild
    [CompleteSpace X]
    (D : H3HeatLerayEstimateData X)
    (τ : ℝ)
    (hτ : 0 ≤ τ)
    (hsmall : 8 * D.C * D.A * Real.sqrt τ ≤ 1) :
    D.free +
        D.duhamel τ
          (D.toRestartPicardProblem τ hτ hsmall).solution
          (D.toRestartPicardProblem τ hτ hsmall).solution
      =
    (D.toRestartPicardProblem τ hτ hsmall).solution := by
  change
    (D.toMildQuadraticPicardData τ hτ hsmall).free +
        (D.toMildQuadraticPicardData τ hτ hsmall).duhamel
          (D.toMildQuadraticPicardData τ hτ hsmall).toRestartPicardProblem.solution
          (D.toMildQuadraticPicardData τ hτ hsmall).toRestartPicardProblem.solution
      =
    (D.toMildQuadraticPicardData τ hτ hsmall).toRestartPicardProblem.solution
  exact
    (D.toMildQuadraticPicardData τ hτ hsmall).solution_satisfies_mild

/-- Picard iteration from zero converges to the heat--Leray mild solution. -/
theorem tendsto_iterate_heatLeray_solution
    [CompleteSpace X]
    (D : H3HeatLerayEstimateData X)
    (τ : ℝ)
    (hτ : 0 ≤ τ)
    (hsmall : 8 * D.C * D.A * Real.sqrt τ ≤ 1) :
    Filter.Tendsto
      (fun n : ℕ =>
        (D.toMildQuadraticPicardData τ hτ hsmall).map^[n] (0 : X))
      Filter.atTop
      (nhds (D.toRestartPicardProblem τ hτ hsmall).solution) := by
  simpa [toRestartPicardProblem] using
    (D.toMildQuadraticPicardData τ hτ hsmall).tendsto_iterate_mild_solution

end

end H3HeatLerayEstimateData

end Euclidean
end Bridge
end PrimeTensor

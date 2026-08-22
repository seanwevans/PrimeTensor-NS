import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Picard

/-!
# Quantitative mild Picard ball

This file isolates the standard quantitative core of the local Navier--Stokes
fixed-point argument.

For a Banach path space `X`, write the mild map as

    Φ(x) = a + B(x,x),

where `a` is the free heat evolution and `B` is the Duhamel bilinear term.
Instead of assuming that `Φ` preserves a complete ball and contracts there,
we derive those facts from the two estimates that the PDE analysis actually
has to prove:

    ‖B(x,y)‖ ≤ K ‖x‖ ‖y‖,

and the bilinear diagonal identity

    B(x,x) - B(y,y) = B(x-y,x) + B(y,x-y).

The remaining scalar conditions are exactly the familiar small-time
conditions `K R² ≤ R/2` and `2 K R < 1` (the latter represented through a
chosen `NNReal` contraction constant).
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

universe u

/--
Quantitative data for the mild quadratic Picard map on a Banach path space.

`free` is the free heat evolution and `duhamel` is the quadratic Duhamel
operator before restriction to the diagonal.  The two analytic obligations
are `duhamel_bound` and `diagonal_sub`; the rest is scalar bookkeeping.
-/
structure MildQuadraticPicardData
    (X : Type u)
    [NormedAddCommGroup X] where
  free : X
  duhamel : X → X → X
  K : ℝ
  radius : ℝ
  contraction : NNReal
  K_nonneg : 0 ≤ K
  radius_pos : 0 < radius
  contraction_lt_one : contraction < 1
  free_bound : ‖free‖ ≤ radius / 2
  duhamel_bound :
    ∀ x y : X,
      ‖duhamel x y‖ ≤ K * ‖x‖ * ‖y‖
  diagonal_sub :
    ∀ x y : X,
      duhamel x x - duhamel y y =
        duhamel (x - y) x + duhamel y (x - y)
  invariant_numeric :
    K * radius ^ 2 ≤ radius / 2
  contraction_numeric :
    2 * K * radius ≤ (contraction : ℝ)

namespace MildQuadraticPicardData

variable
    {X : Type u}
    [NormedAddCommGroup X]

/-- The mild fixed-point map `Φ(x) = a + B(x,x)`. -/
def map
    (D : MildQuadraticPicardData X)
    (x : X) : X :=
  D.free + D.duhamel x x

/-- The closed Picard ball centered at zero. -/
def domain
    (D : MildQuadraticPicardData X) : Set X :=
  Metric.closedBall 0 D.radius

/-- Membership in the Picard ball is exactly the expected norm bound. -/
theorem mem_domain_iff
    (D : MildQuadraticPicardData X)
    (x : X) :
    x ∈ D.domain ↔ ‖x‖ ≤ D.radius := by
  simp [domain, Metric.mem_closedBall, dist_eq_norm]

/-- The quadratic Duhamel term consumes at most half the ball radius. -/
theorem duhamel_diagonal_le_half_radius
    (D : MildQuadraticPicardData X)
    {x : X}
    (hx : x ∈ D.domain) :
    ‖D.duhamel x x‖ ≤ D.radius / 2 := by
  have hxNorm : ‖x‖ ≤ D.radius :=
    (D.mem_domain_iff x).1 hx
  calc
    ‖D.duhamel x x‖
        ≤ D.K * ‖x‖ * ‖x‖ :=
      D.duhamel_bound x x
    _ ≤ D.K * D.radius * D.radius := by
      have hKx : D.K * ‖x‖ ≤ D.K * D.radius :=
        mul_le_mul_of_nonneg_left hxNorm D.K_nonneg
      exact
        mul_le_mul
          hKx
          hxNorm
          (norm_nonneg x)
          (mul_nonneg D.K_nonneg D.radius_pos.le)
    _ = D.K * D.radius ^ 2 := by ring
    _ ≤ D.radius / 2 :=
      D.invariant_numeric

/-- The mild map preserves the closed Picard ball. -/
theorem mapsTo_domain
    (D : MildQuadraticPicardData X) :
    Set.MapsTo D.map D.domain D.domain := by
  intro x hx
  apply (D.mem_domain_iff (D.map x)).2
  calc
    ‖D.map x‖
        ≤ ‖D.free‖ + ‖D.duhamel x x‖ := by
      simpa [map] using norm_add_le D.free (D.duhamel x x)
    _ ≤ D.radius / 2 + D.radius / 2 :=
      add_le_add
        D.free_bound
        (D.duhamel_diagonal_le_half_radius hx)
    _ = D.radius := by ring

/--
On the Picard ball, the mild map has the chosen contraction constant.

The proof is the standard bilinear difference estimate.  No fixed-point
machinery is used here.
-/
theorem dist_map_le
    (D : MildQuadraticPicardData X)
    {x y : X}
    (hx : x ∈ D.domain)
    (hy : y ∈ D.domain) :
    dist (D.map x) (D.map y) ≤
      (D.contraction : ℝ) * dist x y := by
  have hxNorm : ‖x‖ ≤ D.radius :=
    (D.mem_domain_iff x).1 hx
  have hyNorm : ‖y‖ ≤ D.radius :=
    (D.mem_domain_iff y).1 hy
  have hxyNorm : 0 ≤ ‖x - y‖ :=
    norm_nonneg (x - y)
  have hCancel :
      (D.free + D.duhamel x x) -
          (D.free + D.duhamel y y) =
        D.duhamel x x - D.duhamel y y := by
    abel
  simp only [dist_eq_norm]
  change
    ‖(D.free + D.duhamel x x) -
        (D.free + D.duhamel y y)‖
      ≤ (D.contraction : ℝ) * ‖x - y‖
  rw [hCancel, D.diagonal_sub x y]
  calc
    ‖D.duhamel (x - y) x + D.duhamel y (x - y)‖
        ≤ ‖D.duhamel (x - y) x‖ +
            ‖D.duhamel y (x - y)‖ :=
      norm_add_le _ _
    _ ≤
        D.K * ‖x - y‖ * ‖x‖ +
          D.K * ‖y‖ * ‖x - y‖ :=
      add_le_add
        (D.duhamel_bound (x - y) x)
        (D.duhamel_bound y (x - y))
    _ ≤ (2 * D.K * D.radius) * ‖x - y‖ := by
      have hFirst :
          D.K * ‖x - y‖ * ‖x‖ ≤
            D.K * D.radius * ‖x - y‖ := by
        calc
          D.K * ‖x - y‖ * ‖x‖
              ≤ D.K * ‖x - y‖ * D.radius :=
            mul_le_mul_of_nonneg_left
              hxNorm
              (mul_nonneg D.K_nonneg hxyNorm)
          _ = D.K * D.radius * ‖x - y‖ := by ring
      have hSecond :
          D.K * ‖y‖ * ‖x - y‖ ≤
            D.K * D.radius * ‖x - y‖ := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hyNorm D.K_nonneg)
            hxyNorm
      calc
        D.K * ‖x - y‖ * ‖x‖ +
            D.K * ‖y‖ * ‖x - y‖
            ≤ D.K * D.radius * ‖x - y‖ +
                D.K * D.radius * ‖x - y‖ :=
          add_le_add hFirst hSecond
        _ = (2 * D.K * D.radius) * ‖x - y‖ := by ring
    _ ≤ (D.contraction : ℝ) * ‖x - y‖ := by
      exact mul_le_mul_of_nonneg_right
        D.contraction_numeric
        hxyNorm

/-- The restricted mild map is genuinely contracting. -/
theorem contracting_restrict
    (D : MildQuadraticPicardData X) :
    ContractingWith
      D.contraction
      (D.mapsTo_domain.restrict D.map D.domain D.domain) := by
  refine ⟨D.contraction_lt_one, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change
    dist (D.map x.1) (D.map y.1) ≤
      (D.contraction : ℝ) * dist x.1 y.1
  exact
    D.dist_map_le
      x.2
      y.2

/-- The closed Picard ball is complete in a Banach path space. -/
theorem domain_complete
    [CompleteSpace X]
    (D : MildQuadraticPicardData X) :
    IsComplete D.domain := by
  exact Metric.isClosed_closedBall.isComplete

/--
The quantitative mild estimates canonically produce the abstract Picard
problem used by the restart construction.
-/
def toRestartPicardProblem
    [CompleteSpace X]
    (D : MildQuadraticPicardData X) :
    RestartPicardProblem X where
  map := D.map
  domain := D.domain
  complete := D.domain_complete
  mapsTo := D.mapsTo_domain
  contraction := D.contraction
  contracting := D.contracting_restrict
  seed := 0
  seed_mem := by
    apply (D.mem_domain_iff 0).2
    simpa using D.radius_pos.le

/--
The Banach-selected point produced from the quantitative mild data satisfies
its mild equation.
-/
theorem solution_satisfies_mild
    [CompleteSpace X]
    (D : MildQuadraticPicardData X) :
    D.free +
        D.duhamel
          D.toRestartPicardProblem.solution
          D.toRestartPicardProblem.solution
      =
    D.toRestartPicardProblem.solution := by
  change
    D.map D.toRestartPicardProblem.solution =
      D.toRestartPicardProblem.solution
  exact D.toRestartPicardProblem.solution_isFixedPt

/-- Picard iteration from zero converges to the mild solution. -/
theorem tendsto_iterate_mild_solution
    [CompleteSpace X]
    (D : MildQuadraticPicardData X) :
    Filter.Tendsto
      (fun n : ℕ =>
        D.map^[n] (0 : X))
      Filter.atTop
      (nhds D.toRestartPicardProblem.solution) := by
  simpa [toRestartPicardProblem] using
    D.toRestartPicardProblem.tendsto_iterate_solution

end MildQuadraticPicardData

end Euclidean
end Bridge
end PrimeTensor

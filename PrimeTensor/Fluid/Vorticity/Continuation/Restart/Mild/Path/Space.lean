import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Leray
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Normalized finite-time H³ path space

The mild fixed-point layer in `Restart.Mild.HeatLeray` keeps one Banach space
`X` fixed while the physical lifespan parameter `τ` varies.  Using the literal
space `C([0, τ], H³)` would make the type itself depend on `τ`.

We therefore normalize the time carrier once and for all to `[0,1]` and put
physical time into the operators through

    t = τ s,    s ∈ [0,1].

For any complete normed state space `H`, the normalized path space is the space
of bounded continuous maps `[0,1] → H` with its uniform norm.  Mathlib supplies
both the normed additive-group structure and completeness.  This is exactly the
Banach path space required by the Picard construction.

The eventual H³ realization only has to instantiate the state space `H`; the
time-path topology and completeness are settled here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

universe u

/-- The fixed normalized local-time interval `[0,1]`. -/
abbrev H3UnitTime : Type :=
  Set.Icc (0 : ℝ) 1

/--
The normalized continuous H³ path space with the uniform norm.

The spatial state type is left as a parameter because the next analytic layer
will realize it as the concrete H³ state space.  Crucially, the time carrier no
longer depends on the physical lifespan `τ`.
-/
abbrev H3Path
    (H : Type u)
    [NormedAddCommGroup H] : Type u :=
  BoundedContinuousFunction H3UnitTime H

/-- The left endpoint of normalized time. -/
def h3UnitTimeZero : H3UnitTime :=
  ⟨0, by norm_num⟩

/-- The right endpoint of normalized time. -/
def h3UnitTimeOne : H3UnitTime :=
  ⟨1, by norm_num⟩

@[simp]
theorem h3UnitTimeZero_val :
    (h3UnitTimeZero : ℝ) = 0 :=
  rfl

@[simp]
theorem h3UnitTimeOne_val :
    (h3UnitTimeOne : ℝ) = 1 :=
  rfl

/-- Convert normalized time `s ∈ [0,1]` to physical time `τ s`. -/
def h3PhysicalTime
    (τ : ℝ)
    (s : H3UnitTime) : ℝ :=
  τ * (s : ℝ)

@[simp]
theorem h3PhysicalTime_zero
    (τ : ℝ) :
    h3PhysicalTime τ h3UnitTimeZero = 0 := by
  simp [h3PhysicalTime]

@[simp]
theorem h3PhysicalTime_one
    (τ : ℝ) :
    h3PhysicalTime τ h3UnitTimeOne = τ := by
  simp [h3PhysicalTime]

/-- For nonnegative lifespan, normalized time lands in the physical interval. -/
theorem h3PhysicalTime_mem_Icc
    {τ : ℝ}
    (hτ : 0 ≤ τ)
    (s : H3UnitTime) :
    h3PhysicalTime τ s ∈ Set.Icc (0 : ℝ) τ := by
  rcases s.property with ⟨hs0, hs1⟩
  constructor
  · exact mul_nonneg hτ hs0
  · calc
      h3PhysicalTime τ s
          = τ * (s : ℝ) := rfl
      _ ≤ τ * 1 :=
        mul_le_mul_of_nonneg_left hs1 hτ
      _ = τ := by ring

/-- The normalized-to-physical time map as a subtype-valued function. -/
def h3PhysicalTimeMap
    (τ : ℝ)
    (hτ : 0 ≤ τ) :
    H3UnitTime → Set.Icc (0 : ℝ) τ :=
  fun s =>
    ⟨h3PhysicalTime τ s,
      h3PhysicalTime_mem_Icc hτ s⟩

@[simp]
theorem h3PhysicalTimeMap_val
    (τ : ℝ)
    (hτ : 0 ≤ τ)
    (s : H3UnitTime) :
    ((h3PhysicalTimeMap τ hτ s : Set.Icc (0 : ℝ) τ) : ℝ) =
      h3PhysicalTime τ s :=
  rfl

/-- Pointwise state norm is bounded by the path sup norm. -/
theorem h3Path_norm_apply_le_norm
    {H : Type u}
    [NormedAddCommGroup H]
    (u : H3Path H)
    (s : H3UnitTime) :
    ‖u s‖ ≤ ‖u‖ := by
  exact
    BoundedContinuousFunction.norm_coe_le_norm
      u s

/-- A constant state defines a normalized continuous path. -/
def h3ConstantPath
    {H : Type u}
    [NormedAddCommGroup H]
    (x : H) :
    H3Path H :=
  BoundedContinuousFunction.const H3UnitTime x

@[simp]
theorem h3ConstantPath_apply
    {H : Type u}
    [NormedAddCommGroup H]
    (x : H)
    (s : H3UnitTime) :
    h3ConstantPath x s = x :=
  rfl

/-- On the nonempty unit interval, a constant path has exactly the state norm. -/
@[simp]
theorem norm_h3ConstantPath
    {H : Type u}
    [NormedAddCommGroup H]
    (x : H) :
    ‖h3ConstantPath x‖ = ‖x‖ := by
  apply le_antisymm
  · exact
      BoundedContinuousFunction.norm_const_le x
  · calc
      ‖x‖ = ‖h3ConstantPath x h3UnitTimeZero‖ := by
        rfl
      _ ≤ ‖h3ConstantPath x‖ :=
        h3Path_norm_apply_le_norm
          (h3ConstantPath x)
          h3UnitTimeZero

/--
Heat--Leray estimate data specialized to the concrete normalized path space.
-/
abbrev H3PathHeatLerayEstimateData
    (H : Type u)
    [NormedAddCommGroup H] : Type u :=
  H3HeatLerayEstimateData (H3Path H)

/-- The normalized path space is Banach whenever the spatial H³ state is. -/
theorem h3Path_complete
    {H : Type u}
    [NormedAddCommGroup H]
    [CompleteSpace H] :
    CompleteSpace (H3Path H) := by
  infer_instance

/--
The Banach-selected mild path inherits the closed-ball bound pointwise.
-/
theorem H3PathHeatLerayEstimateData.solution_pointwise_norm_le_radius
    {H : Type u}
    [NormedAddCommGroup H]
    [CompleteSpace H]
    (D : H3PathHeatLerayEstimateData H)
    (τ : ℝ)
    (hτ : 0 ≤ τ)
    (hsmall : 8 * D.C * D.A * Real.sqrt τ ≤ 1)
    (s : H3UnitTime) :
    ‖(D.toRestartPicardProblem τ hτ hsmall).solution s‖ ≤
      D.radius := by
  calc
    ‖(D.toRestartPicardProblem τ hτ hsmall).solution s‖
        ≤ ‖(D.toRestartPicardProblem τ hτ hsmall).solution‖ :=
      h3Path_norm_apply_le_norm
        (D.toRestartPicardProblem τ hτ hsmall).solution
        s
    _ ≤ D.radius := by
      have hmem :=
        (D.toRestartPicardProblem τ hτ hsmall).solution_mem
      exact
        ((D.toMildQuadraticPicardData τ hτ hsmall).mem_domain_iff
          (D.toRestartPicardProblem τ hτ hsmall).solution).1
          hmem

/-- The canonical radius is `2A`, hence every point of the mild solution is. -/
theorem H3PathHeatLerayEstimateData.solution_pointwise_norm_le_twoA
    {H : Type u}
    [NormedAddCommGroup H]
    [CompleteSpace H]
    (D : H3PathHeatLerayEstimateData H)
    (τ : ℝ)
    (hτ : 0 ≤ τ)
    (hsmall : 8 * D.C * D.A * Real.sqrt τ ≤ 1)
    (s : H3UnitTime) :
    ‖(D.toRestartPicardProblem τ hτ hsmall).solution s‖ ≤
      2 * D.A := by
  simpa [H3HeatLerayEstimateData.radius] using
    D.solution_pointwise_norm_le_radius τ hτ hsmall s

end Euclidean
end Bridge
end PrimeTensor

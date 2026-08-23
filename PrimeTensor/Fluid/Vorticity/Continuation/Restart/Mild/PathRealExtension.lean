import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.PathSpace

/-!
# Canonical real-time extension of normalized H³ paths

The mild solver uses normalized paths on

    H3UnitTime = [0,1],

while the concrete Fourier Duhamel operator is currently formulated for
real-time functions `ℝ → H`.

This file introduces the canonical bridge: clamp a real parameter into
`[0,1]` and evaluate the normalized path there.

The extension

    U♯(s) = U(clamp(s, 0, 1))

is continuous on all of `ℝ`, agrees exactly with `U` on `[0,1]`, preserves the
uniform path bound pointwise, and commutes with the additive operations needed
by the Picard subtraction identity.

No analytic estimate is introduced here; this is only path-space packaging.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open scoped Topology

noncomputable section

universe u

/-- Clamp a real parameter into the normalized local-time interval `[0,1]`. -/
def h3ClampUnitTime
    (s : ℝ) : H3UnitTime :=
  ⟨max 0 (min 1 s), by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)⟩

/-- The clamp map from real time to normalized time is continuous. -/
theorem continuous_h3ClampUnitTime :
    Continuous h3ClampUnitTime := by
  unfold h3ClampUnitTime
  fun_prop

/-- Clamping does nothing to a point already in `[0,1]`. -/
@[simp]
theorem h3ClampUnitTime_coe_of_mem_Icc
    {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ((h3ClampUnitTime s : H3UnitTime) : ℝ) = s := by
  unfold h3ClampUnitTime
  dsimp
  rw [min_eq_right hs.2, max_eq_right hs.1]

/-- Clamping the real value of a normalized time gives back that normalized time. -/
@[simp]
theorem h3ClampUnitTime_coe
    (s : H3UnitTime) :
    h3ClampUnitTime (s : ℝ) = s := by
  apply Subtype.ext
  exact h3ClampUnitTime_coe_of_mem_Icc s.property

/--
Canonical continuous real-time extension of a normalized H³ path.

Outside `[0,1]` the path is held fixed at the nearest endpoint.
-/
def h3PathRealExtension
    {H : Type u}
    [NormedAddCommGroup H]
    (U : H3Path H) :
    ℝ → H :=
  fun s =>
    U (h3ClampUnitTime s)

/-- The canonical real-time extension is continuous on all of `ℝ`. -/
theorem continuous_h3PathRealExtension
    {H : Type u}
    [NormedAddCommGroup H]
    (U : H3Path H) :
    Continuous (h3PathRealExtension U) := by
  unfold h3PathRealExtension
  exact U.continuous.comp continuous_h3ClampUnitTime

/-- On normalized time, the real extension agrees exactly with the original path. -/
@[simp]
theorem h3PathRealExtension_apply_coe
    {H : Type u}
    [NormedAddCommGroup H]
    (U : H3Path H)
    (s : H3UnitTime) :
    h3PathRealExtension U (s : ℝ) = U s := by
  unfold h3PathRealExtension
  rw [h3ClampUnitTime_coe]

/-- The real extension inherits the normalized path's uniform norm bound. -/
theorem norm_h3PathRealExtension_le
    {H : Type u}
    [NormedAddCommGroup H]
    (U : H3Path H)
    (s : ℝ) :
    ‖h3PathRealExtension U s‖ ≤ ‖U‖ := by
  unfold h3PathRealExtension
  exact
    h3Path_norm_apply_le_norm
      U (h3ClampUnitTime s)

/-! ## Compatibility with additive path algebra -/

@[simp]
theorem h3PathRealExtension_zero
    {H : Type u}
    [NormedAddCommGroup H]
    (s : ℝ) :
    h3PathRealExtension
        (0 : H3Path H) s
      =
    0 := by
  rfl

@[simp]
theorem h3PathRealExtension_add
    {H : Type u}
    [NormedAddCommGroup H]
    (U V : H3Path H)
    (s : ℝ) :
    h3PathRealExtension (U + V) s
      =
    h3PathRealExtension U s +
      h3PathRealExtension V s := by
  rfl

@[simp]
theorem h3PathRealExtension_neg
    {H : Type u}
    [NormedAddCommGroup H]
    (U : H3Path H)
    (s : ℝ) :
    h3PathRealExtension (-U) s
      =
    -h3PathRealExtension U s := by
  rfl

@[simp]
theorem h3PathRealExtension_sub
    {H : Type u}
    [NormedAddCommGroup H]
    (U V : H3Path H)
    (s : ℝ) :
    h3PathRealExtension (U - V) s
      =
    h3PathRealExtension U s -
      h3PathRealExtension V s := by
  rfl

end

end Euclidean
end Bridge
end PrimeTensor

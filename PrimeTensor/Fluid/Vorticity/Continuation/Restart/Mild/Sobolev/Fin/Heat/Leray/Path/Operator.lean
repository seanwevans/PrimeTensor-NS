import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel.Path
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Path.Real.Extension

/-!
# Concrete path-to-path heat--Leray Duhamel operator

The physical Duhamel machinery consumes real-time paths, while the Picard layer
uses normalized bounded continuous paths on `[0,1]`.

For a normalized path `U`, define its physical-time extension by

    q ↦ U_clamp(q / τ).

The clamp extension is already globally continuous and norm controlled.  Since
division by a constant is continuous in `ℝ` (including `τ = 0` under Lean's
field semantics), this gives a globally continuous real-time path for every
real `τ`.

Feeding these rescaled extensions into the normalized Duhamel-path constructor
produces the actual nonlinear operator

    H3SpectralVelocityPath → H3SpectralVelocityPath
      → H3SpectralVelocityPath

for each `τ ≥ 0`, with the expected `sqrt τ` norm bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-! ## Physical-time extension of a normalized path -/

/--
Extend a normalized path to all real physical times by clamping after rescaling
physical time back to normalized time.
-/
def h3PathPhysicalRealExtension
    {H : Type u}
    [NormedAddCommGroup H]
    (τ : ℝ)
    (U : H3Path H) :
    ℝ → H :=
  fun q =>
    h3PathRealExtension U (q / τ)

/--
The physical-time extension is globally continuous.
-/
theorem continuous_h3PathPhysicalRealExtension
    {H : Type u}
    [NormedAddCommGroup H]
    (τ : ℝ)
    (U : H3Path H) :
    Continuous (h3PathPhysicalRealExtension τ U) := by
  unfold h3PathPhysicalRealExtension
  exact
    (continuous_h3PathRealExtension U).comp
      (continuous_id.div_const τ)

/--
The physical-time extension inherits the normalized path's uniform norm bound.
-/
theorem norm_h3PathPhysicalRealExtension_le
    {H : Type u}
    [NormedAddCommGroup H]
    (τ : ℝ)
    (U : H3Path H)
    (q : ℝ) :
    ‖h3PathPhysicalRealExtension τ U q‖ ≤ ‖U‖ := by
  unfold h3PathPhysicalRealExtension
  exact
    norm_h3PathRealExtension_le U (q / τ)

/-! ## Concrete normalized nonlinear path operator -/

/--
The heat--Leray Duhamel operator on actual normalized spectral H³ velocity
paths.

The input paths are rescaled to physical time, passed through the physical
Duhamel integral, then restricted back to normalized target time `τ s`.
-/
noncomputable def h3SpectralFinHeatLerayDuhamelPathOperator
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U V : H3SpectralVelocityPath) :
    H3SpectralVelocityPath :=
  h3SpectralFinHeatLerayDuhamelPath
    hν
    hτ
    (norm_nonneg U)
    (norm_nonneg V)
    (h3PathPhysicalRealExtension τ U)
    (h3PathPhysicalRealExtension τ V)
    (continuous_h3PathPhysicalRealExtension τ U)
    (continuous_h3PathPhysicalRealExtension τ V)
    (fun q =>
      norm_h3PathPhysicalRealExtension_le τ U q)
    (fun q =>
      norm_h3PathPhysicalRealExtension_le τ V q)

@[simp]
theorem h3SpectralFinHeatLerayDuhamelPathOperator_apply
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U V : H3SpectralVelocityPath)
    (s : H3UnitTime) :
    h3SpectralFinHeatLerayDuhamelPathOperator
        hν hτ U V s
      =
    h3SpectralFinHeatLerayDuhamel
      ν
      (h3PhysicalTimeNN τ hτ s : ℝ)
      hν
      (h3PathPhysicalRealExtension τ U)
      (h3PathPhysicalRealExtension τ V) :=
  rfl

/--
The concrete path-to-path nonlinear operator has the expected square-root
lifespan gain.
-/
theorem norm_h3SpectralFinHeatLerayDuhamelPathOperator_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U V : H3SpectralVelocityPath) :
    ‖h3SpectralFinHeatLerayDuhamelPathOperator
        hν hτ U V‖
      ≤
    h3HeatLerayDuhamelPathCoefficient ν *
      Real.sqrt τ * ‖U‖ * ‖V‖ := by
  exact
    norm_h3SpectralFinHeatLerayDuhamelPath_le
      hν
      hτ
      (norm_nonneg U)
      (norm_nonneg V)
      (h3PathPhysicalRealExtension τ U)
      (h3PathPhysicalRealExtension τ V)
      (continuous_h3PathPhysicalRealExtension τ U)
      (continuous_h3PathPhysicalRealExtension τ V)
      (fun q =>
        norm_h3PathPhysicalRealExtension_le τ U q)
      (fun q =>
        norm_h3PathPhysicalRealExtension_le τ V q)

end

end Euclidean
end Bridge
end PrimeTensor

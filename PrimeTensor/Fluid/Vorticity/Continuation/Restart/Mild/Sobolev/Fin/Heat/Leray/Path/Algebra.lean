import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Path.Operator
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Bilinear

/-!
# Picard algebra for the concrete finite heat--Leray path operator

The previous rung constructed the genuine normalized path-to-path Duhamel
operator and proved its `sqrt τ` norm estimate.  The abstract Picard package
also requires the exact diagonal subtraction identity

    B(U,U) - B(V,V)
      = B(U-V,U) + B(V,U-V).

At the physical-time level this identity is already proved for the Bochner
Duhamel integral under four interval-integrability hypotheses.  Here those
hypotheses are discharged from the global continuity and uniform bounds of the
canonical physical-time extensions of normalized paths.

No new analytic estimate is introduced in this file.  This is the algebraic
closure needed to feed the concrete operator into `H3HeatLerayEstimateData`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

universe u

noncomputable section

/-! ## Physical-time extension and path subtraction -/

/--
Physical-time extension commutes pointwise with subtraction of normalized
paths.
-/
@[simp]
theorem h3PathPhysicalRealExtension_sub
    {H : Type u}
    [NormedAddCommGroup H]
    (τ : ℝ)
    (U V : H3Path H)
    (q : ℝ) :
    h3PathPhysicalRealExtension τ (U - V) q
      =
    h3PathPhysicalRealExtension τ U q -
      h3PathPhysicalRealExtension τ V q := by
  rfl

/-! ## Exact diagonal subtraction on normalized paths -/

/--
The actual normalized finite heat--Leray Duhamel path operator satisfies the
Picard diagonal subtraction identity.
-/
theorem h3SpectralFinHeatLerayDuhamelPathOperator_diagonal_sub
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U V : H3SpectralVelocityPath) :
    h3SpectralFinHeatLerayDuhamelPathOperator
        hν hτ U U
      -
    h3SpectralFinHeatLerayDuhamelPathOperator
        hν hτ V V
      =
    h3SpectralFinHeatLerayDuhamelPathOperator
        hν hτ (U - V) U
      +
    h3SpectralFinHeatLerayDuhamelPathOperator
        hν hτ V (U - V) := by
  apply BoundedContinuousFunction.ext
  intro s

  let t : ℝ :=
    (h3PhysicalTimeNN τ hτ s : ℝ)

  let X : ℝ → H3SpectralFinVectorState :=
    h3PathPhysicalRealExtension τ U

  let Y : ℝ → H3SpectralFinVectorState :=
    h3PathPhysicalRealExtension τ V

  let Z : ℝ → H3SpectralFinVectorState :=
    h3PathPhysicalRealExtension τ (U - V)

  have ht : 0 ≤ t := by
    dsimp [t]
    exact (h3PhysicalTimeNN τ hτ s).property

  have hXcont : Continuous X := by
    dsimp [X]
    exact continuous_h3PathPhysicalRealExtension τ U

  have hYcont : Continuous Y := by
    dsimp [Y]
    exact continuous_h3PathPhysicalRealExtension τ V

  have hZcont : Continuous Z := by
    dsimp [Z]
    exact continuous_h3PathPhysicalRealExtension τ (U - V)

  have hX :
      ∀ q ∈ Set.Ioc (0 : ℝ) t,
        ‖X q‖ ≤ ‖U‖ := by
    intro q _hq
    dsimp [X]
    exact norm_h3PathPhysicalRealExtension_le τ U q

  have hY :
      ∀ q ∈ Set.Ioc (0 : ℝ) t,
        ‖Y q‖ ≤ ‖V‖ := by
    intro q _hq
    dsimp [Y]
    exact norm_h3PathPhysicalRealExtension_le τ V q

  have hZ :
      ∀ q ∈ Set.Ioc (0 : ℝ) t,
        ‖Z q‖ ≤ ‖U - V‖ := by
    intro q _hq
    dsimp [Z]
    exact norm_h3PathPhysicalRealExtension_le τ (U - V) q

  have hXY : X - Y = Z := by
    funext q
    dsimp [X, Y, Z]
    rfl

  have hXX :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν X X)
        volume 0 t := by
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν ht
        (norm_nonneg U)
        (norm_nonneg U)
        X X
        hXcont hXcont
        hX hX

  have hYY :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν Y Y)
        volume 0 t := by
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν ht
        (norm_nonneg V)
        (norm_nonneg V)
        Y Y
        hYcont hYcont
        hY hY

  have hZX :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν Z X)
        volume 0 t := by
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν ht
        (norm_nonneg (U - V))
        (norm_nonneg U)
        Z X
        hZcont hXcont
        hZ hX

  have hYZ :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν Y Z)
        volume 0 t := by
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν ht
        (norm_nonneg V)
        (norm_nonneg (U - V))
        Y Z
        hYcont hZcont
        hY hZ

  have hDX :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν (X - Y) X)
        volume 0 t := by
    rw [hXY]
    exact hZX

  have hYD :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν Y (X - Y))
        volume 0 t := by
    rw [hXY]
    exact hYZ

  have hDiag :=
    h3SpectralFinHeatLerayDuhamel_diagonal_sub
      hν X Y hXX hYY hDX hYD

  rw [hXY] at hDiag

  change
    h3SpectralFinHeatLerayDuhamel
        ν t hν X X
      -
    h3SpectralFinHeatLerayDuhamel
        ν t hν Y Y
      =
    h3SpectralFinHeatLerayDuhamel
        ν t hν Z X
      +
    h3SpectralFinHeatLerayDuhamel
        ν t hν Y Z

  exact hDiag

end

end Euclidean
end Bridge
end PrimeTensor

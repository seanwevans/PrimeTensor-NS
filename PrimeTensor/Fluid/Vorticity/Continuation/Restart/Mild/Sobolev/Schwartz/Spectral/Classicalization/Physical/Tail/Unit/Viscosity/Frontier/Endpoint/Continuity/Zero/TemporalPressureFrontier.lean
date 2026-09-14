import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalProjectedRHSMass

/-!
# Zeroth-order endpoint continuity: reduce temporal Fubini to pressure-defect mass

The endpoint-independent branch has now completely closed the projected-RHS
part of the old temporal mass estimate.

For every compact smooth scalar test `ψ`,

    M_projectedRHS(q,i,ψ)
      ≤
    ‖ψ‖₂ · K(E),

up to the harmless square/root normalization already used by the project,
uniformly in the elapsed slice.

Together with `TemporalPressureMass`,

    M_temporal
      ≤
    M_projectedRHS + M_pressureDefect,

this leaves one and only one quantitative obstruction in the coordinatewise
Fubini route:

    a uniform compact-test spatial mass bound for
    ∂ᵢ p_old - ∂ᵢ p_can.

This file states that pressure-defect mass frontier explicitly and proves:

    pressure-defect mass bound
      -> old temporal mass envelope
      -> old temporal product integrability.

No pressure uniqueness, decay, harmonic Liouville theorem, or endpoint
continuity is silently assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroPressureDefectMassFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroPressureDefectMassFrontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Uniform compact-test mass control for the old-vs-canonical pressure-gradient
defect over one closed elapsed interval. -/
def H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector) : Prop :=
  ∃ C : ℝ,
    ∀ (i : Fin 3) (q : Set.Icc (0 : ℝ) tau),
      h3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassOnElapsed
          hNS ht hEnd hTail q i (φ i)
        ≤
      C

/-- Finite-coordinate aggregate of the already-closed projected-RHS compact
test mass ceilings. -/
noncomputable def h3UnitViscosityZeroProjectedRHSWeakTestMassBound
    (E : ℝ)
    (φ : H3WeakTestVector) :
    ℝ :=
  ∑ i : Fin 3,
    h3WeakTestFunctionL2Mass (φ i)
      *
    ((h3UnitViscosityZeroRHSBound E) ^ 2) ^
      (1 / (2 : ℝ))

theorem h3UnitViscosityZeroProjectedRHSWeakTestMassBound_nonneg
    (E : ℝ)
    (φ : H3WeakTestVector) :
    0 ≤
      h3UnitViscosityZeroProjectedRHSWeakTestMassBound E φ := by
  unfold h3UnitViscosityZeroProjectedRHSWeakTestMassBound

  exact
    Finset.sum_nonneg
      (fun i hi => by
        exact
          mul_nonneg
            (h3WeakTestFunctionL2Mass_nonneg (φ i))
            (by positivity))

/-- Each coordinate projected-RHS mass is bounded by the finite-coordinate
aggregate ceiling. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSSpatialNormMassOnElapsed_le_aggregate
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3PreterminalTailCanonicalZeroProjectedRHSSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i (φ i)
      ≤
    h3UnitViscosityZeroProjectedRHSWeakTestMassBound E φ := by
  have hCoord :=
    h3PreterminalTailCanonicalZeroProjectedRHSSpatialNormMassOnElapsed_le
      hNS ht hEnd hE hTail q i (φ i)

  have hSingle :
      h3WeakTestFunctionL2Mass (φ i)
          *
        ((h3UnitViscosityZeroRHSBound E) ^ 2) ^
          (1 / (2 : ℝ))
        ≤
      ∑ j : Fin 3,
        h3WeakTestFunctionL2Mass (φ j)
          *
        ((h3UnitViscosityZeroRHSBound E) ^ 2) ^
          (1 / (2 : ℝ)) := by
    exact
      Finset.single_le_sum
        (fun j _ =>
          mul_nonneg
            (h3WeakTestFunctionL2Mass_nonneg (φ j))
            (by positivity))
        (Finset.mem_univ i)

  exact
    hCoord.trans
      (by
        simpa only [
          h3UnitViscosityZeroProjectedRHSWeakTestMassBound
        ] using hSingle)

/-- A uniform pressure-defect mass bound closes the complete old temporal
spatial norm-mass envelope. -/
theorem H3PreterminalLoggedVelocityTemporalSpatialNormMassUniformlyBoundedOnElapsed_of_pressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hPressure :
      H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail φ) :
    H3PreterminalLoggedVelocityTemporalSpatialNormMassUniformlyBoundedOnElapsed
      hNS t tau φ := by
  rcases hPressure with ⟨C, hC⟩

  refine
    ⟨
      h3UnitViscosityZeroProjectedRHSWeakTestMassBound E φ + C,
      ?_
    ⟩

  intro i r hr

  let q : Set.Icc (0 : ℝ) tau :=
    ⟨r, hr.1.le, hr.2.le⟩

  have hSplit :=
    h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed_le_projectedRHS_add_pressureDefect
      hNS ht hEnd hTail q i (φ i)

  have hProjected :=
    h3PreterminalTailCanonicalZeroProjectedRHSSpatialNormMassOnElapsed_le_aggregate
      hNS ht hEnd hE hTail φ q i

  have hDefect := hC i q

  dsimp only [q] at hSplit hProjected hDefect

  exact
    hSplit.trans
      (add_le_add hProjected hDefect)

/-- Consequently, the pressure-defect mass frontier alone is enough to close
the product-space integrability needed by the old pointwise temporal FTC. -/
theorem H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_pressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hq0 : 0 ≤ q)
    (hqtau : q ≤ tau)
    (hPressure :
      H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail φ) :
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo
      hNS t q φ := by
  apply
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_uniformBound
      hNS φ hq0 hqtau

  exact
    H3PreterminalLoggedVelocityTemporalSpatialNormMassUniformlyBoundedOnElapsed_of_pressureDefect
      hNS ht hEnd hE hTail φ hPressure

end

end Euclidean
end Bridge
end PrimeTensor

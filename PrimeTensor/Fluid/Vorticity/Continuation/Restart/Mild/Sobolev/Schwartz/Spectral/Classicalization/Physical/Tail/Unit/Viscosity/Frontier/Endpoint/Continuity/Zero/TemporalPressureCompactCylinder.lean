import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureWitness
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Forcing.Pairing.Continuity

/-!
# Zeroth endpoint continuity: reduce pressure mass to a compact-cylinder bound

`TemporalPressureWitness` removed the arbitrary pressure-choice issue: the old
preterminal pressure gradient can be computed using the specific pressure
witness already carried by the canonical H³ energy package.

The remaining hypothesis is still phrased as a uniform spatial `L¹` mass.
For compact weak tests, that is stronger-looking than the actual local
regularity needed.

This file reduces it to the natural compact-cylinder estimate.  For one fixed
weak-test vector `φ`, assume there is a constant `B` such that, uniformly in

* coordinate `i`,
* elapsed time `q ∈ [0,τ]`,
* spatial point `x`,

the pressure-gradient factor obeys

    ‖φ_i(x) ∂_i p(t+q,x)‖
      ≤ B ‖φ_i(x)‖.

Because each `φ_i` has compact support and finite `L¹` mass, integration gives

    ∫ ‖φ_i ∂_i p‖
      ≤ B ∫ ‖φ_i‖.

A single finite-coordinate sum of the three fixed test masses then supplies the
common constant required by the old-pressure frontier.

This is the exact form that joint continuity / local boundedness of the energy
pressure gradient on compact spacetime cylinders would discharge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3ZeroPressureCompactCylinder
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroPressureCompactCylinder :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact test-local pointwise bound needed on one closed elapsed cylinder.

The factor `‖φ_i(x)‖` makes this only a bound where the compact test is active;
no global spatial boundedness of the pressure gradient is asserted. -/
def H3PressureWitnessGradientCompactCylinderBoundOnElapsed
    {t tau : ℝ}
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (φ : H3WeakTestVector) : Prop :=
  ∃ B : ℝ,
    0 ≤ B
      ∧
    ∀
      (i : Fin 3)
      (q : Set.Icc (0 : ℝ) tau)
      (x : Point3),
        ‖(ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (p (t + (q : ℝ)))
              x)‖
          ≤
        B * ‖φ i x‖

/-- Any valid preterminal pressure witness has an integrable compact-test
gradient product at every elapsed slice. -/
theorem h3WeakTest_mul_pressureWitnessGradient_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p T)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d
            (h3AxisOfFin3 i)
            (p (t + (q : ℝ)))
            x))
      (volume : Measure Point3) := by
  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hC2 :
      SpatialC2
        (p (t + (q : ℝ))) :=
    hPDE.regularity.pressure_spatial_two
      (t + (q : ℝ)) hAbs

  have hC1 :
      SpatialC1
        (p (t + (q : ℝ))) :=
    hC2.of_le (by norm_num)

  have hD :
      Continuous
        (spatial3.d
          (h3AxisOfFin3 i)
          (p (t + (q : ℝ)))) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hC1
      (h3AxisOfFin3 i)

  exact
    ψ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hD.locallyIntegrable.locallyIntegrableOn Set.univ)

/-- Fixed `L¹` mass of a weak test is nonnegative. -/
theorem h3WeakTestFunctionL1Mass_nonneg_pressureCompactCylinder
    (ψ : H3WeakTestFunction) :
    0 ≤ h3WeakTestFunctionL1Mass ψ := by
  unfold h3WeakTestFunctionL1Mass
  exact
    integral_nonneg
      (fun x : Point3 => norm_nonneg (ψ x))

/-- The compact-cylinder pointwise bound implies the uniform spatial mass
predicate for one pressure witness and one weak-test vector. -/
theorem H3PressureWitnessGradientSpatialNormMassUniformlyBoundedOnElapsed_of_compactCylinder
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p T)
    (φ : H3WeakTestVector)
    (hCylinder :
      H3PressureWitnessGradientCompactCylinderBoundOnElapsed
        (t := t) (tau := tau) p φ) :
    H3PressureWitnessGradientSpatialNormMassUniformlyBoundedOnElapsed
      (t := t) (tau := tau) p φ := by
  rcases hCylinder with
    ⟨B, hB, hPoint⟩

  let L : ℝ :=
    ∑ j : Fin 3,
      h3WeakTestFunctionL1Mass (φ j)

  refine
    ⟨B * L, ?_⟩

  intro i q

  have hLeftInt :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (p (t + (q : ℝ)))
              x))
        (volume : Measure Point3) :=
    h3WeakTest_mul_pressureWitnessGradient_integrable
      hNS ht hEnd p hPDE q i (φ i)

  have hNormTest :
      Integrable
        (fun x : Point3 =>
          ‖φ i x‖)
        (volume : Measure Point3) :=
    (h3WeakTestFunction_integrable (φ i)).norm

  have hMajor :
      Integrable
        (fun x : Point3 =>
          B * ‖φ i x‖)
        (volume : Measure Point3) :=
    hNormTest.const_mul B

  have hMass :
      h3PressureWitnessGradientSpatialNormMassOnElapsed
          (t := t) p q i (φ i)
        ≤
      B * h3WeakTestFunctionL1Mass (φ i) := by
    unfold h3PressureWitnessGradientSpatialNormMassOnElapsed

    calc
      (∫ x : Point3,
        ‖(ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d
            (h3AxisOfFin3 i)
            (p (t + (q : ℝ)))
            x)‖
        ∂volume)
          ≤
        ∫ x : Point3,
          B * ‖φ i x‖
          ∂volume := by
            exact
              integral_mono_ae
                hLeftInt.norm
                hMajor
                (Filter.Eventually.of_forall
                  (fun x => hPoint i q x))
      _ =
        B * h3WeakTestFunctionL1Mass (φ i) := by
          unfold h3WeakTestFunctionL1Mass
          rw [integral_const_mul]

  have hSingle :
      h3WeakTestFunctionL1Mass (φ i)
        ≤
      L := by
    dsimp only [L]

    exact
      Finset.single_le_sum
        (fun j hj =>
          h3WeakTestFunctionL1Mass_nonneg_pressureCompactCylinder
            (φ j))
        (Finset.mem_univ i)

  exact
    hMass.trans
      (mul_le_mul_of_nonneg_left
        hSingle hB)

/-- The compact-cylinder bound for any pressure witness closes the existing
all-divergence-free old-pressure mass condition on the same elapsed interval. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed_of_compactCylinder
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p T)
    (hCylinder :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        H3PressureWitnessGradientCompactCylinderBoundOnElapsed
          (t := t) (tau := tau) p φ) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail := by
  intro φ hφ

  apply
    H3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassUniformlyBoundedOnElapsed_of_pressureWitness
      hNS ht hEnd hTail
      p hPDE φ

  exact
    H3PressureWitnessGradientSpatialNormMassUniformlyBoundedOnElapsed_of_compactCylinder
      hNS ht hEnd hTail
      p hPDE φ
      (hCylinder φ hφ)

/-- Compact-cylinder regularity for the specific analytic pressure carried by
canonical H³ energy data. -/
def H3CanonicalH3EnergyAnalyticPressureCompactCylinderBoundOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t T tau : ℝ}
    (hData : CanonicalH3EnergyDataOnTail u t T) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    H3PressureWitnessGradientCompactCylinderBoundOnElapsed
      (t := t) (tau := tau)
      (h3CanonicalH3EnergyAnalyticPressure hData)
      φ

/-- The energy-pressure compact-cylinder estimate is sufficient for the old
pressure mass frontier on the same elapsed interval. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed_of_canonicalEnergyCompactCylinder
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hData : CanonicalH3EnergyDataOnTail u t T)
    (hCylinder :
      H3CanonicalH3EnergyAnalyticPressureCompactCylinderBoundOnElapsed
        (tau := tau) hData) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail := by
  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed_of_compactCylinder
      hNS ht hEnd hTail
      (h3CanonicalH3EnergyAnalyticPressure hData)
      (h3CanonicalH3EnergyAnalyticPressure_preterminalNavierStokes3 hData)
      hCylinder

end

end Euclidean
end Bridge
end PrimeTensor

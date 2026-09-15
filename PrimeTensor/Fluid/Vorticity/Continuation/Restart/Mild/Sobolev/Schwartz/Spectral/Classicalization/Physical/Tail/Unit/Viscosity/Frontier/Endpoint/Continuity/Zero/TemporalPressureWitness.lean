import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureOldFrontier
import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure

/-!
# Zeroth endpoint continuity: pressure-witness independence

The remaining zeroth-order continuation obstruction was phrased using

    Classical.choose hNS

as the old preterminal pressure.  That choice is mathematically inessential.

If two pressures satisfy `PreterminalNavierStokes3` for the same velocity on
the same interval, their pressure-force components are equal by subtracting
the two momentum equations.  Since

    pressureForceComponent = -∂ᵢ p,

their spatial gradients agree pointwise on `(0,T)`.

Consequently every compact-test old-pressure gradient mass is exactly
independent of the pressure witness.

This file packages that fact and then specializes it to the pressure witness
already carried by `CanonicalH3EnergyDataOnTail`.  The remaining pressure
frontier is therefore no longer about an arbitrary existential choice: it is
the uniform compact-test mass of the high-order energy pressure itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3ZeroPressureWitness
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroPressureWitness :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Pressure gradients are uniquely determined by a fixed preterminal velocity,
even though the pressure itself is only determined up to a spatial constant. -/
theorem preterminalNavierStokes3_pressureGradient_eq
    {v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three}
    {p₁ p₂ : SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {T s : ℝ}
    (h₁ : PreterminalNavierStokes3 v p₁ T)
    (h₂ : PreterminalNavierStokes3 v p₂ T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    spatial3.d j (p₁ s) x
      =
    spatial3.d j (p₂ s) x := by
  have hm₁ :=
    h₁.momentum s hs x j
  have hm₂ :=
    h₂.momentum s hs x j

  unfold PrimeTensor.Bridge.RealFluid.pressureForceComponent at hm₁ hm₂

  linarith

/-- The pressure selected by `LoggedPreterminalNavierStokesAdmissible` has the
same spatial gradient as every other pressure witness for the same logged
velocity. -/
theorem h3LoggedPreterminal_oldPressureGradient_eq_pressureWitness
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (i : Fin 3) :
    spatial3.d
        (h3AxisOfFin3 i)
        ((Classical.choose hNS) s)
        x
      =
    spatial3.d
        (h3AxisOfFin3 i)
        (p s)
        x := by
  exact
    preterminalNavierStokes3_pressureGradient_eq
      (Classical.choose_spec hNS)
      hPDE
      hs
      x
      (h3AxisOfFin3 i)

/-- Compact-test spatial `L¹` mass of the gradient of an arbitrary pressure
witness. -/
noncomputable def h3PressureWitnessGradientSpatialNormMassOnElapsed
    {t tau : ℝ}
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    ℝ :=
  ∫ x : Point3,
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (spatial3.d
        (h3AxisOfFin3 i)
        (p (t + (q : ℝ)))
        x)‖
    ∂volume

/-- The old-pressure compact-test mass is exactly the same mass computed from
any other pressure witness for the same preterminal velocity. -/
theorem h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed_eq_pressureWitness
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
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i ψ
      =
    h3PressureWitnessGradientSpatialNormMassOnElapsed
      (t := t) p q i ψ := by
  unfold
    h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed
    h3PressureWitnessGradientSpatialNormMassOnElapsed

  apply integral_congr_ae

  filter_upwards with x

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  rw [
    h3LoggedPreterminal_oldPressureGradient_eq_pressureWitness
      hNS p hPDE hAbs x i
  ]

/-- Uniform compact-test mass for an arbitrary preterminal pressure witness. -/
def H3PressureWitnessGradientSpatialNormMassUniformlyBoundedOnElapsed
    {t tau : ℝ}
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (φ : H3WeakTestVector) : Prop :=
  ∃ C : ℝ,
    ∀ (i : Fin 3) (q : Set.Icc (0 : ℝ) tau),
      h3PressureWitnessGradientSpatialNormMassOnElapsed
          (t := t) p q i (φ i)
        ≤
      C

/-- Uniform compact-test mass for any valid pressure witness transfers exactly
to the existing old-pressure mass predicate. -/
theorem H3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassUniformlyBoundedOnElapsed_of_pressureWitness
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
    (hMass :
      H3PressureWitnessGradientSpatialNormMassUniformlyBoundedOnElapsed
        (t := t) (tau := tau) p φ) :
    H3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail φ := by
  rcases hMass with ⟨C, hC⟩

  refine ⟨C, ?_⟩
  intro i q

  rw [
    h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed_eq_pressureWitness
      hNS ht hEnd hTail p hPDE q i (φ i)
  ]

  exact hC i q

/-- All divergence-free compact tests may therefore be controlled using any
pressure witness for the same velocity. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed_of_pressureWitness
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
    (hMass :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        H3PressureWitnessGradientSpatialNormMassUniformlyBoundedOnElapsed
          (t := t) (tau := tau) p φ) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail := by
  intro φ hφ

  exact
    H3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassUniformlyBoundedOnElapsed_of_pressureWitness
      hNS ht hEnd hTail p hPDE φ
      (hMass φ hφ)

/-- Canonical high-order energy data already carries a specific preterminal
pressure witness through `H3EnergyEstimateAnalyticOnTail`. -/
noncomputable def h3CanonicalH3EnergyAnalyticPressure
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t T : ℝ}
    (hData : CanonicalH3EnergyDataOnTail u t T) :
    SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
  Classical.choose hData.2.2

/-- The canonical-energy analytic pressure is a genuine preterminal pressure
witness for the same logged velocity. -/
theorem h3CanonicalH3EnergyAnalyticPressure_preterminalNavierStokes3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t T : ℝ}
    (hData : CanonicalH3EnergyDataOnTail u t T) :
    PreterminalNavierStokes3
      (logSpaceTimeVectorField u)
      (h3CanonicalH3EnergyAnalyticPressure hData)
      T := by
  exact
    (Classical.choose_spec hData.2.2).1

/-- The exact remaining pressure hypothesis after canonical H³ energy data is
available: uniform compact-test mass of the analytic pressure witness already
used by the differentiated H³ energy argument. -/
def H3CanonicalH3EnergyAnalyticPressureMassUniformlyBoundedOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t T tau : ℝ}
    (hData : CanonicalH3EnergyDataOnTail u t T) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    H3PressureWitnessGradientSpatialNormMassUniformlyBoundedOnElapsed
      (t := t) (tau := tau)
      (h3CanonicalH3EnergyAnalyticPressure hData)
      φ

/-- Uniform mass control for the canonical-energy analytic pressure closes the
old-pressure frontier on the same elapsed interval. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed_of_canonicalEnergyPressure
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hData : CanonicalH3EnergyDataOnTail u t T)
    (hMass :
      H3CanonicalH3EnergyAnalyticPressureMassUniformlyBoundedOnElapsed
        (tau := tau) hData) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail := by
  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed_of_pressureWitness
      hNS ht hEnd hTail
      (h3CanonicalH3EnergyAnalyticPressure hData)
      (h3CanonicalH3EnergyAnalyticPressure_preterminalNavierStokes3 hData)
      hMass

end

end Euclidean
end Bridge
end PrimeTensor

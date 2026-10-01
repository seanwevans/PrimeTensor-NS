import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.Integral

/-!
# Zeroth-order canonical H³ energy derivative

The reusable square-integral theorem reduces the zeroth-order energy identity
to one local dominated-convergence package for each velocity component.

At a preterminal time `t`:

* `LoggedPreterminalNavierStokesAdmissible` already gives genuine `C¹` time
  regularity of each scalar velocity component;
* `VelocityH3IntegrableAt u t` gives integrability of the base-time square;
* the only remaining local analytic data are measurability of the square and
  product derivative together with one integrable dominator for
  `2 u_j ∂ₜu_j`.

This file packages exactly that remaining datum and proves

    HasDerivAt
      (velocityH3Energy0At u)
      (velocityH3FormalDerivative0At u t)
      t.

The same square-integral engine will be reused for derivative orders one
through three.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeOrderZero
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine pointwise time derivative of one logged velocity component at every
preterminal time. -/
theorem loggedVelocityComponent_hasDerivAt_time
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    HasDerivAt
      (fun r : ℝ =>
        loggedVelocityComponent u r j x)
      (loggedVelocityTemporalComponent u s j x)
      s := by
  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  let fOld : ℝ → ℝ :=
    fun r =>
      loggedVelocityComponent u r j x

  have hC1 :
      ContDiffOn
        ℝ 1
        fOld
        (Set.Ioo (0 : ℝ) T) := by
    dsimp only [fOld]
    simpa only [loggedVelocityComponent] using
      hPDE.regularity.velocity_temporal_one x j

  have hCriterion :
      ContDiffOn
          ℝ 1
          fOld
          (Set.Ioo (0 : ℝ) T)
        ↔
      DifferentiableOn
          ℝ
          fOld
          (Set.Ioo (0 : ℝ) T)
        ∧
      ContinuousOn
          (deriv fOld)
          (Set.Ioo (0 : ℝ) T) := by
    simpa using
      (contDiffOn_succ_iff_deriv_of_isOpen
        (𝕜 := ℝ)
        (f := fOld)
        (s := Set.Ioo (0 : ℝ) T)
        (n := 0)
        isOpen_Ioo)

  have hDiffOn :
      DifferentiableOn
        ℝ
        fOld
        (Set.Ioo (0 : ℝ) T) :=
    (hCriterion.1 hC1).1

  have hDiffWithin :
      DifferentiableWithinAt
        ℝ
        fOld
        (Set.Ioo (0 : ℝ) T)
        s :=
    hDiffOn s hs

  have hDiff :
      DifferentiableAt ℝ fOld s :=
    hDiffWithin.differentiableAt
      (isOpen_Ioo.mem_nhds hs)

  have hRaw :
      HasDerivAt
        fOld
        (deriv fOld s)
        s :=
    hDiff.hasDerivAt

  dsimp only [fOld] at hRaw

  simpa only [
    loggedVelocityTemporalComponent,
    temporal_d,
    loggedVelocityComponent
  ] using hRaw

/-- Exact local domination data needed to differentiate every zeroth-order
square-energy integral at one preterminal time.

The pointwise derivative itself is *not* included: it follows from the
preterminal `C¹` regularity theorem above. -/
structure H3Order0EnergyDerivativeDominatedAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : Type where

  timeSet :
    PrimeTensor.Axis Depth.three → Set ℝ

  bound :
    PrimeTensor.Axis Depth.three → Point3 → ℝ

  timeSet_mem_nhds :
    ∀ j : PrimeTensor.Axis Depth.three,
      timeSet j ∈ 𝓝 t

  timeSet_preterminal :
    ∀ j : PrimeTensor.Axis Depth.three,
      timeSet j ⊆ Set.Ioo (0 : ℝ) T

  square_aestronglyMeasurable :
    ∀ j : PrimeTensor.Axis Depth.three,
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable
          (fun x : Point3 =>
            (loggedVelocityComponent u s j x) ^ 2)
          (volume : Measure Point3)

  derivative_aestronglyMeasurable :
    ∀ j : PrimeTensor.Axis Depth.three,
      AEStronglyMeasurable
        (fun x : Point3 =>
          2 *
            loggedVelocityComponent u t j x *
            loggedVelocityTemporalComponent u t j x)
        (volume : Measure Point3)

  derivative_le_bound :
    ∀ j : PrimeTensor.Axis Depth.three,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j,
          norm
            (2 *
              loggedVelocityComponent u s j x *
              loggedVelocityTemporalComponent u s j x)
            ≤
          bound j x

  bound_integrable :
    ∀ j : PrimeTensor.Axis Depth.three,
      Integrable
        (bound j)
        (volume : Measure Point3)

/-- One zeroth-order scalar square-energy term has the expected derivative. -/
theorem hasDerivAt_spatialSquareEnergy_loggedVelocityComponent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order0EnergyDerivativeDominatedAt u T t)
    (j : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun s : ℝ =>
        spatialSquareEnergy
          (loggedVelocityComponent u s j))
      (spatialEnergyPairing
        (loggedVelocityComponent u t j)
        (loggedVelocityTemporalComponent u t j))
      t := by
  have hSquareInt :
      Integrable
        (fun x : Point3 =>
          (loggedVelocityComponent u t j x) ^ 2)
        (volume : Measure Point3) := by
    have hj :
        SpatialL2SquareIntegrable
          (loggedVelocityComponent u t j) :=
      (hInt j).1

    exact hj

  have hDiff :
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ hDom.timeSet j,
          HasDerivAt
            (fun r : ℝ =>
              (loggedVelocityComponent u r j x) ^ 2)
            (2 *
              loggedVelocityComponent u s j x *
              loggedVelocityTemporalComponent u s j x)
            s := by
    filter_upwards with x
    intro s hs

    have hsPre :
        s ∈ Set.Ioo (0 : ℝ) T :=
      hDom.timeSet_preterminal j hs

    exact
      hasDerivAt_sq_two_mul
        (f := fun r =>
          loggedVelocityComponent u r j)
        (ft := fun r =>
          loggedVelocityTemporalComponent u r j)
        (s := s)
        (x := x)
        (loggedVelocityComponent_hasDerivAt_time
          hNS hsPre j x)

  exact
    hasDerivAt_spatialSquareEnergy_of_dominated
      (f := fun s =>
        loggedVelocityComponent u s j)
      (ft := fun s =>
        loggedVelocityTemporalComponent u s j)
      (t := t)
      (S := hDom.timeSet j)
      (bound := hDom.bound j)
      (hDom.timeSet_mem_nhds j)
      (hDom.square_aestronglyMeasurable j)
      hSquareInt
      (hDom.derivative_aestronglyMeasurable j)
      (hDom.derivative_le_bound j)
      (hDom.bound_integrable j)
      hDiff

/-- The complete zeroth-order canonical H³ energy block has its exact formal
time derivative. -/
theorem hasDerivAt_velocityH3Energy0At_of_dominated
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order0EnergyDerivativeDominatedAt u T t) :
    HasDerivAt
      (velocityH3Energy0At u)
      (velocityH3FormalDerivative0At u t)
      t := by
  have hEach :
      ∀ j : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun s : ℝ =>
            spatialSquareEnergy
              (loggedVelocityComponent u s j))
          (spatialEnergyPairing
            (loggedVelocityComponent u t j)
            (loggedVelocityTemporalComponent u t j))
          t := by
    intro j
    exact
      hasDerivAt_spatialSquareEnergy_loggedVelocityComponent
        hNS ht hInt hDom j

  have hSum :
      HasDerivAt
        (fun s : ℝ =>
          ∑ j : PrimeTensor.Axis Depth.three,
            spatialSquareEnergy
              (loggedVelocityComponent u s j))
        (∑ j : PrimeTensor.Axis Depth.three,
          spatialEnergyPairing
            (loggedVelocityComponent u t j)
            (loggedVelocityTemporalComponent u t j))
        t := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact hEach j

  change
    HasDerivAt
      (fun s : ℝ =>
        ∑ j : PrimeTensor.Axis Depth.three,
          spatialSquareEnergy
            (loggedVelocityComponent u s j))
      (∑ j : PrimeTensor.Axis Depth.three,
        spatialEnergyPairing
          (loggedVelocityComponent u t j)
          (loggedVelocityTemporalComponent u t j))
      t

  exact hSum

end

end Euclidean
end Bridge
end PrimeTensor

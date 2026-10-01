import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Envelope.Square.Clock.Obstruction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Vorticity.Energy.Envelope

/-!
# Canonical H³ energy physical-clock obstruction

The canonical H³-path vorticity envelope is a fixed multiple of
`sqrt (velocityH3EnergyAt u t)`.  The path's built-in scalar-energy continuity
makes this envelope measurable on every strict H³ energy-class tail.

Consequently a tail-wide bound

`(T - t) * velocityH3EnergyAt u t ≤ B`

would imply a bounded physical square clock for the canonical vorticity
envelope.  The tail-wide square-clock continuation theorem then forces smooth
continuation through `T`.

Thus on a hypothetical nonextension branch the dimensionless H³ energy clock
`(T - t) * velocityH3EnergyAt u t` is unbounded above on every H³ energy-class
tail.  This is a necessary blowup-rate condition, not a proof that a
nonextension branch exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The canonical square-root H³-energy vorticity envelope is strongly
measurable on every H³ energy-class tail. -/
theorem h3PathCanonicalVorticitySqrtEnergyEnvelope_aestronglyMeasurableOnEnergyClassTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    AEStronglyMeasurable
      (h3PathCanonicalVorticitySqrtEnergyEnvelope u)
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a T)) := by
  have hEnergyContinuous :
      ContinuousOn
        (velocityH3EnergyAt u)
        (Set.Ioo a T) := by
    intro t ht
    exact
      (hH3.energy_continuousAt t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩).continuousWithinAt

  have hSqrtContinuous :
      ContinuousOn
        (fun t : ℝ => Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo a T) := by
    intro t ht
    change
      ContinuousWithinAt
        ((fun x : ℝ => Real.sqrt x) ∘ velocityH3EnergyAt u)
        (Set.Ioo a T) t
    exact
      Real.continuous_sqrt.continuousAt.comp_continuousWithinAt
        (hEnergyContinuous t ht)

  have hEnvelopeContinuous :
      ContinuousOn
        (h3PathCanonicalVorticitySqrtEnergyEnvelope u)
        (Set.Ioo a T) := by
    unfold h3PathCanonicalVorticitySqrtEnergyEnvelope
    exact
      continuousOn_const.mul
        (continuousOn_const.mul hSqrtContinuous)

  exact
    hEnvelopeContinuous.aestronglyMeasurable measurableSet_Ioo

/-- A tail-wide physical clock bound for canonical H³ energy supplies the
bounded square clock required for the canonical vorticity envelope. -/
theorem boundedH3EnergyTailClock_implies_boundedCanonicalVorticityEnvelopeSquareClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hEnergyClock : ∃ B : ℝ,
      ∀ t : ℝ, t ∈ Set.Ioo a T →
        (T - t) * velocityH3EnergyAt u t ≤ B) :
    ∃ C : ℝ,
      ∀ t : ℝ, t ∈ Set.Ioo a T →
        (T - t) *
          (h3PathCanonicalVorticitySqrtEnergyEnvelope u t) ^ 2 ≤ C := by
  obtain ⟨B, hBound⟩ := hEnergyClock
  let K : ℝ :=
    (2 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2
  refine ⟨K * B, ?_⟩
  intro t ht
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hEq :
      (T - t) *
          (h3PathCanonicalVorticitySqrtEnergyEnvelope u t) ^ 2 =
        K * ((T - t) * velocityH3EnergyAt u t) := by
    dsimp [K, h3PathCanonicalVorticitySqrtEnergyEnvelope]
    have hRootSq :
        (Real.sqrt (velocityH3EnergyAt u t)) ^ 2 =
          velocityH3EnergyAt u t :=
      Real.sq_sqrt hE
    calc
      (T - t) *
          (2 *
            (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              Real.sqrt (velocityH3EnergyAt u t))) ^ 2 =
        (2 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
          ((T - t) * (Real.sqrt (velocityH3EnergyAt u t)) ^ 2) := by
        ring
      _ =
        (2 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
          ((T - t) * velocityH3EnergyAt u t) := by
        rw [hRootSq]
  rw [hEq]
  exact
    mul_le_mul_of_nonneg_left
      (hBound t ht)
      (sq_nonneg
        (2 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient))

/-- A bounded tail-wide physical H³ energy clock forces smooth continuation. -/
theorem h3PathExtension_of_boundedH3EnergyTailClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEnergyClock : ∃ B : ℝ,
      ∀ t : ℝ, t ∈ Set.Ioo a T →
        (T - t) * velocityH3EnergyAt u t ≤ B) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  let g : ℝ → ℝ := h3PathCanonicalVorticitySqrtEnergyEnvelope u

  have hEnvelope :
      ∀ t : ℝ, t ∈ Set.Ioo a T → VorticityEnvelope u g t := by
    intro t ht
    exact
      h3PathCanonicalVorticitySqrtEnergyEnvelope_at
        hH3 ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have hMeas :
      AEStronglyMeasurable
        g
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a T)) := by
    dsimp only [g]
    exact
      h3PathCanonicalVorticitySqrtEnergyEnvelope_aestronglyMeasurableOnEnergyClassTail
        hH3 hClass

  have hSquareClock : ∃ C : ℝ,
      ∀ t : ℝ, t ∈ Set.Ioo a T →
        (T - t) * (g t) ^ 2 ≤ C := by
    dsimp only [g]
    exact
      boundedH3EnergyTailClock_implies_boundedCanonicalVorticityEnvelopeSquareClock
        hEnergyClock

  exact
    h3PathExtension_of_boundedVorticityEnvelopeTailSquareClock
      hH3 hClass hEnvelope hMeas hSquareClock

/-- On a hypothetical nonextension branch, the physical H³ energy clock cannot
be bounded on any H³ energy-class tail. -/
theorem no_boundedH3EnergyTailClock_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ ∃ B : ℝ,
      ∀ t : ℝ, t ∈ Set.Ioo a T →
        (T - t) * velocityH3EnergyAt u t ≤ B := by
  intro hEnergyClock
  exact
    hNoExtension
      (h3PathExtension_of_boundedH3EnergyTailClock
        hH3 hClass hEnergyClock)

/-- Explicit unboundedness form of the physical H³ energy-clock obstruction. -/
theorem h3EnergyPhysicalClock_unbounded_on_tail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ B : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo a T ∧
        B < (T - t) * velocityH3EnergyAt u t := by
  intro B
  by_contra hNoPoint
  have hBound :
      ∀ t : ℝ, t ∈ Set.Ioo a T →
        (T - t) * velocityH3EnergyAt u t ≤ B := by
    intro t ht
    by_contra hNotLe
    have hLt :
        B < (T - t) * velocityH3EnergyAt u t :=
      lt_of_not_ge hNotLe
    exact hNoPoint ⟨t, ht, hLt⟩
  exact
    no_boundedH3EnergyTailClock_of_noH3PathExtension
      hH3 hNoExtension hClass ⟨B, hBound⟩

end

end Euclidean
end Bridge
end PrimeTensor

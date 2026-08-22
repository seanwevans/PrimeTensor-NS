import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.State
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Logged H³ velocity snapshots as concrete L² jet states

This file bridges the existing componentwise H³ energy at one time into the
concrete 120-coordinate `H3L2JetState` used by the mild Picard construction.

The bridge keeps measurability explicit.  `VelocityH3IntegrableAt` supplies
integrability of every squared derivative; the additional
`VelocityH3MeasurableAt` predicate supplies the `AEStronglyMeasurable`
hypotheses required by Mathlib's `MemLp` API.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3MildBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3MildBridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Fin-three to project-axis bridge -/

/-- The canonical enumeration `0 ↦ x`, `1 ↦ y`, `2 ↦ z`. -/
def h3AxisOfFin3 : Fin 3 → PrimeTensor.Axis Depth.three :=
  Fin.cases xAxis
    (Fin.cases yAxis
      (Fin.cases zAxis Fin.elim0))

@[simp] theorem h3AxisOfFin3_zero :
    h3AxisOfFin3 (0 : Fin 3) = xAxis := rfl

@[simp] theorem h3AxisOfFin3_one :
    h3AxisOfFin3 (1 : Fin 3) = yAxis := rfl

@[simp] theorem h3AxisOfFin3_two :
    h3AxisOfFin3 (2 : Fin 3) = zAxis := rfl

/-! ## Snapshot fields and measurability -/

/-- The scalar spatial field represented by one semantic H³ jet slot. -/
noncomputable def velocityH3JetFieldAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    H3JetIndex → ScalarField3
  | Sum.inl j =>
      loggedVelocityComponent u t (h3AxisOfFin3 j)
  | Sum.inr (Sum.inl ji) =>
      spatial3.d
        (h3AxisOfFin3 ji.2)
        (loggedVelocityComponent u t (h3AxisOfFin3 ji.1))
  | Sum.inr (Sum.inr (Sum.inl jik)) =>
      spatial3.d
        (h3AxisOfFin3 jik.2.1)
        (spatial3.d
          (h3AxisOfFin3 jik.2.2)
          (loggedVelocityComponent u t (h3AxisOfFin3 jik.1)))
  | Sum.inr (Sum.inr (Sum.inr jikl)) =>
      spatial3.d
        (h3AxisOfFin3 jikl.2.1)
        (spatial3.d
          (h3AxisOfFin3 jikl.2.2.1)
          (spatial3.d
            (h3AxisOfFin3 jikl.2.2.2)
            (loggedVelocityComponent u t (h3AxisOfFin3 jikl.1))))

/--
Every scalar derivative through order three is strongly measurable almost
everywhere.  This is the exact missing hypothesis needed to turn
`VelocityH3IntegrableAt` into concrete `Lp` values.
-/
def VelocityH3MeasurableAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  ∀ j : PrimeTensor.Axis Depth.three,
    let f := loggedVelocityComponent u t j
    AEStronglyMeasurable f volume
      ∧ (∀ i : PrimeTensor.Axis Depth.three,
          AEStronglyMeasurable (spatial3.d i f) volume)
      ∧ (∀ i k : PrimeTensor.Axis Depth.three,
          AEStronglyMeasurable
            (spatial3.d i (spatial3.d k f)) volume)
      ∧ (∀ i k l : PrimeTensor.Axis Depth.three,
          AEStronglyMeasurable
            (spatial3.d i (spatial3.d k (spatial3.d l f))) volume)

/-- Every semantic jet slot belongs to `L²`. -/
theorem velocityH3JetFieldAt_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (a : H3JetIndex) :
    MemLp (velocityH3JetFieldAt u t a) 2 volume := by
  cases a with
  | inl j =>
      have hjInt := hInt (h3AxisOfFin3 j)
      have hjMeas := hMeas (h3AxisOfFin3 j)
      dsimp only at hjInt hjMeas
      simpa [velocityH3JetFieldAt] using
        (memLp_two_of_spatialL2SquareIntegrable hjMeas.1 hjInt.1)
  | inr a1 =>
      cases a1 with
      | inl ji =>
          have hjInt := hInt (h3AxisOfFin3 ji.1)
          have hjMeas := hMeas (h3AxisOfFin3 ji.1)
          dsimp only at hjInt hjMeas
          simpa [velocityH3JetFieldAt] using
            (memLp_two_of_spatialL2SquareIntegrable
              (hjMeas.2.1 (h3AxisOfFin3 ji.2))
              (hjInt.2.1 (h3AxisOfFin3 ji.2)))
      | inr a2 =>
          cases a2 with
          | inl jik =>
              have hjInt := hInt (h3AxisOfFin3 jik.1)
              have hjMeas := hMeas (h3AxisOfFin3 jik.1)
              dsimp only at hjInt hjMeas
              simpa [velocityH3JetFieldAt] using
                (memLp_two_of_spatialL2SquareIntegrable
                  (hjMeas.2.2.1
                    (h3AxisOfFin3 jik.2.1)
                    (h3AxisOfFin3 jik.2.2))
                  (hjInt.2.2.1
                    (h3AxisOfFin3 jik.2.1)
                    (h3AxisOfFin3 jik.2.2)))
          | inr jikl =>
              have hjInt := hInt (h3AxisOfFin3 jikl.1)
              have hjMeas := hMeas (h3AxisOfFin3 jikl.1)
              dsimp only at hjInt hjMeas
              simpa [velocityH3JetFieldAt] using
                (memLp_two_of_spatialL2SquareIntegrable
                  (hjMeas.2.2.2
                    (h3AxisOfFin3 jikl.2.1)
                    (h3AxisOfFin3 jikl.2.2.1)
                    (h3AxisOfFin3 jikl.2.2.2))
                  (hjInt.2.2.2
                    (h3AxisOfFin3 jikl.2.1)
                    (h3AxisOfFin3 jikl.2.2.1)
                    (h3AxisOfFin3 jikl.2.2.2)))

/-- The concrete 120-coordinate `L²` jet of a logged velocity snapshot. -/
noncomputable def velocityH3L2JetAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    H3L2JetState :=
  fun a =>
    let hLp := velocityH3JetFieldAt_memLp2 hInt hMeas a
    hLp.toLp (velocityH3JetFieldAt u t a)

/-! ## Exact scalar L² energy bridge -/

/--
For a measurable square-integrable real scalar field, the squared norm of its
Mathlib `L²` class is exactly the spatial square energy used by PrimeTensor.
-/
theorem norm_toLp_sq_eq_spatialSquareEnergy
    {f : ScalarField3}
    (hLp : MemLp f 2 volume) :
    ‖hLp.toLp f‖ ^ 2 = spatialSquareEnergy f := by
  change ‖hLp.toLp f‖ ^ 2 = ∫ x : Point3, (f x) ^ 2
  rw [← real_inner_self_eq_norm_sq]
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MeasureTheory.MemLp.coeFn_toLp hLp] with x hx
  rw [hx]
  simp [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Every jet coordinate has exactly the expected PrimeTensor square energy. -/
theorem velocityH3L2JetAt_coordinate_norm_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (a : H3JetIndex) :
    ‖velocityH3L2JetAt u t hInt hMeas a‖ ^ 2
      = spatialSquareEnergy (velocityH3JetFieldAt u t a) := by
  unfold velocityH3L2JetAt
  dsimp only
  let hLp := velocityH3JetFieldAt_memLp2 hInt hMeas a
  change ‖hLp.toLp (velocityH3JetFieldAt u t a)‖ ^ 2 = _
  exact norm_toLp_sq_eq_spatialSquareEnergy hLp

/-! ## Canonical H³ energy controls the concrete jet norm -/

/-- Every concrete jet coordinate square is bounded by the canonical H³ energy. -/
theorem velocityH3L2JetAt_coordinate_norm_sq_le_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (a : H3JetIndex) :
    ‖velocityH3L2JetAt u t hInt hMeas a‖ ^ 2
      ≤ velocityH3EnergyAt u t := by
  rw [velocityH3L2JetAt_coordinate_norm_sq hInt hMeas a]
  have hBound := velocityH3BoundAt_canonical u t hInt
  unfold VelocityH3BoundAt at hBound
  cases a with
  | inl j =>
      have hj := hBound (h3AxisOfFin3 j)
      dsimp only at hj
      simpa [velocityH3JetFieldAt, spatialSquareEnergy] using hj.1.2
  | inr a1 =>
      cases a1 with
      | inl ji =>
          have hj := hBound (h3AxisOfFin3 ji.1)
          dsimp only at hj
          simpa [velocityH3JetFieldAt, spatialSquareEnergy] using
            (hj.2.1 (h3AxisOfFin3 ji.2)).2
      | inr a2 =>
          cases a2 with
          | inl jik =>
              have hj := hBound (h3AxisOfFin3 jik.1)
              dsimp only at hj
              simpa [velocityH3JetFieldAt, spatialSquareEnergy] using
                (hj.2.2.1
                  (h3AxisOfFin3 jik.2.1)
                  (h3AxisOfFin3 jik.2.2)).2
          | inr jikl =>
              have hj := hBound (h3AxisOfFin3 jikl.1)
              dsimp only at hj
              simpa [velocityH3JetFieldAt, spatialSquareEnergy] using
                (hj.2.2.2
                  (h3AxisOfFin3 jikl.2.1)
                  (h3AxisOfFin3 jikl.2.2.1)
                  (h3AxisOfFin3 jikl.2.2.2)).2

/-- The concrete jet sup norm is bounded by the square root of canonical H³ energy. -/
theorem velocityH3L2JetAt_norm_le_sqrt_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ‖velocityH3L2JetAt u t hInt hMeas‖
      ≤ Real.sqrt (velocityH3EnergyAt u t) := by
  apply
    (pi_norm_le_iff_of_nonneg
      (Real.sqrt_nonneg (velocityH3EnergyAt u t))).2
  intro a
  have hsq := velocityH3L2JetAt_coordinate_norm_sq_le_energy hInt hMeas a
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hsqrtSq : (Real.sqrt (velocityH3EnergyAt u t)) ^ 2 = velocityH3EnergyAt u t := by
    simpa using Real.sq_sqrt hE
  rw [← hsqrtSq] at hsq
  exact le_of_sq_le_sq hsq (Real.sqrt_nonneg _)

/-- Squaring the previous estimate gives the sharp energy-to-jet bound. -/
theorem velocityH3L2JetAt_norm_sq_le_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ‖velocityH3L2JetAt u t hInt hMeas‖ ^ 2
      ≤ velocityH3EnergyAt u t := by
  have hnorm := velocityH3L2JetAt_norm_le_sqrt_energy hInt hMeas
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hsqrt : 0 ≤ Real.sqrt (velocityH3EnergyAt u t) := Real.sqrt_nonneg _
  have hnorm0 : 0 ≤ ‖velocityH3L2JetAt u t hInt hMeas‖ := norm_nonneg _
  have hsqrtSq := Real.sq_sqrt hE
  nlinarith

end

end Euclidean
end Bridge
end PrimeTensor

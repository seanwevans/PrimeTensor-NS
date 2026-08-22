import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Bridge
import PrimeTensor.Fluid.Vorticity.H3.Axis.Sum

/-!
# Exact energy identity for the concrete H³ L² jet

The snapshot bridge already proves that every one of the 120 concrete `L²`
coordinates has squared norm equal to the corresponding PrimeTensor spatial
square energy.  This file closes the finite bookkeeping gap: summing those
120 coordinates gives exactly the four derivative-order pieces of the
canonical componentwise H³ energy.

The primary normalized identity is written without subtraction:

    1 + h3L2JetSquareEnergy (velocityH3L2JetAt ...) = velocityH3EnergyAt u t.

This keeps the bridge aligned with the normalized energy used by the
continuation argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open scoped BigOperators

noncomputable section

noncomputable local instance axisFintypeH3MildBridgeEnergy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Fin-three / project-axis sum transport -/

/--
Summing a scalar function over the canonical `Fin 3` enumeration is exactly
summing it over the project's three-dimensional positive axis.
-/
theorem sum_fin3_comp_h3AxisOfFin3
    (f : PrimeTensor.Axis Depth.three → ℝ) :
    (∑ i : Fin 3, f (h3AxisOfFin3 i))
      = ∑ i : PrimeTensor.Axis Depth.three, f i := by
  rw [Fin.sum_univ_three, axis_sum_three]
  simp
  ring

/-! ## Nested finite-axis sum transport -/

/-- Transport a two-axis `Fin 3` sum to the project's axis type. -/
theorem sum_fin3_comp_h3AxisOfFin3_two
    (f : PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three → ℝ) :
    (∑ j : Fin 3, ∑ i : Fin 3,
      f (h3AxisOfFin3 j) (h3AxisOfFin3 i))
      = ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three, f j i := by
  calc
    (∑ j : Fin 3, ∑ i : Fin 3,
      f (h3AxisOfFin3 j) (h3AxisOfFin3 i))
        = ∑ j : Fin 3,
            ∑ i : PrimeTensor.Axis Depth.three,
              f (h3AxisOfFin3 j) i := by
            apply Finset.sum_congr rfl
            intro j hj
            exact
              sum_fin3_comp_h3AxisOfFin3
                (fun i => f (h3AxisOfFin3 j) i)
    _ = ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three, f j i := by
        exact
          sum_fin3_comp_h3AxisOfFin3
            (fun j => ∑ i : PrimeTensor.Axis Depth.three, f j i)

/-- Transport a three-axis `Fin 3` sum to the project's axis type. -/
theorem sum_fin3_comp_h3AxisOfFin3_three
    (f : PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three → ℝ) :
    (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3,
      f (h3AxisOfFin3 j) (h3AxisOfFin3 i) (h3AxisOfFin3 k))
      = ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three, f j i k := by
  calc
    (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3,
      f (h3AxisOfFin3 j) (h3AxisOfFin3 i) (h3AxisOfFin3 k))
        = ∑ j : Fin 3,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                f (h3AxisOfFin3 j) i k := by
            apply Finset.sum_congr rfl
            intro j hj
            exact
              sum_fin3_comp_h3AxisOfFin3_two
                (fun i k => f (h3AxisOfFin3 j) i k)
    _ = ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three, f j i k := by
        exact
          sum_fin3_comp_h3AxisOfFin3
            (fun j =>
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three, f j i k)

/-- Transport a four-axis `Fin 3` sum to the project's axis type. -/
theorem sum_fin3_comp_h3AxisOfFin3_four
    (f : PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three → ℝ) :
    (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      f (h3AxisOfFin3 j) (h3AxisOfFin3 i)
        (h3AxisOfFin3 k) (h3AxisOfFin3 l))
      = ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three, f j i k l := by
  calc
    (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      f (h3AxisOfFin3 j) (h3AxisOfFin3 i)
        (h3AxisOfFin3 k) (h3AxisOfFin3 l))
        = ∑ j : Fin 3,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  f (h3AxisOfFin3 j) i k l := by
            apply Finset.sum_congr rfl
            intro j hj
            exact
              sum_fin3_comp_h3AxisOfFin3_three
                (fun i k l => f (h3AxisOfFin3 j) i k l)
    _ = ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three, f j i k l := by
        exact
          sum_fin3_comp_h3AxisOfFin3
            (fun j =>
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  ∑ l : PrimeTensor.Axis Depth.three, f j i k l)

/-! ## Exact identities at each derivative order -/

/-- The zeroth-order jet slots sum to `velocityH3Energy0At`. -/
theorem velocityH3L2JetAt_squareEnergy0_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    (∑ j : H3JetIndex0,
      ‖velocityH3L2JetAt u t hInt hMeas (Sum.inl j)‖ ^ 2)
      = velocityH3Energy0At u t := by
  simp_rw [velocityH3L2JetAt_coordinate_norm_sq hInt hMeas]
  simp only [velocityH3JetFieldAt]
  unfold velocityH3Energy0At
  exact
    sum_fin3_comp_h3AxisOfFin3
      (fun j => spatialSquareEnergy (loggedVelocityComponent u t j))

/-- The first-order jet slots sum to `velocityH3Energy1At`. -/
theorem velocityH3L2JetAt_squareEnergy1_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    (∑ ji : H3JetIndex1,
      ‖velocityH3L2JetAt u t hInt hMeas
        (Sum.inr (Sum.inl ji))‖ ^ 2)
      = velocityH3Energy1At u t := by
  simp_rw [velocityH3L2JetAt_coordinate_norm_sq hInt hMeas]
  simp_rw [Fintype.sum_prod_type]
  simp only [velocityH3JetFieldAt]
  unfold velocityH3Energy1At
  exact
    sum_fin3_comp_h3AxisOfFin3_two
      (fun j i =>
        spatialSquareEnergy
          (spatial3.d i (loggedVelocityComponent u t j)))

/-- The second-order jet slots sum to `velocityH3Energy2At`. -/
theorem velocityH3L2JetAt_squareEnergy2_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    (∑ jik : H3JetIndex2,
      ‖velocityH3L2JetAt u t hInt hMeas
        (Sum.inr (Sum.inr (Sum.inl jik)))‖ ^ 2)
      = velocityH3Energy2At u t := by
  simp_rw [velocityH3L2JetAt_coordinate_norm_sq hInt hMeas]
  simp_rw [Fintype.sum_prod_type]
  simp only [velocityH3JetFieldAt]
  unfold velocityH3Energy2At
  exact
    sum_fin3_comp_h3AxisOfFin3_three
      (fun j i k =>
        spatialSquareEnergy
          (spatial3.d i
            (spatial3.d k (loggedVelocityComponent u t j))))

/-- The third-order jet slots sum to `velocityH3Energy3At`. -/
theorem velocityH3L2JetAt_squareEnergy3_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    (∑ jikl : H3JetIndex3,
      ‖velocityH3L2JetAt u t hInt hMeas
        (Sum.inr (Sum.inr (Sum.inr jikl)))‖ ^ 2)
      = velocityH3Energy3At u t := by
  simp_rw [velocityH3L2JetAt_coordinate_norm_sq hInt hMeas]
  simp_rw [Fintype.sum_prod_type]
  simp only [velocityH3JetFieldAt]
  unfold velocityH3Energy3At
  exact
    sum_fin3_comp_h3AxisOfFin3_four
      (fun j i k l =>
        spatialSquareEnergy
          (spatial3.d i
            (spatial3.d k
              (spatial3.d l (loggedVelocityComponent u t j)))))

/-! ## Exact total energy bridge -/

/--
The unnormalized 120-coordinate jet energy is exactly the sum of the four
componentwise derivative-order energies.
-/
theorem h3L2JetSquareEnergy_velocityH3L2JetAt_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    h3L2JetSquareEnergy (velocityH3L2JetAt u t hInt hMeas)
      = velocityH3Energy0At u t
        + velocityH3Energy1At u t
        + velocityH3Energy2At u t
        + velocityH3Energy3At u t := by
  unfold h3L2JetSquareEnergy
  simp only [Fintype.sum_sum_type]
  rw [
    velocityH3L2JetAt_squareEnergy0_eq hInt hMeas,
    velocityH3L2JetAt_squareEnergy1_eq hInt hMeas,
    velocityH3L2JetAt_squareEnergy2_eq hInt hMeas,
    velocityH3L2JetAt_squareEnergy3_eq hInt hMeas
  ]
  ring

/--
Exact normalized identification of the concrete `L²` jet energy with the
canonical PrimeTensor H³ energy.
-/
theorem one_add_h3L2JetSquareEnergy_velocityH3L2JetAt_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    1 + h3L2JetSquareEnergy (velocityH3L2JetAt u t hInt hMeas)
      = velocityH3EnergyAt u t := by
  rw [h3L2JetSquareEnergy_velocityH3L2JetAt_eq hInt hMeas]
  unfold velocityH3EnergyAt
  ring

/-- Subtractive rearrangement of the normalized identity, for classical use. -/
theorem h3L2JetSquareEnergy_velocityH3L2JetAt_eq_energy_sub_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    h3L2JetSquareEnergy (velocityH3L2JetAt u t hInt hMeas)
      = velocityH3EnergyAt u t - 1 := by
  have h :=
    one_add_h3L2JetSquareEnergy_velocityH3L2JetAt_eq hInt hMeas
  linarith

end

end Euclidean
end Bridge
end PrimeTensor

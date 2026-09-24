import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Sign.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Pressure.L2.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Velocity.Jet.Four.Arbitrary.Closure
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Close the positive-order H³ pressure cancellation blocks

The remaining scalar-sign frontier after diffusion closure is pressure
cancellation.  At order zero the pressure potential itself appears, so a
whole-space integration-by-parts proof must respect the pressure gauge and
cannot simply assume `p ∈ L²`.

Orders one through three are different.  Their scalar potentials are
`∂p`, `D²p`, and `D³p`, all of which are already known to belong to physical
`L²` from the closed pressure-mass frontier.  The matching pressure fields are
the next derivatives, also in `L²`.  Together with the H³/fourth velocity
jets, Mathlib's whole-space Fréchet integration-by-parts theorem therefore
closes those three blocks directly.

This file isolates that gauge-safe result and reduces the public pressure
cancellation hypothesis to the zeroth-order block alone.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3PathPressureCancellationHigher
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathPressureCancellationHigher :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic whole-space pressure IBP from L² data -/

private theorem integrable_mul_of_memLp_two_two_h3PressureHigher
    {f g : ScalarField3}
    (hf : MemLp f 2 (volume : Measure Point3))
    (hg : MemLp g 2 (volume : Measure Point3)) :
    Integrable
      (fun x : Point3 => f x * g x)
      (volume : Measure Point3) := by
  have hMeas :
      AEStronglyMeasurable
        (fun x : Point3 => f x * g x)
        (volume : Measure Point3) :=
    hf.1.mul hg.1

  rw [← MeasureTheory.integrable_norm_iff hMeas]

  have hAbs :
      Integrable
        (fun x : Point3 => ‖f x‖ * ‖g x‖)
        (volume : Measure Point3) :=
    MemLp.integrable_mul hf.norm hg.norm

  simpa only [Real.norm_eq_abs, abs_mul] using hAbs

/--
Whole-space pressure integration by parts when both the scalar potential and
its gradient are represented by physical `L²` fields.
-/
private theorem pressurePairingIntegrationByParts_of_memLp2
    {F P : PrimeTensor.Axis Depth.three → ScalarField3}
    {q : ScalarField3}
    (hF1 : ∀ j : PrimeTensor.Axis Depth.three, SpatialC1 (F j))
    (hq1 : SpatialC1 q)
    (hFL2 : ∀ j : PrimeTensor.Axis Depth.three,
      MemLp (F j) 2 (volume : Measure Point3))
    (hDFL2 : ∀ j : PrimeTensor.Axis Depth.three,
      MemLp (spatial3.d j (F j)) 2 (volume : Measure Point3))
    (hqL2 : MemLp q 2 (volume : Measure Point3))
    (hPL2 : ∀ j : PrimeTensor.Axis Depth.three,
      MemLp (P j) 2 (volume : Measure Point3))
    (hP : ∀ j : PrimeTensor.Axis Depth.three,
      spatial3.d j q = P j) :
    PressurePairingIntegrationByParts F P q := by

  unfold PressurePairingIntegrationByParts
  refine ⟨?_, ?_⟩

  · intro j
    exact
      integrable_mul_of_memLp_two_two_h3PressureHigher
        (hDFL2 j) hqL2

  · intro j

    have hDfAt :
        ∀ x : Point3,
          fderiv ℝ (F j) x (axisDirection j)
            = spatial3.d j (F j) x := by
      intro x
      exact
        ((hF1 j).partialDeriv_eq_fderiv_axisDirection x j).symm

    have hDqAt :
        ∀ x : Point3,
          fderiv ℝ q x (axisDirection j)
            = P j x := by
      intro x
      rw [← congrFun (hP j) x]
      exact
        (hq1.partialDeriv_eq_fderiv_axisDirection x j).symm

    have hDFG :
        Integrable
          (fun x : Point3 =>
            fderiv ℝ (F j) x (axisDirection j) * q x)
          (volume : Measure Point3) := by
      simpa only [hDfAt] using
        (integrable_mul_of_memLp_two_two_h3PressureHigher
          (hDFL2 j) hqL2)

    have hFDG :
        Integrable
          (fun x : Point3 =>
            F j x * fderiv ℝ q x (axisDirection j))
          (volume : Measure Point3) := by
      simpa only [hDqAt] using
        (integrable_mul_of_memLp_two_two_h3PressureHigher
          (hFL2 j) (hPL2 j))

    have hFG :
        Integrable
          (fun x : Point3 => F j x * q x)
          (volume : Measure Point3) :=
      integrable_mul_of_memLp_two_two_h3PressureHigher
        (hFL2 j) hqL2

    have hRaw :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := volume)
        (f := F j)
        (g := q)
        (v := axisDirection j)
        hDFG
        hFDG
        hFG
        (fun x hx => (hF1 j).differentiable_one.differentiableAt)
        (fun x hx => hq1.differentiable_one.differentiableAt)

    have hIBP :
        (∫ x : Point3, F j x * P j x)
          =
        -(∫ x : Point3, spatial3.d j (F j) x * q x) := by
      simpa only [hDfAt, hDqAt] using hRaw

    unfold spatialEnergyPairing
    rw [hIBP]
    ring

/-! ## Regularity of the canonical split-pressure gradient -/

private theorem h3EnergyClassSplitPressure_gradient_spatialC3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (spatial3.d j
        ((h3EnergyClassSplitPressureAt hClass ht) t)) := by

  rcases hClass.pressure_witness with
    ⟨pOld, hOldPDE, hOldC4⟩

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨le_of_lt ht.1, ht.2⟩

  have hEq :
      spatial3.d j
          ((h3EnergyClassSplitPressureAt hClass ht) t)
        =
      spatial3.d j (pOld t) := by
    funext x
    exact
      preterminalNavierStokes3_pressureGradient_eq
        (h3EnergyClassSplitPressureAt_navierStokes hClass ht)
        hOldPDE
        htAbs
        x
        j

  rw [hEq]
  exact hOldC4 t htTail j

/-! ## Positive-order pressure integration by parts -/

/-- The order-one through order-three pressure IBP data. -/
def H3PressureHigherIntegrationByPartsAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (t : ℝ) : Prop :=
  (∀ i : PrimeTensor.Axis Depth.three,
    PressurePairingIntegrationByParts
      (h3PressureVelocityFamily1 u t i)
      (h3PressureFieldFamily1 p t i)
      (h3PressurePotential1 p t i))
  ∧
  (∀ i k : PrimeTensor.Axis Depth.three,
    PressurePairingIntegrationByParts
      (h3PressureVelocityFamily2 u t i k)
      (h3PressureFieldFamily2 p t i k)
      (h3PressurePotential2 p t i k))
  ∧
  (∀ i k l : PrimeTensor.Axis Depth.three,
    PressurePairingIntegrationByParts
      (h3PressureVelocityFamily3 u t i k l)
      (h3PressureFieldFamily3 p t i k l)
      (h3PressurePotential3 p t i k l))

/-- Orders one through three of pressure integration by parts are automatic on
an H³ path.  No statement about the undifferentiated pressure potential is
used. -/
theorem h3PathEnergyClassProducesPressureHigherIntegrationByParts_closed :
    ∀
      (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
      (T : ℝ),
        LoggedPreterminalH3PathAdmissible u T →
        ∀ a : ℝ,
          ∀ hClass : PreterminalH3EnergyClass u a T,
            ∀ t : ℝ,
              ∀ ht : t ∈ Set.Ioo a T,
                H3PressureHigherIntegrationByPartsAt
                  u
                  (h3EnergyClassSplitPressureAt hClass ht)
                  t := by

  intro u T hH3 a hClass t ht

  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3EnergyClassSplitPressureAt hClass ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨le_of_lt ht.1, ht.2⟩

  have hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  have hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  obtain ⟨pNS, hNS⟩ := hH3.navier_stokes

  have hBase3
      (m : PrimeTensor.Axis Depth.three) :
      SpatialC3 (loggedVelocityComponent u t m) := by
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField u t x).component m)
    exact hNS.regularity.velocity_spatial_three t htAbs m

  have hBase2
      (m : PrimeTensor.Axis Depth.three) :
      SpatialC2 (loggedVelocityComponent u t m) :=
    (hBase3 m).toSpatialC2

  have hMem1
      (i m : PrimeTensor.Axis Depth.three) :
      MemLp
        (spatial3.d i (loggedVelocityComponent u t m))
        2 (volume : Measure Point3) := by
    have hmInt := hInt m
    have hmMeas := hMeas m
    dsimp only at hmInt hmMeas
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hmMeas.2.1 i) (hmInt.2.1 i))

  have hMem2
      (i k m : PrimeTensor.Axis Depth.three) :
      MemLp
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u t m)))
        2 (volume : Measure Point3) := by
    have hmInt := hInt m
    have hmMeas := hMeas m
    dsimp only at hmInt hmMeas
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hmMeas.2.2.1 i k) (hmInt.2.2.1 i k))

  have hMem3
      (i k l m : PrimeTensor.Axis Depth.three) :
      MemLp
        (spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (loggedVelocityComponent u t m))))
        2 (volume : Measure Point3) := by
    have hmInt := hInt m
    have hmMeas := hMeas m
    dsimp only at hmInt hmMeas
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hmMeas.2.2.2 i k l) (hmInt.2.2.2 i k l))

  have hArb4 : H3ArbitraryFourthVelocityJetMemLp2At u t :=
    h3PathEnergyClassProducesArbitraryFourthVelocityJetMemLp2_closed
      u T hH3 a hClass t ht

  have hSplitPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u) p T := by
    dsimp only [p]
    exact h3EnergyClassSplitPressureAt_navierStokes hClass ht

  have hPressure2 : SpatialC2 (p t) :=
    hSplitPDE.regularity.pressure_spatial_two t htAbs

  have hGrad3
      (r : PrimeTensor.Axis Depth.three) :
      SpatialC3 (spatial3.d r (p t)) := by
    dsimp only [p]
    exact
      h3EnergyClassSplitPressure_gradient_spatialC3
        hClass ht r

  unfold H3PressureHigherIntegrationByPartsAt
  refine ⟨?_, ?_, ?_⟩

  · intro i

    let q : ScalarField3 :=
      h3PressurePotential1 p t i

    have hq1 : SpatialC1 q := by
      dsimp only [q, h3PressurePotential1]
      exact (hGrad3 i).of_le (by norm_num)

    have hqL2 : MemLp q 2 (volume : Measure Point3) := by
      dsimp only [q, h3PressurePotential1, p]
      simpa only [momentumPressure0Component] using
        (h3PathEnergyClassProducesPressure0MemLp2_closed
          u T hH3 a hClass t ht i)

    have hF1 :
        ∀ m : PrimeTensor.Axis Depth.three,
          SpatialC1 (h3PressureVelocityFamily1 u t i m) := by
      intro m
      dsimp only [h3PressureVelocityFamily1]
      exact
        ((hBase3 m).partialDeriv_contDiff_two i).of_le
          (by norm_num)

    have hFL2 :
        ∀ m : PrimeTensor.Axis Depth.three,
          MemLp
            (h3PressureVelocityFamily1 u t i m)
            2 (volume : Measure Point3) := by
      intro m
      simpa only [h3PressureVelocityFamily1] using hMem1 i m

    have hDFL2 :
        ∀ m : PrimeTensor.Axis Depth.three,
          MemLp
            (spatial3.d m (h3PressureVelocityFamily1 u t i m))
            2 (volume : Measure Point3) := by
      intro m
      have hEq :
          spatial3.d m
              (spatial3.d i (loggedVelocityComponent u t m))
            =
          spatial3.d i
              (spatial3.d m (loggedVelocityComponent u t m)) := by
        funext x
        exact (hBase2 m).spatial_d_comm x m i
      dsimp only [h3PressureVelocityFamily1]
      rw [hEq]
      exact hMem2 i m m

    have hPL2 :
        ∀ m : PrimeTensor.Axis Depth.three,
          MemLp
            (h3PressureFieldFamily1 p t i m)
            2 (volume : Measure Point3) := by
      intro m
      dsimp only [h3PressureFieldFamily1, p]
      exact
        h3PathEnergyClassProducesPressure1MemLp2_closed
          u T hH3 a hClass t ht i m

    have hP :
        ∀ m : PrimeTensor.Axis Depth.three,
          spatial3.d m q = h3PressureFieldFamily1 p t i m := by
      intro m
      dsimp only [q, h3PressurePotential1, h3PressureFieldFamily1]
      unfold momentumPressure1Component momentumPressure0Component
      funext x
      exact hPressure2.spatial_d_comm x m i

    exact
      pressurePairingIntegrationByParts_of_memLp2
        hF1 hq1 hFL2 hDFL2 hqL2 hPL2 hP

  · intro i k

    let q : ScalarField3 :=
      h3PressurePotential2 p t i k

    have hq1 : SpatialC1 q := by
      dsimp only [q, h3PressurePotential2]
      exact
        ((hGrad3 k).partialDeriv_contDiff_two i).of_le
          (by norm_num)

    have hqL2 : MemLp q 2 (volume : Measure Point3) := by
      dsimp only [q, h3PressurePotential2, p]
      simpa only [momentumPressure1Component, momentumPressure0Component] using
        (h3PathEnergyClassProducesPressure1MemLp2_closed
          u T hH3 a hClass t ht i k)

    have hF1 :
        ∀ m : PrimeTensor.Axis Depth.three,
          SpatialC1 (h3PressureVelocityFamily2 u t i k m) := by
      intro m
      dsimp only [h3PressureVelocityFamily2]
      exact
        (hClass.velocity_spatial_five
          t htTail m i k).of_le
          (by norm_num)

    have hFL2 :
        ∀ m : PrimeTensor.Axis Depth.three,
          MemLp
            (h3PressureVelocityFamily2 u t i k m)
            2 (volume : Measure Point3) := by
      intro m
      simpa only [h3PressureVelocityFamily2] using hMem2 i k m

    have hDFL2 :
        ∀ m : PrimeTensor.Axis Depth.three,
          MemLp
            (spatial3.d m (h3PressureVelocityFamily2 u t i k m))
            2 (volume : Measure Point3) := by
      intro m
      dsimp only [h3PressureVelocityFamily2]

      have hmi :
          spatial3.d m
              (spatial3.d i
                (spatial3.d k (loggedVelocityComponent u t m)))
            =
          spatial3.d i
              (spatial3.d m
                (spatial3.d k (loggedVelocityComponent u t m))) := by
        funext x
        exact
          ((hBase3 m).partialDeriv_contDiff_two k).spatial_d_comm
            x m i

      have hmk :
          spatial3.d m
              (spatial3.d k (loggedVelocityComponent u t m))
            =
          spatial3.d k
              (spatial3.d m (loggedVelocityComponent u t m)) := by
        funext x
        exact (hBase2 m).spatial_d_comm x m k

      rw [hmi, hmk]
      exact hMem3 i k m m

    have hPL2 :
        ∀ m : PrimeTensor.Axis Depth.three,
          MemLp
            (h3PressureFieldFamily2 p t i k m)
            2 (volume : Measure Point3) := by
      intro m
      dsimp only [h3PressureFieldFamily2, p]
      exact
        h3PathEnergyClassProducesPressure2MemLp2_closed
          u T hH3 a hClass t ht i k m

    have hP :
        ∀ m : PrimeTensor.Axis Depth.three,
          spatial3.d m q = h3PressureFieldFamily2 p t i k m := by
      intro m
      dsimp only [q, h3PressurePotential2, h3PressureFieldFamily2]
      unfold momentumPressure2Component momentumPressure1Component momentumPressure0Component

      have hmi :
          spatial3.d m
              (spatial3.d i (spatial3.d k (p t)))
            =
          spatial3.d i
              (spatial3.d m (spatial3.d k (p t))) := by
        funext x
        exact (hGrad3 k).toSpatialC2.spatial_d_comm x m i

      have hmk :
          spatial3.d m (spatial3.d k (p t))
            =
          spatial3.d k (spatial3.d m (p t)) := by
        funext x
        exact hPressure2.spatial_d_comm x m k

      rw [hmi, hmk]

    exact
      pressurePairingIntegrationByParts_of_memLp2
        hF1 hq1 hFL2 hDFL2 hqL2 hPL2 hP

  · intro i k l

    let q : ScalarField3 :=
      h3PressurePotential3 p t i k l

    have hq1 : SpatialC1 q := by
      dsimp only [q, h3PressurePotential3]
      have hkl2 :
          SpatialC2
            (spatial3.d k (spatial3.d l (p t))) :=
        (hGrad3 l).partialDeriv_contDiff_two k
      exact hkl2.partialDeriv_contDiff_one i

    have hqL2 : MemLp q 2 (volume : Measure Point3) := by
      dsimp only [q, h3PressurePotential3, p]
      simpa only [
        momentumPressure2Component,
        momentumPressure1Component,
        momentumPressure0Component
      ] using
        (h3PathEnergyClassProducesPressure2MemLp2_closed
          u T hH3 a hClass t ht i k l)

    have hF1 :
        ∀ m : PrimeTensor.Axis Depth.three,
          SpatialC1 (h3PressureVelocityFamily3 u t i k l m) := by
      intro m
      dsimp only [h3PressureVelocityFamily3]
      have hkl3 :
          SpatialC3
            (spatial3.d k
              (spatial3.d l
                (loggedVelocityComponent u t m))) :=
        hClass.velocity_spatial_five t htTail m k l
      exact
        (hkl3.partialDeriv_contDiff_two i).of_le
          (by norm_num)

    have hFL2 :
        ∀ m : PrimeTensor.Axis Depth.three,
          MemLp
            (h3PressureVelocityFamily3 u t i k l m)
            2 (volume : Measure Point3) := by
      intro m
      simpa only [h3PressureVelocityFamily3] using hMem3 i k l m

    have hDFL2 :
        ∀ m : PrimeTensor.Axis Depth.three,
          MemLp
            (spatial3.d m (h3PressureVelocityFamily3 u t i k l m))
            2 (volume : Measure Point3) := by
      intro m
      dsimp only [h3PressureVelocityFamily3]

      have hmi :
          spatial3.d m
              (spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t m))))
            =
          spatial3.d i
              (spatial3.d m
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t m)))) := by
        funext x
        have hkl2 :
            SpatialC2
              (spatial3.d k
                (spatial3.d l
                  (loggedVelocityComponent u t m))) :=
          (hClass.velocity_spatial_five t htTail m k l).toSpatialC2
        exact hkl2.spatial_d_comm x m i

      have hmk :
          spatial3.d m
              (spatial3.d k
                (spatial3.d l
                  (loggedVelocityComponent u t m)))
            =
          spatial3.d k
              (spatial3.d m
                (spatial3.d l
                  (loggedVelocityComponent u t m))) := by
        funext x
        have hl2 :
            SpatialC2
              (spatial3.d l
                (loggedVelocityComponent u t m)) :=
          (hBase3 m).partialDeriv_contDiff_two l
        exact hl2.spatial_d_comm x m k

      have hml :
          spatial3.d m
              (spatial3.d l (loggedVelocityComponent u t m))
            =
          spatial3.d l
              (spatial3.d m (loggedVelocityComponent u t m)) := by
        funext x
        exact (hBase2 m).spatial_d_comm x m l

      rw [hmi, hmk, hml]
      exact hArb4 i k l m m

    have hPL2 :
        ∀ m : PrimeTensor.Axis Depth.three,
          MemLp
            (h3PressureFieldFamily3 p t i k l m)
            2 (volume : Measure Point3) := by
      intro m
      dsimp only [h3PressureFieldFamily3, p]
      exact
        h3PathEnergyClassProducesPressure3MemLp2_closed
          u T hH3 a hClass t ht i k l m

    have hP :
        ∀ m : PrimeTensor.Axis Depth.three,
          spatial3.d m q = h3PressureFieldFamily3 p t i k l m := by
      intro m
      dsimp only [q, h3PressurePotential3, h3PressureFieldFamily3]
      unfold momentumPressure3Component momentumPressure1Component momentumPressure0Component

      have hmi :
          spatial3.d m
              (spatial3.d i
                (spatial3.d k
                  (spatial3.d l (p t))))
            =
          spatial3.d i
              (spatial3.d m
                (spatial3.d k
                  (spatial3.d l (p t)))) := by
        funext x
        have hkl2 :
            SpatialC2
              (spatial3.d k (spatial3.d l (p t))) :=
          (hGrad3 l).partialDeriv_contDiff_two k
        exact hkl2.spatial_d_comm x m i

      have hmk :
          spatial3.d m
              (spatial3.d k (spatial3.d l (p t)))
            =
          spatial3.d k
              (spatial3.d m (spatial3.d l (p t))) := by
        funext x
        exact (hGrad3 l).toSpatialC2.spatial_d_comm x m k

      have hml :
          spatial3.d m (spatial3.d l (p t))
            =
          spatial3.d l (spatial3.d m (p t)) := by
        funext x
        exact hPressure2.spatial_d_comm x m l

      rw [hmi, hmk, hml]

    exact
      pressurePairingIntegrationByParts_of_memLp2
        hF1 hq1 hFL2 hDFL2 hqL2 hPL2 hP

/-! ## Positive-order pressure cancellation -/

/-- All three positive-order pressure blocks vanish. -/
theorem h3PathEnergyClassProducesPressureHigherCancellation_closed :
    ∀
      (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
      (T : ℝ),
        LoggedPreterminalH3PathAdmissible u T →
        ∀ a : ℝ,
          ∀ hClass : PreterminalH3EnergyClass u a T,
            ∀ t : ℝ,
              ∀ ht : t ∈ Set.Ioo a T,
                velocityH3PressureDerivative1At
                    u (h3EnergyClassSplitPressureAt hClass ht) t = 0
                ∧
                velocityH3PressureDerivative2At
                    u (h3EnergyClassSplitPressureAt hClass ht) t = 0
                ∧
                velocityH3PressureDerivative3At
                    u (h3EnergyClassSplitPressureAt hClass ht) t = 0 := by

  intro u T hH3 a hClass t ht

  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3EnergyClassSplitPressureAt hClass ht

  have hIBP : H3PressureHigherIntegrationByPartsAt u p t := by
    dsimp only [p]
    exact
      h3PathEnergyClassProducesPressureHigherIntegrationByParts_closed
        u T hH3 a hClass t ht

  have hDiv : H3DifferentiatedIncompressibilityAt u t :=
    preterminalH3EnergyClass_produces_differentiatedIncompressibility
      hClass ht

  refine ⟨?_, ?_, ?_⟩

  · unfold velocityH3PressureDerivative1At
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    simpa [
      p,
      h3PressureVelocityFamily1,
      h3PressureFieldFamily1
    ] using
      sum_pressurePairing_eq_zero
        (hIBP.1 i)
        (hDiv.2.1 i)

  · unfold velocityH3PressureDerivative2At
    calc
      (∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)))
              (momentumPressure2Component p t i k j))
          =
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ j : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d i
                  (spatial3.d k
                    (loggedVelocityComponent u t j)))
                (momentumPressure2Component p t i k j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_comm]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro k hk
        simpa [
          h3PressureVelocityFamily2,
          h3PressureFieldFamily2
        ] using
          sum_pressurePairing_eq_zero
            (hIBP.2.1 i k)
            (hDiv.2.2.1 i k)

  · unfold velocityH3PressureDerivative3At
    calc
      (∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d i
                  (spatial3.d k
                    (spatial3.d l
                      (loggedVelocityComponent u t j))))
                (momentumPressure3Component p t i k l j))
          =
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              ∑ j : PrimeTensor.Axis Depth.three,
                spatialEnergyPairing
                  (spatial3.d i
                    (spatial3.d k
                      (spatial3.d l
                        (loggedVelocityComponent u t j))))
                  (momentumPressure3Component p t i k l j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.sum_comm]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro k hk
        apply Finset.sum_eq_zero
        intro l hl
        simpa [
          h3PressureVelocityFamily3,
          h3PressureFieldFamily3
        ] using
          sum_pressurePairing_eq_zero
            (hIBP.2.2 i k l)
            (hDiv.2.2.2 i k l)

/-! ## Reduce the pressure frontier to the gauge-sensitive order-zero block -/

/-- Only the zeroth-order velocity/pressure pairing remains to be cancelled. -/
def H3PathEnergyClassProducesPressure0Cancellation : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              velocityH3PressureDerivative0At
                  u
                  (h3EnergyClassSplitPressureAt hClass ht)
                  t
                =
              0

/-- Zeroth-order cancellation plus the closed positive-order blocks gives the
full pressure cancellation package. -/
theorem h3PathEnergyClassProducesPressureCancellation_of_orderZero
    (hZero : H3PathEnergyClassProducesPressure0Cancellation) :
    H3PathEnergyClassProducesPressureCancellation := by

  intro u T hH3 a hClass t ht

  have h0 := hZero u T hH3 a hClass t ht

  rcases
    h3PathEnergyClassProducesPressureHigherCancellation_closed
      u T hH3 a hClass t ht
  with ⟨h1, h2, h3⟩

  unfold velocityH3PressureDerivativeAt
  rw [h0, h1, h2, h3]
  ring

/-- The active BKM continuation theorem now needs only the gauge-safe
zeroth-order pressure cancellation, in addition to the low-tail and exact
energy-derivative frontiers. -/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_pressure0Cancellation
    (hLow : H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative : H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hPressure0 : H3PathEnergyClassProducesPressure0Cancellation) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_pressureCancellation
      hLow
      hDerivative
      (h3PathEnergyClassProducesPressureCancellation_of_orderZero
        hPressure0)

end

end Euclidean
end Bridge
end PrimeTensor

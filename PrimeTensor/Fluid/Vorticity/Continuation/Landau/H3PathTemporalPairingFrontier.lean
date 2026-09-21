import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathPathMajorantsFullScalarClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathMajorantPDEPairing

/-!
# Split derivative majorants into exact scalar derivatives and temporal pairing integrability

The path-specific majorant frontier was useful because one hypothesis supplied
two logically different facts:

1. differentiation of the four scalar H³ energy blocks;
2. integrability of the four spatial-jet / temporal-jet products.

Only the second fact is used when reconstructing the complete PDE pairing
package by subtraction.

This file isolates that exact fixed-time requirement as

    H3TemporalEnergyPairingIntegrableAt

and its path-level version

    H3PathEnergyClassProducesTemporalEnergyPairingIntegrability.

The Navier--Stokes temporal identities turn these temporal products into the
complete momentum-RHS products.  Diffusion and pressure product integrability
then recover transport product integrability algebraically.

Consequently BKM continuation can now be stated without any majorant object.
It consumes only

* the low-frequency `L²` tail;
* exact orderwise scalar energy derivative identities;
* temporal energy-pairing integrability;
* full-order diffusion/pressure scalar data.

The existing path-majorant route is retained only as one sufficient mechanism
for producing the first two time-side conclusions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathTemporalPairingFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Exact temporal product integrability -/

/--
Integrability of every spatial-jet / temporal-jet product occurring in the
formal H³ energy derivative at one time.
-/
def H3TemporalEnergyPairingIntegrableAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      Integrable
        (fun x : Point3 =>
          loggedVelocityComponent u t j x
            *
          loggedVelocityTemporalComponent u t j x)
        (volume : Measure Point3)
  )
    ∧
  (
    ∀ i j : PrimeTensor.Axis Depth.three,
      Integrable
        (fun x : Point3 =>
          spatial3.d i
              (loggedVelocityComponent u t j) x
            *
          spatial3.d i
              (loggedVelocityTemporalComponent u t j) x)
        (volume : Measure Point3)
  )
    ∧
  (
    ∀ i k j : PrimeTensor.Axis Depth.three,
      Integrable
        (fun x : Point3 =>
          spatial3.d i
              (spatial3.d k
                (loggedVelocityComponent u t j)) x
            *
          spatial3.d i
              (spatial3.d k
                (loggedVelocityTemporalComponent u t j)) x)
        (volume : Measure Point3)
  )
    ∧
  (
    ∀ i k l j : PrimeTensor.Axis Depth.three,
      Integrable
        (fun x : Point3 =>
          spatial3.d i
              (spatial3.d k
                (spatial3.d l
                  (loggedVelocityComponent u t j))) x
            *
          spatial3.d i
              (spatial3.d k
                (spatial3.d l
                  (loggedVelocityTemporalComponent u t j))) x)
        (volume : Measure Point3)
  )

/--
Path-specific temporal-pairing frontier.
-/
def H3PathEnergyClassProducesTemporalEnergyPairingIntegrability : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              H3TemporalEnergyPairingIntegrableAt u t

/-! ## Temporal products are exactly momentum-RHS products -/

/--
At one strict energy-class time, temporal-pairing integrability gives
integrability of all four complete momentum-RHS product families.
-/
theorem h3MomentumRHSPairings_integrable_of_temporalPairings
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T)
    (hTemporal :
      H3TemporalEnergyPairingIntegrableAt u t) :
    (
      (∀ j : PrimeTensor.Axis Depth.three,
        Integrable
          (fun x : Point3 =>
            loggedVelocityComponent u t j x
              *
            momentumRHS0Component
              (logSpaceTimeVectorField u)
              p t j x)
          (volume : Measure Point3))
        ∧
      (∀ i j : PrimeTensor.Axis Depth.three,
        Integrable
          (fun x : Point3 =>
            spatial3.d i
                (loggedVelocityComponent u t j) x
              *
            momentumRHS1Component
              (logSpaceTimeVectorField u)
              p t i j x)
          (volume : Measure Point3))
        ∧
      (∀ i k j : PrimeTensor.Axis Depth.three,
        Integrable
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)) x
              *
            momentumRHS2Component
              (logSpaceTimeVectorField u)
              p t i k j x)
          (volume : Measure Point3))
        ∧
      (∀ i k l j : PrimeTensor.Axis Depth.three,
        Integrable
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))) x
              *
            momentumRHS3Component
              (logSpaceTimeVectorField u)
              p t i k l j x)
          (volume : Measure Point3))
    ) := by

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j
    have hInt := hTemporal.1 j
    have hEq :
        loggedVelocityTemporalComponent u t j
          =
        momentumRHS0Component
          (logSpaceTimeVectorField u)
          p t j :=
      loggedVelocityTemporalComponent_eq_momentumRHS0
        hPDE htAbs j
    rw [hEq] at hInt
    exact hInt

  · intro i j
    have hInt := hTemporal.2.1 i j
    have hEq :
        spatial3.d i
            (loggedVelocityTemporalComponent u t j)
          =
        momentumRHS1Component
          (logSpaceTimeVectorField u)
          p t i j :=
      spatial_d_loggedVelocityTemporalComponent_eq_momentumRHS1
        hPDE htAbs i j
    rw [hEq] at hInt
    exact hInt

  · intro i k j
    have hInt := hTemporal.2.2.1 i k j
    have hEq :
        spatial3.d i
            (spatial3.d k
              (loggedVelocityTemporalComponent u t j))
          =
        momentumRHS2Component
          (logSpaceTimeVectorField u)
          p t i k j :=
      spatial_d2_loggedVelocityTemporalComponent_eq_momentumRHS2
        hPDE htAbs i k j
    rw [hEq] at hInt
    exact hInt

  · intro i k l j
    have hInt := hTemporal.2.2.2 i k l j
    have hEq :
        spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (loggedVelocityTemporalComponent u t j)))
          =
        momentumRHS3Component
          (logSpaceTimeVectorField u)
          p t i k l j :=
      spatial_d3_loggedVelocityTemporalComponent_eq_momentumRHS3
        hPDE htAbs i k l j
    rw [hEq] at hInt
    exact hInt

/-! ## Reconstruct complete PDE pairing integrability -/

/--
Complete momentum-RHS product integrability plus the separated diffusion and
pressure products recovers transport product integrability by subtraction.
-/
theorem h3PDEPairingIntegrableAt_of_rhs_of_diffusion_pressure
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hHigher :
      HigherOrderMomentumRHSSplitsAt
        (logSpaceTimeVectorField u)
        p t)
    (hRHS :
      (∀ j : PrimeTensor.Axis Depth.three,
        Integrable
          (fun x : Point3 =>
            loggedVelocityComponent u t j x
              *
            momentumRHS0Component
              (logSpaceTimeVectorField u)
              p t j x)
          (volume : Measure Point3))
        ∧
      (∀ i j : PrimeTensor.Axis Depth.three,
        Integrable
          (fun x : Point3 =>
            spatial3.d i
                (loggedVelocityComponent u t j) x
              *
            momentumRHS1Component
              (logSpaceTimeVectorField u)
              p t i j x)
          (volume : Measure Point3))
        ∧
      (∀ i k j : PrimeTensor.Axis Depth.three,
        Integrable
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)) x
              *
            momentumRHS2Component
              (logSpaceTimeVectorField u)
              p t i k j x)
          (volume : Measure Point3))
        ∧
      (∀ i k l j : PrimeTensor.Axis Depth.three,
        Integrable
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))) x
              *
            momentumRHS3Component
              (logSpaceTimeVectorField u)
              p t i k l j x)
          (volume : Measure Point3)))
    (hDiffusion : H3DiffusionPairingIntegrableAt u t)
    (hPressure : H3PressurePairingIntegrableAt u p t) :
    H3PDEPairingIntegrableAt u p t := by

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j

    have hTransport :
        Integrable
          (fun x : Point3 =>
            loggedVelocityComponent u t j x
              *
            momentumTransport0Component
              (logSpaceTimeVectorField u)
              t j x)
          (volume : Measure Point3) := by

      have hEq :
          (fun x : Point3 =>
            loggedVelocityComponent u t j x
              *
            momentumTransport0Component
              (logSpaceTimeVectorField u)
              t j x)
            =
          (fun x : Point3 =>
            loggedVelocityComponent u t j x
                *
              momentumDiffusion0Component
                (logSpaceTimeVectorField u)
                t j x
              -
            loggedVelocityComponent u t j x
                *
              momentumPressure0Component
                p t j x
              -
            loggedVelocityComponent u t j x
                *
              momentumRHS0Component
                (logSpaceTimeVectorField u)
                p t j x) := by
        funext x
        rw [
          congrFun
            (momentumRHS0Component_eq_split
              (logSpaceTimeVectorField u)
              p t j)
            x
        ]
        ring

      rw [hEq]
      exact
        ((hDiffusion.1 j).sub
          (hPressure.1 j)).sub
          (hRHS.1 j)

    exact
      ⟨
        hDiffusion.1 j,
        hTransport,
        hPressure.1 j
      ⟩

  · intro i j

    have hTransport :
        Integrable
          (fun x : Point3 =>
            spatial3.d i
                (loggedVelocityComponent u t j) x
              *
            momentumTransport1Component
              (logSpaceTimeVectorField u)
              t i j x)
          (volume : Measure Point3) := by

      have hEq :
          (fun x : Point3 =>
            spatial3.d i
                (loggedVelocityComponent u t j) x
              *
            momentumTransport1Component
              (logSpaceTimeVectorField u)
              t i j x)
            =
          (fun x : Point3 =>
            spatial3.d i
                (loggedVelocityComponent u t j) x
                *
              momentumDiffusion1Component
                (logSpaceTimeVectorField u)
                t i j x
              -
            spatial3.d i
                (loggedVelocityComponent u t j) x
                *
              momentumPressure1Component
                p t i j x
              -
            spatial3.d i
                (loggedVelocityComponent u t j) x
                *
              momentumRHS1Component
                (logSpaceTimeVectorField u)
                p t i j x) := by
        funext x
        rw [
          congrFun
            (momentumRHS1Component_eq_split
              (logSpaceTimeVectorField u)
              p t i j)
            x
        ]
        ring

      rw [hEq]
      exact
        ((hDiffusion.2.1 i j).sub
          (hPressure.2.1 i j)).sub
          (hRHS.2.1 i j)

    exact
      ⟨
        hDiffusion.2.1 i j,
        hTransport,
        hPressure.2.1 i j
      ⟩

  · intro i k j

    have hTransport :
        Integrable
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)) x
              *
            momentumTransport2Component
              (logSpaceTimeVectorField u)
              t i k j x)
          (volume : Measure Point3) := by

      have hEq :
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)) x
              *
            momentumTransport2Component
              (logSpaceTimeVectorField u)
              t i k j x)
            =
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)) x
                *
              momentumDiffusion2Component
                (logSpaceTimeVectorField u)
                t i k j x
              -
            spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)) x
                *
              momentumPressure2Component
                p t i k j x
              -
            spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)) x
                *
              momentumRHS2Component
                (logSpaceTimeVectorField u)
                p t i k j x) := by
        funext x
        rw [congrFun (hHigher.1 i k j) x]
        ring

      rw [hEq]
      exact
        ((hDiffusion.2.2.1 i k j).sub
          (hPressure.2.2.1 i k j)).sub
          (hRHS.2.2.1 i k j)

    exact
      ⟨
        hDiffusion.2.2.1 i k j,
        hTransport,
        hPressure.2.2.1 i k j
      ⟩

  · intro i k l j

    have hTransport :
        Integrable
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))) x
              *
            momentumTransport3Component
              (logSpaceTimeVectorField u)
              t i k l j x)
          (volume : Measure Point3) := by

      have hEq :
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))) x
              *
            momentumTransport3Component
              (logSpaceTimeVectorField u)
              t i k l j x)
            =
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))) x
                *
              momentumDiffusion3Component
                (logSpaceTimeVectorField u)
                t i k l j x
              -
            spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))) x
                *
              momentumPressure3Component
                p t i k l j x
              -
            spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))) x
                *
              momentumRHS3Component
                (logSpaceTimeVectorField u)
                p t i k l j x) := by
        funext x
        rw [congrFun (hHigher.2 i k l j) x]
        ring

      rw [hEq]
      exact
        ((hDiffusion.2.2.2 i k l j).sub
          (hPressure.2.2.2 i k l j)).sub
          (hRHS.2.2.2 i k l j)

    exact
      ⟨
        hDiffusion.2.2.2 i k l j,
        hTransport,
        hPressure.2.2.2 i k l j
      ⟩

/--
Temporal-pairing integrability plus separated diffusion/pressure product
integrability reconstructs the complete PDE pairing package.
-/
theorem h3PDEPairingIntegrableAt_of_temporalPairings_of_diffusion_pressure
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T)
    (hHigher :
      HigherOrderMomentumRHSSplitsAt
        (logSpaceTimeVectorField u)
        p t)
    (hTemporal :
      H3TemporalEnergyPairingIntegrableAt u t)
    (hDiffusion : H3DiffusionPairingIntegrableAt u t)
    (hPressure : H3PressurePairingIntegrableAt u p t) :
    H3PDEPairingIntegrableAt u p t := by

  have hRHS :=
    h3MomentumRHSPairings_integrable_of_temporalPairings
      hClass
      ht
      hPDE
      hTemporal

  exact
    h3PDEPairingIntegrableAt_of_rhs_of_diffusion_pressure
      hClass
      ht
      hHigher
      hRHS
      hDiffusion
      hPressure

/-! ## Path-level reconstruction -/

/--
Path-level temporal-pairing and full-scalar packages imply exact PDE pairing
integrability.
-/
theorem h3PathEnergyClassProducesPDEPairingIntegrability_of_temporalPairings_of_fullScalarEnergy
    (hTemporal :
      H3PathEnergyClassProducesTemporalEnergyPairingIntegrability)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathEnergyClassProducesPDEPairingIntegrability := by

  intro u T hH3 a hClass t ht

  rcases
    hFull u T hH3 a hClass t ht
  with
    ⟨
      hDiffusionPairing,
      hPressurePairing,
      hPressure,
      hDiffusion
    ⟩

  exact
    h3PDEPairingIntegrableAt_of_temporalPairings_of_diffusion_pressure
      hClass
      ht
      (h3EnergyClassSplitPressureAt_navierStokes
        hClass ht)
      (h3EnergyClassSplitPressureAt_momentumRHSSplits
        hClass ht)
      (hTemporal u T hH3 a hClass t ht)
      hDiffusionPairing
      hPressurePairing

/-! ## Majorants are only one sufficient route -/

/--
The current path-majorant frontier implies temporal energy-pairing
integrability, but the downstream theorem no longer requires the stronger
majorant object.
-/
theorem h3PathEnergyClassProducesTemporalEnergyPairingIntegrability_of_pathMajorants
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesTemporalEnergyPairingIntegrability := by

  intro u T hH3 a hClass t ht

  rcases
    hMajorants u T hH3 a hClass t ht
  with
    ⟨hMajorant⟩

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3EnergyClassSplitPressureAt hClass ht

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T := by
    dsimp only [p]
    exact
      h3EnergyClassSplitPressureAt_navierStokes
        hClass ht

  have hRHS :=
    h3MomentumRHSPairings_integrable_of_majorants
      hClass
      ht
      hPDE
      hMajorant

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j
    have hInt := hRHS.1 j
    have hEq :
        loggedVelocityTemporalComponent u t j
          =
        momentumRHS0Component
          (logSpaceTimeVectorField u)
          p t j :=
      loggedVelocityTemporalComponent_eq_momentumRHS0
        hPDE htAbs j
    rw [← hEq] at hInt
    exact hInt

  · intro i j
    have hInt := hRHS.2.1 i j
    have hEq :
        spatial3.d i
            (loggedVelocityTemporalComponent u t j)
          =
        momentumRHS1Component
          (logSpaceTimeVectorField u)
          p t i j :=
      spatial_d_loggedVelocityTemporalComponent_eq_momentumRHS1
        hPDE htAbs i j
    rw [← hEq] at hInt
    exact hInt

  · intro i k j
    have hInt := hRHS.2.2.1 i k j
    have hEq :
        spatial3.d i
            (spatial3.d k
              (loggedVelocityTemporalComponent u t j))
          =
        momentumRHS2Component
          (logSpaceTimeVectorField u)
          p t i k j :=
      spatial_d2_loggedVelocityTemporalComponent_eq_momentumRHS2
        hPDE htAbs i k j
    rw [← hEq] at hInt
    exact hInt

  · intro i k l j
    have hInt := hRHS.2.2.2 i k l j
    have hEq :
        spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (loggedVelocityTemporalComponent u t j)))
          =
        momentumRHS3Component
          (logSpaceTimeVectorField u)
          p t i k l j :=
      spatial_d3_loggedVelocityTemporalComponent_eq_momentumRHS3
        hPDE htAbs i k l j
    rw [← hEq] at hInt
    exact hInt

/-! ## Majorant-free public BKM frontier -/

/--
BKM continuation with derivative majorants removed from the public interface.

The time side is now stated by its two exact consequences:

1. the four scalar H³ energy derivative identities;
2. integrability of the four temporal energy-pairing families.

This formulation is suitable for either the existing dominated-convergence
route or a future Hilbert-valued differentiation proof.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_temporalPairings_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hTemporal :
      H3PathEnergyClassProducesTemporalEnergyPairingIntegrability)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  have hPairing :
      H3PathEnergyClassProducesPDEPairingIntegrability :=
    h3PathEnergyClassProducesPDEPairingIntegrability_of_temporalPairings_of_fullScalarEnergy
      hTemporal
      hFull

  have hSigns :
      H3PathEnergyClassProducesFullScalarSigns :=
    h3PathEnergyClassProducesFullScalarSigns_of_fullScalarEnergy
      hFull

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_exactEnergy
      hLow
      hDerivative
      hPairing
      hSigns

/--
Compatibility with the current path-majorant theorem.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_pathMajorants_of_fullScalarEnergy_via_temporalPairings
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_temporalPairings_of_fullScalarEnergy
      hLow
      (h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_pathMajorants
        hMajorants)
      (h3PathEnergyClassProducesTemporalEnergyPairingIntegrability_of_pathMajorants
        hMajorants)
      hFull

end

end Euclidean
end Bridge
end PrimeTensor

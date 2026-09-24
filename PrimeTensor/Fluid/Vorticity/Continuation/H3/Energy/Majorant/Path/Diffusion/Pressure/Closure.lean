import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Majorant.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Majorant.Pairing.PDE

/-!
# Close the H³-path time side and reduce BKM to path majorants plus diffusion/pressure whole-space data

The H³-path route has now closed both higher mixed-time commutation branches and
restricted the derivative-majorant hypothesis to actual H³-path energy
classes.

`H3PathMajorantPDEPairing` already showed that derivative majorants recover the
complete momentum-RHS pairing once diffusion and pressure pairings are
integrable.  Therefore the remaining fixed-time spatial package may be taken to
be only

* diffusion pairing integrability;
* pressure pairing integrability;
* pressure integration by parts;
* diffusion integration by parts.

This file combines those reductions without reintroducing the old global
higher-time or global-majorant interfaces.

At one strict H³-path energy-class time:

1. the path-specific majorant witness reconstructs the tail-local domination
   package;
2. the already-closed order-two and order-three mixed commutation theorems give
   the exact four scalar H³ energy derivative identities;
3. path majorants plus diffusion/pressure pairings reconstruct the complete PDE
   pairing package;
4. the existing pointwise Landau transport theorem gives the transport bound;
5. pressure cancellation and diffusion nonpositivity give the canonical H³
   growth inequality;
6. the order-zero part gives kinetic-energy monotonicity and hence the BKM
   low-frequency L² tail.

Consequently BKM continuation now depends on only two path-specific analytic
inputs:

    H3PathEnergyClassProducesH3EnergyDerivativeMajorants

and

    H3PathEnergyClassProducesDiffusionPressureWholeSpaceEnergyData.

No new PDE estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathPathMajorantsDiffusionPressureClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Exact energy derivatives from path-specific majorants -/

/--
Path-specific derivative majorants plus the now-closed order-two/order-three
mixed commutation give all four exact scalar H³ energy derivative identities
at every strict path energy-class time.
-/
theorem h3Path_orderEnergyDerivativeIdentities_of_pathMajorants
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    H3OrderEnergyDerivativeIdentities u t := by

  rcases
    hMajorants u T hH3 a hClass t ht
  with
    ⟨hMajorant⟩

  have hReduced :
      H3EnergyDerivativeReducedDominationDataAt
        u a T t :=
    {
      order0 :=
        h3Order0ReducedDomination_of_majorant
          hClass ht hMajorant.order0
      order1 :=
        h3Order1ReducedDomination_of_majorant
          hClass ht hMajorant.order1
      order2 :=
        h3Order2ReducedDomination_of_majorant
          hClass ht hMajorant.order2
      order3 :=
        h3Order3ReducedDomination_of_majorant
          hClass ht hMajorant.order3
    }

  have ha :
      0 < a :=
    hClass.terminal_start.1

  have hDom :
      H3EnergyDerivativeTailLocalDominationDataAt
        u a T t :=
    {
      order0 :=
        h3Order0EnergyDerivativeDominatedAt_of_reducedOnTail
          hH3.navier_stokes
          ha
          ht
          hReduced.order0
      order1 :=
        h3Order1EnergyDerivativeDominatedAt_of_reducedOnTail
          hH3.navier_stokes
          ha
          ht
          hReduced.order1
      order2 :=
        h3Order2EnergyDerivativeDominatedOnTailAt_of_reduced
          hH3.navier_stokes
          ha
          ht
          hReduced.order2
      order3 :=
        h3Order3EnergyDerivativeDominatedOnTailAt_of_reduced
          hH3.navier_stokes
          ha
          ht
          hReduced.order3
    }

  have hMixed2 :
      H3Order2VelocityMixedTimeDerivativeOnTail u a T :=
    h3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail
      u T hH3 a hClass

  have hMixed3 :
      H3Order3VelocityMixedTimeDerivativeOnTail u a T :=
    h3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail
      u T hH3 a hClass

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable
      t htAbs

  exact
    h3OrderEnergyDerivativeIdentities_of_integrable_of_tailLocalInputs
      hH3.navier_stokes
      htAbs
      hInt
      hMixed2
      hMixed3
      hDom

/-! ## Pointwise spatial package from the reduced whole-space frontier -/

/--
Path-specific majorants plus diffusion/pressure whole-space data reconstruct the
pointwise spatial energy package used by the Landau and scalar-energy proofs.
-/
theorem h3PathEnergyClassProducesPointwiseSpatialEnergyData_of_pathMajorants_of_diffusionPressure
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hWhole :
      H3PathEnergyClassProducesDiffusionPressureWholeSpaceEnergyData) :
    H3PathEnergyClassProducesPointwiseSpatialEnergyData := by

  intro u T hH3 a hClass t ht

  rcases
    hMajorants u T hH3 a hClass t ht
  with
    ⟨hMajorant⟩

  rcases
    hWhole u T hH3 a hClass t ht
  with
    ⟨
      hDiffusionPairing,
      hPressurePairing,
      hPressureIBP,
      hDiffusionIBP
    ⟩

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

  have hHigher :
      HigherOrderMomentumRHSSplitsAt
        (logSpaceTimeVectorField u)
        p
        t := by
    dsimp only [p]
    exact
      h3EnergyClassSplitPressureAt_momentumRHSSplits
        hClass ht

  have hPDEPairing :
      H3PDEPairingIntegrableAt
        u p t :=
    h3PDEPairingIntegrableAt_of_majorants_of_diffusion_pressure
      hClass
      ht
      hPDE
      hHigher
      hMajorant
      hDiffusionPairing
      (by
        simpa only [p] using hPressurePairing)

  refine
    ⟨
      p,
      hPDE,
      hHigher,
      hPDEPairing,
      ?_,
      hDiffusionIBP
    ⟩

  simpa only [p] using hPressureIBP

/-! ## Low-frequency kinetic control -/

/--
The zeroth-order physical energy has nonpositive derivative at every strict
path energy-class time under path-majorants and the pointwise spatial package.
-/
theorem deriv_velocityH3Energy0At_nonpos_of_pathMajorants_of_pointwiseSpatial
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesPointwiseSpatialEnergyData)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3Energy0At u) t ≤ 0 := by

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable
      t htAbs

  have hDerivative :
      H3OrderEnergyDerivativeIdentities u t :=
    h3Path_orderEnergyDerivativeIdentities_of_pathMajorants
      hMajorants
      hH3
      hClass
      ht

  rcases
    hSpatial u T hH3 a hClass t ht
  with
    ⟨
      p,
      hPDE,
      hHigher,
      hPairing,
      hPressureIBP,
      hDiffusionIBP
    ⟩

  let h : ℝ → ℝ :=
    fun s =>
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        * velocityH3EnergyAt u s

  have hGradient :
      VelocityGradientEnvelope u h t := by
    intro i j x

    have hBound :=
      norm_loggedVelocityComponent_spatial_d_le_h3Energy
        hClass ht hInt i j x

    change
      abs
        (spatial3.d
          i
          (loggedVelocityComponent u t j)
          x)
        ≤
      h t

    dsimp only [h]

    simpa only [Real.norm_eq_abs] using hBound

  have hTransportIBP :
      H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hInt hGradient

  have hFlux :
      H3TransportEnergyFluxVanishesAt u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts
      hTransportIBP

  have hTransportZero :
      velocityH3TransportDerivative0At u t = 0 :=
    velocityH3TransportDerivative0At_eq_zero_of_energyClass
      hClass ht hFlux

  have hDiv :
      H3DifferentiatedIncompressibilityAt u t :=
    preterminalH3EnergyClass_produces_differentiatedIncompressibility
      hClass ht

  have hPressureZero :
      velocityH3PressureDerivative0At u p t = 0 :=
    velocityH3PressureDerivative0At_eq_zero
      hPressureIBP
      hDiv

  have hDiffusion :
      velocityH3DiffusionDerivative0At u t ≤ 0 :=
    velocityH3DiffusionDerivative0At_nonpos
      hDiffusionIBP

  have hFormalPDE :
      velocityH3FormalDerivative0At u t
        =
      velocityH3PDEDerivative0At u p t :=
    velocityH3FormalDerivative0At_eq_pde
      hPDE
      htAbs

  have hSplit :
      velocityH3PDEDerivative0At u p t
        =
      velocityH3DiffusionDerivative0At u t
        -
      velocityH3TransportDerivative0At u t
        -
      velocityH3PressureDerivative0At u p t :=
    velocityH3PDEDerivative0At_eq_split
      hPairing

  calc
    deriv (velocityH3Energy0At u) t
        =
      velocityH3FormalDerivative0At u t :=
      hDerivative.1.deriv

    _ =
      velocityH3PDEDerivative0At u p t :=
      hFormalPDE

    _ =
      velocityH3DiffusionDerivative0At u t
        -
      velocityH3TransportDerivative0At u t
        -
      velocityH3PressureDerivative0At u p t :=
      hSplit

    _ =
      velocityH3DiffusionDerivative0At u t := by
      rw [hTransportZero, hPressureZero]
      ring

    _ ≤ 0 :=
      hDiffusion

/--
Kinetic energy is antitone on every strict H³-path energy-class tail under
path-specific majorants and pointwise spatial whole-space data.
-/
theorem antitoneOn_velocityH3Energy0At_of_pathMajorants_of_pointwiseSpatial
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesPointwiseSpatialEnergyData)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    AntitoneOn
      (velocityH3Energy0At u)
      (Set.Ioo a T) := by

  have hDifferentiable :
      DifferentiableOn ℝ
        (velocityH3Energy0At u)
        (Set.Ioo a T) := by

    intro t ht

    have hDerivative :
        H3OrderEnergyDerivativeIdentities u t :=
      h3Path_orderEnergyDerivativeIdentities_of_pathMajorants
        hMajorants
        hH3
        hClass
        ht

    exact
      hDerivative.1.differentiableAt.differentiableWithinAt

  refine
    antitoneOn_of_deriv_nonpos
      (convex_Ioo a T)
      hDifferentiable.continuousOn
      (hDifferentiable.mono interior_subset)
      ?_

  intro t htInterior

  exact
    deriv_velocityH3Energy0At_nonpos_of_pathMajorants_of_pointwiseSpatial
      hMajorants
      hSpatial
      hH3
      hClass
      (interior_subset htInterior)

/--
The path-majorant and pointwise spatial packages therefore close the exact
late-tail physical L² input used by the BKM endpoint.
-/
theorem h3PathEnergyClassProducesBKMZerothVelocityL2LateTail_of_pathMajorants_of_pointwiseSpatial
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesPointwiseSpatialEnergyData) :
    H3PathEnergyClassProducesBKMZerothVelocityL2LateTail := by

  intro u T hH3 a hClass b hb

  have hAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_pathMajorants_of_pointwiseSpatial
      hMajorants
      hSpatial
      hH3
      hClass

  have hEnergy :
      BKMKineticEnergyControlledFromAnchor
        u b T := by
    intro t ht

    have htOld :
        t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hb.1 ht.1,
        ht.2
      ⟩

    exact
      hAnti
        hb
        htOld
        (le_of_lt ht.1)

  exact
    ⟨
      Real.sqrt (velocityH3Energy0At u b),
      bkmZerothVelocityL2TailBound_of_kineticEnergyControlledFromAnchor
        hEnergy
    ⟩

/-! ## Canonical H³ gradient growth -/

/--
Canonical H³ differential inequality from path-majorants and pointwise spatial
whole-space data, with no global higher-time hypothesis.
-/
theorem h3GradientGrowthInequalityFrom_h3Path_pathMajorants_pointwiseSpatial
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesPointwiseSpatialEnergyData)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGradient :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VelocityGradientEnvelope u h t) :
    H3GradientGrowthInequalityFrom
      a T h
      (velocityH3EnergyAt u)
      4422 := by

  have hTransport :
      H3TransportControlledOnTail
        u a T h 4422 :=
    h3TransportControlledOnTail_of_h3Path_pointwiseSpatial
      hSpatial
      hH3
      hClass
      hGradient

  intro t ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  have hDerivative :
      H3OrderEnergyDerivativeIdentities u t :=
    h3Path_orderEnergyDerivativeIdentities_of_pathMajorants
      hMajorants
      hH3
      hClass
      ht

  rcases
    hSpatial u T hH3 a hClass t ht
  with
    ⟨
      p,
      hPDE,
      hHigher,
      hPairing,
      hPressureIBP,
      hDiffusionIBP
    ⟩

  have hSplit :
      deriv (velocityH3EnergyAt u) t
        =
      velocityH3DiffusionDerivativeAt u t
        -
      velocityH3TransportDerivativeAt u t
        -
      velocityH3PressureDerivativeAt u p t :=
    deriv_velocityH3EnergyAt_eq_diffusion_sub_transport_sub_pressure
      hPDE
      htAbs
      hDerivative
      hHigher
      hPairing

  have hDiffusion :
      velocityH3DiffusionDerivativeAt u t ≤ 0 :=
    velocityH3DiffusionDerivativeAt_nonpos
      hDiffusionIBP

  have hPressure :
      velocityH3PressureDerivativeAt u p t = 0 :=
    preterminalH3EnergyClass_pressureDerivative_eq_zero
      hClass
      ht
      hPressureIBP

  have hTransportUpper :
      -
        velocityH3TransportDerivativeAt u t
          ≤
        4422
          * (1 + |h t|)
          * velocityH3EnergyAt u t :=
    neg_transport_le_of_commutatorBound
      (hTransport t ht).2

  rw [
    hSplit,
    hPressure
  ]

  linarith

/--
Path-specific derivative majorants plus pointwise spatial data close the
canonical H³ gradient-growth interface.
-/
theorem h3PathEnergyClassProducesCanonicalGradientGrowth_of_pathMajorants_of_pointwiseSpatial
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesPointwiseSpatialEnergyData) :
    H3PathEnergyClassProducesCanonicalGradientGrowth := by

  intro u T hH3 a hClass h hGradient

  exact
    h3GradientGrowthInequalityFrom_h3Path_pathMajorants_pointwiseSpatial
      hMajorants
      hSpatial
      hH3
      hClass
      hGradient

/-! ## Two-frontier BKM closure -/

/--
The current H³-path BKM continuation theorem after closing the mixed-time side,
restricting majorants to actual H³ paths, and reconstructing transport pairing
from the majorants.

Only two independent analytic interfaces remain:

1. path-specific locally uniform integrable H³ derivative majorants;
2. diffusion/pressure whole-space pairing and integration-by-parts data.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_pathMajorants_of_diffusionPressureWholeSpace
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hWhole :
      H3PathEnergyClassProducesDiffusionPressureWholeSpaceEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  have hSpatial :
      H3PathEnergyClassProducesPointwiseSpatialEnergyData :=
    h3PathEnergyClassProducesPointwiseSpatialEnergyData_of_pathMajorants_of_diffusionPressure
      hMajorants
      hWhole

  have hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail :=
    h3PathEnergyClassProducesBKMZerothVelocityL2LateTail_of_pathMajorants_of_pointwiseSpatial
      hMajorants
      hSpatial

  have hGrowth :
      H3PathEnergyClassProducesCanonicalGradientGrowth :=
    h3PathEnergyClassProducesCanonicalGradientGrowth_of_pathMajorants_of_pointwiseSpatial
      hMajorants
      hSpatial

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_energyDynamics
      hLow
      (h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_pathMajorants
        hMajorants)
      hGrowth

end

end Euclidean
end Bridge
end PrimeTensor

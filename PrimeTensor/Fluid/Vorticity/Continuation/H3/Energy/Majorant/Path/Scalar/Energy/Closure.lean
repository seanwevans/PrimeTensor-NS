import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Majorant.Path.Diffusion.Pressure.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Scalar.Frontier

/-!
# Reduce the remaining H³-path spatial frontier to exact scalar energy data

`H3PathPathMajorantsDiffusionPressureClosure` reduced BKM continuation to

* path-specific energy-derivative majorants;
* diffusion/pressure product integrability plus full pressure/diffusion
  integration-by-parts identities.

The second package is stronger than the scalar energy argument actually uses.

The already-developed exact-energy factorization shows that downstream BKM
needs only

* exact orderwise scalar energy derivative identities;
* complete PDE pairing integrability;
* order-zero kinetic dissipation to manufacture the low-frequency tail;
* total H³ pressure cancellation and diffusion nonpositivity.

Path-specific majorants now give the derivative identities directly, while
`H3PathEnergyClassProducesScalarEnergyData` contains exactly the remaining
fixed-time pressure/diffusion consequences:

* diffusion pairing integrability;
* pressure pairing integrability;
* order-zero pressure cancellation;
* order-zero diffusion nonpositivity;
* total H³ pressure cancellation;
* total H³ diffusion nonpositivity.

Thus no pressure-IBP or diffusion-IBP predicate needs to remain in the public
BKM frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathPathMajorantsScalarEnergyClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Exact derivative interface from path majorants -/

/-- Path-specific majorants close the exact order-energy derivative interface. -/
theorem h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_pathMajorants
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesOrderEnergyDerivativeIdentities := by
  intro u T hH3 a hClass t ht

  exact
    h3Path_orderEnergyDerivativeIdentities_of_pathMajorants
      hMajorants
      hH3
      hClass
      ht

/-! ## Exact PDE pairing from path majorants plus scalar product data -/

/--
Path-specific majorants integrate the full momentum RHS pairing.  Hence the
diffusion and pressure pairing families retained by the scalar-energy frontier
reconstruct the complete PDE pairing package.
-/
theorem h3PathEnergyClassProducesPDEPairingIntegrability_of_pathMajorants_of_scalarEnergy
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData) :
    H3PathEnergyClassProducesPDEPairingIntegrability := by
  intro u T hH3 a hClass t ht

  rcases
    hMajorants u T hH3 a hClass t ht
  with
    ⟨hMajorant⟩

  rcases
    hScalar u T hH3 a hClass t ht
  with
    ⟨
      hDiffusionPairing,
      hPressurePairing,
      hPressure0,
      hDiffusion0,
      hPressure,
      hDiffusion
    ⟩

  exact
    h3PDEPairingIntegrableAt_of_majorants_of_diffusion_pressure
      hClass
      ht
      (h3EnergyClassSplitPressureAt_navierStokes
        hClass ht)
      (h3EnergyClassSplitPressureAt_momentumRHSSplits
        hClass ht)
      hMajorant
      hDiffusionPairing
      hPressurePairing

/-- Scalar-energy data projects to the exact full-order sign interface. -/
theorem h3PathEnergyClassProducesFullScalarSigns_of_scalarEnergy
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData) :
    H3PathEnergyClassProducesFullScalarSigns := by
  intro u T hH3 a hClass t ht

  rcases
    hScalar u T hH3 a hClass t ht
  with
    ⟨
      hDiffusionPairing,
      hPressurePairing,
      hPressure0,
      hDiffusion0,
      hPressure,
      hDiffusion
    ⟩

  exact
    ⟨
      hPressure,
      hDiffusion
    ⟩

/-! ## Kinetic low-frequency tail from the scalar order-zero signs -/

/--
At every strict path energy-class time, path-majorant differentiability plus
the scalar order-zero pressure/diffusion signs imply nonincrease of physical
kinetic energy.
-/
theorem deriv_velocityH3Energy0At_nonpos_of_pathMajorants_of_scalarEnergy
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData)
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

  have hH3At :
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

  have hPairing :
      H3PDEPairingIntegrableAt u p t := by
    dsimp only [p]
    exact
      h3PathEnergyClassProducesPDEPairingIntegrability_of_pathMajorants_of_scalarEnergy
        hMajorants
        hScalar
        u T hH3
        a hClass
        t ht

  let h : ℝ → ℝ :=
    fun s =>
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        * velocityH3EnergyAt u s

  have hGradient :
      VelocityGradientEnvelope u h t := by
    intro i j x

    have hBound :=
      norm_loggedVelocityComponent_spatial_d_le_h3Energy
        hClass ht hH3At i j x

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
      hClass ht hH3At hGradient

  have hFlux :
      H3TransportEnergyFluxVanishesAt u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts
      hTransportIBP

  have hTransportZero :
      velocityH3TransportDerivative0At u t = 0 :=
    velocityH3TransportDerivative0At_eq_zero_of_energyClass
      hClass ht hFlux

  rcases
    hScalar u T hH3 a hClass t ht
  with
    ⟨
      hDiffusionPairing,
      hPressurePairing,
      hPressureZero,
      hDiffusionNonpos,
      hPressureTotal,
      hDiffusionTotal
    ⟩

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

  have hPressureZeroP :
      velocityH3PressureDerivative0At u p t = 0 := by
    dsimp only [p]
    exact hPressureZero

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
      rw [hTransportZero, hPressureZeroP]
      ring

    _ ≤ 0 :=
      hDiffusionNonpos

/-- Kinetic energy is antitone on every strict path energy-class tail. -/
theorem antitoneOn_velocityH3Energy0At_of_pathMajorants_of_scalarEnergy
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData)
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
    deriv_velocityH3Energy0At_nonpos_of_pathMajorants_of_scalarEnergy
      hMajorants
      hScalar
      hH3
      hClass
      (interior_subset htInterior)

/--
The scalar order-zero signs therefore manufacture the exact late-tail physical
L² radius required by the BKM endpoint.
-/
theorem h3PathEnergyClassProducesBKMZerothVelocityL2LateTail_of_pathMajorants_of_scalarEnergy
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData) :
    H3PathEnergyClassProducesBKMZerothVelocityL2LateTail := by
  intro u T hH3 a hClass b hb

  have hAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_pathMajorants_of_scalarEnergy
      hMajorants
      hScalar
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

/-! ## Final scalar-energy BKM closure -/

/--
H³-path BKM continuation from the strictly weaker scalar spatial frontier.

The remaining analytic assumptions are now exactly

1. path-specific locally uniform integrable derivative majorants;
2. diffusion and pressure product integrability;
3. order-zero and total pressure/diffusion scalar signs.

No pressure/diffusion integration-by-parts object appears in this theorem.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_pathMajorants_of_scalarEnergy
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  have hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail :=
    h3PathEnergyClassProducesBKMZerothVelocityL2LateTail_of_pathMajorants_of_scalarEnergy
      hMajorants
      hScalar

  have hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities :=
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_pathMajorants
      hMajorants

  have hPairing :
      H3PathEnergyClassProducesPDEPairingIntegrability :=
    h3PathEnergyClassProducesPDEPairingIntegrability_of_pathMajorants_of_scalarEnergy
      hMajorants
      hScalar

  have hSigns :
      H3PathEnergyClassProducesFullScalarSigns :=
    h3PathEnergyClassProducesFullScalarSigns_of_scalarEnergy
      hScalar

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_exactEnergy
      hLow
      hDerivative
      hPairing
      hSigns

/-!
Compatibility: the previous diffusion/pressure IBP frontier implies the new
scalar-energy frontier.
-/
theorem h3PathEnergyClassProducesScalarEnergyData_of_diffusionPressureWholeSpace
    (hWhole :
      H3PathEnergyClassProducesDiffusionPressureWholeSpaceEnergyData) :
    H3PathEnergyClassProducesScalarEnergyData := by
  intro u T hH3 a hClass t ht

  rcases
    hWhole u T hH3 a hClass t ht
  with
    ⟨
      hDiffusionPairing,
      hPressurePairing,
      hPressureIBP,
      hDiffusionIBP
    ⟩

  have hDiv :
      H3DifferentiatedIncompressibilityAt u t :=
    preterminalH3EnergyClass_produces_differentiatedIncompressibility
      hClass ht

  exact
    ⟨
      hDiffusionPairing,
      hPressurePairing,
      velocityH3PressureDerivative0At_eq_zero
        hPressureIBP hDiv,
      velocityH3DiffusionDerivative0At_nonpos
        hDiffusionIBP,
      velocityH3PressureDerivativeAt_eq_zero
        hPressureIBP hDiv,
      velocityH3DiffusionDerivativeAt_nonpos
        hDiffusionIBP
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

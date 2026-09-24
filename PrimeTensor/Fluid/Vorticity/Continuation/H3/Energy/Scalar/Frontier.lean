import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Majorant.Pairing.PDE
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.TopFlux.Automatic

/-!
# Lower the remaining H³ whole-space frontier to scalar energy consequences

The previous H³-path BKM frontier still carried the full pressure and diffusion
integration-by-parts predicates.  Those predicates are stronger than the
actual scalar energy algebra uses.

There are two places where pressure/diffusion signs enter:

* the midpoint kinetic-energy monotonicity argument uses only the order-zero
  pressure cancellation and order-zero diffusion nonpositivity;
* the full H³ growth inequality uses only the total pressure cancellation and
  total diffusion nonpositivity.

The PDE split still requires diffusion and pressure *product integrability*.
`H3PathMajorantPDEPairing` already showed that, once those two product families
are integrable, the energy-derivative majorants recover all transport-product
integrability and hence the full `H3PDEPairingIntegrableAt` package.

This file therefore replaces whole pressure/diffusion IBP by exactly the four
scalar conclusions consumed downstream.

The remaining fixed-time whole-space interface is:

* diffusion pairing integrability;
* pressure pairing integrability;
* order-zero pressure contribution = 0;
* order-zero diffusion contribution ≤ 0;
* total H³ pressure contribution = 0;
* total H³ diffusion contribution ≤ 0.

No pressure-IBP, diffusion-IBP, or transport-IBP predicate appears in the final
H³-path BKM theorem below.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathScalarEnergyFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Exact scalar whole-space frontier -/

/--
The exact fixed-time pressure/diffusion information consumed by the BKM
energy argument.

The pressure is the canonical pointwise split witness already selected from
`PreterminalH3EnergyClass`.
-/
def H3PathEnergyClassProducesScalarEnergyData : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              H3DiffusionPairingIntegrableAt u t
                ∧
              H3PressurePairingIntegrableAt
                u
                (h3EnergyClassSplitPressureAt hClass ht)
                t
                ∧
              velocityH3PressureDerivative0At
                  u
                  (h3EnergyClassSplitPressureAt hClass ht)
                  t
                =
              0
                ∧
              velocityH3DiffusionDerivative0At
                  u t
                ≤
              0
                ∧
              velocityH3PressureDerivativeAt
                  u
                  (h3EnergyClassSplitPressureAt hClass ht)
                  t
                =
              0
                ∧
              velocityH3DiffusionDerivativeAt
                  u t
                ≤
              0

/-! ## Recover the full PDE pairing package -/

/--
The derivative majorants plus the two retained product-integrability families
recover the complete PDE pairing package at one strict tail time.
-/
theorem h3PDEPairingIntegrableAt_of_majorants_of_scalarEnergyData
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    H3PDEPairingIntegrableAt
      u
      (h3EnergyClassSplitPressureAt hClass ht)
      t := by

  rcases
    hMajorants u a T hClass t ht
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

/-! ## Transport closure needs only the recovered PDE pairing -/

/--
Landau transport control on an H³ path using the PDE pairing package recovered
from derivative majorants and scalar-energy data.

No pressure or diffusion IBP hypothesis is used.
-/
theorem h3TransportControlledOnTail_of_h3Path_scalarEnergyData
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGradient :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VelocityGradientEnvelope u h t) :
    H3TransportControlledOnTail
      u a T h 4422 := by

  have hSobolev6 :
      WholeSpaceC1H1ToL6 :=
    wholeSpaceC1H1ToL6_of_fderiv
      wholeSpaceC1FDerivL2ToL6_cutoff

  have hSobolev :
      WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6
      hSobolev6

  intro t ht

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

  have hGradientAt :
      VelocityGradientEnvelope u h t :=
    hGradient t ht

  have hIBP0 :
      H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradientAt

  have hIBP1 :
      H3FirstDerivativeTransportIntegrationByPartsAt u t :=
    h3FirstDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradientAt

  have hIBP2 :
      H3SecondDerivativeTransportIntegrationByPartsAt u t :=
    h3SecondDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradientAt

  have hFlux0 :
      H3TransportEnergyFluxVanishesAt u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts
      hIBP0

  have hFlux1 :
      H3FirstDerivativeTransportFluxVanishesAt u t :=
    h3FirstDerivativeTransportFluxVanishesAt_of_integrationByParts
      hIBP1

  have hPurePairing1 :
      H3OrderOnePureTransportPairingIntegrableAt u t :=
    h3OrderOnePureTransportPairingIntegrableAt_of_integrationByParts
      hClass ht hIBP1

  have hFlux2 :
      H3SecondDerivativeTransportFluxVanishesAt u t :=
    h3SecondDerivativeTransportFluxVanishesAt_of_integrationByParts
      hIBP2

  have hPurePairing2 :
      H3OrderTwoPureTransportPairingIntegrableAt u t :=
    h3OrderTwoPureTransportPairingIntegrableAt_of_integrationByParts
      hClass ht hIBP2

  have hAnalyticCore3 :
      H3OrderThreeInterpolationLandauCoreAnalyticDataAt
        u h t := by
    simpa [
      H3OrderThreeInterpolationLandauCoreAnalyticDataAt
    ] using
      hGradientAt

  have hAnalytic3 :
      H3OrderThreeInterpolationLandauAnalyticDataAt
        u h t :=
    h3OrderThreeInterpolationLandauAnalyticDataAt_of_core
      hSobolev
      wholeSpaceQuarticDerivativeIntegrationByParts_cutoff
      hClass
      ht
      hH3At
      hAnalyticCore3

  have hPairing1 :
      H3OrderOneTransportPairingIntegrableAt u t :=
    h3OrderOneTransportPairingIntegrableAt_of_pure
      hClass
      ht
      hH3At
      hGradientAt
      hPurePairing1

  have hPairing2 :
      H3OrderTwoTransportPairingIntegrableAt u t :=
    h3OrderTwoTransportPairingIntegrableAt_of_pure
      hClass
      ht
      hH3At
      hGradientAt
      hPurePairing2

  have hRegular3 :
      H3OrderThreeTransportRegularityAt u t :=
    h3OrderThreeTransportRegularityAt_of_energyClass
      hClass ht

  have hGradientPairing3 :
      H3OrderThreeGradientPairingIntegrableAt u t :=
    h3OrderThreeGradientPairingIntegrableAt_of_energyClass
      hClass
      ht
      hH3At
      hGradientAt

  have hMonomialPairing3 :
      H3OrderThreeInterpolationMonomialPairingIntegrableAt u t :=
    h3OrderThreeInterpolationMonomialPairingIntegrableAt_of_landauAnalyticData
      hAnalytic3

  have hInterpolationPairing3 :
      H3OrderThreeInterpolationPairingIntegrableAt u t :=
    h3OrderThreeInterpolationPairingIntegrableAt_of_monomials
      hMonomialPairing3

  have hPDEPairing :
      H3PDEPairingIntegrableAt
        u
        (h3EnergyClassSplitPressureAt hClass ht)
        t :=
    h3PDEPairingIntegrableAt_of_majorants_of_scalarEnergyData
      hMajorants
      hScalar
      hH3
      hClass
      ht

  have hFlux3 :
      H3ThirdDerivativeTransportFluxVanishesAt u t :=
    h3ThirdDerivativeTransportFluxVanishesAt_of_pde
      hClass
      ht
      hH3At
      hPDEPairing
      hGradientPairing3
      hInterpolationPairing3

  have hPairing3 :
      H3OrderThreeTransportPairingIntegrableAt u t :=
    h3OrderThreeTransportPairingIntegrableAt_of_pde
      hClass
      ht
      hPDEPairing
      hGradientPairing3
      hInterpolationPairing3

  have hTransport :
      H3TransportCommutatorBoundAt
        u h 4422 t :=
    h3TransportCommutatorBoundAt_of_landauAnalyticData
      hClass
      ht
      hFlux0
      hFlux1
      hPairing1
      hFlux2
      hPairing2
      hRegular3
      hFlux3
      hPairing3
      hGradientPairing3
      hH3At
      hAnalytic3

  exact
    ⟨
      hGradientAt,
      hTransport
    ⟩

/-! ## Kinetic midpoint control from scalar signs -/

/--
Order-zero kinetic dissipation at one strict tail time, using only the scalar
order-zero pressure/diffusion conclusions.
-/
theorem deriv_velocityH3Energy0At_nonpos_of_h3Path_scalarEnergyData
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
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
    h3Path_orderEnergyDerivativeIdentities_of_pdeTime_of_majorants
      hTime
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
      h3PDEPairingIntegrableAt_of_majorants_of_scalarEnergyData
        hMajorants
        hScalar
        hH3
        hClass
        ht

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
      hPDE htAbs

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

theorem antitoneOn_velocityH3Energy0At_of_h3Path_scalarEnergyData
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
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
      h3Path_orderEnergyDerivativeIdentities_of_pdeTime_of_majorants
        hTime
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
    deriv_velocityH3Energy0At_nonpos_of_h3Path_scalarEnergyData
      hTime
      hMajorants
      hScalar
      hH3
      hClass
      (interior_subset htInterior)

theorem bkmKineticEnergyControlledFromAnchor_midpoint_of_h3Path_scalarEnergyData
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    BKMKineticEnergyControlledFromAnchor
      u
      (h3BKMKineticTailMidpoint a T)
      T := by

  have hAnti :=
    antitoneOn_velocityH3Energy0At_of_h3Path_scalarEnergyData
      hTime
      hMajorants
      hScalar
      hH3
      hClass

  have hMid :
      h3BKMKineticTailMidpoint a T
        ∈ Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo
      hClass.terminal_start.2

  intro t ht

  have htOld :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hMid.1 ht.1,
      ht.2
    ⟩

  exact
    hAnti
      hMid
      htOld
      (le_of_lt ht.1)

/-! ## Full H³ growth from scalar signs -/

/--
Canonical H³ differential inequality using only scalar pressure cancellation
and diffusion nonpositivity, rather than full pressure/diffusion IBP packages.
-/
theorem h3GradientGrowthInequalityFrom_h3Path_scalarEnergyData
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData)
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
    h3TransportControlledOnTail_of_h3Path_scalarEnergyData
      hMajorants
      hScalar
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
    h3Path_orderEnergyDerivativeIdentities_of_pdeTime_of_majorants
      hTime
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

  have hHigher :
      HigherOrderMomentumRHSSplitsAt
        (logSpaceTimeVectorField u)
        p
        t := by
    dsimp only [p]
    exact
      h3EnergyClassSplitPressureAt_momentumRHSSplits
        hClass ht

  have hPairing :
      H3PDEPairingIntegrableAt u p t := by
    dsimp only [p]
    exact
      h3PDEPairingIntegrableAt_of_majorants_of_scalarEnergyData
        hMajorants
        hScalar
        hH3
        hClass
        ht

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

  rcases
    hScalar u T hH3 a hClass t ht
  with
    ⟨
      hDiffusionPairing,
      hPressurePairing,
      hPressure0,
      hDiffusion0,
      hPressureZero,
      hDiffusionNonpos
    ⟩

  have hPressureZeroP :
      velocityH3PressureDerivativeAt u p t = 0 := by
    dsimp only [p]
    exact hPressureZero

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
    hPressureZeroP
  ]

  linarith

/-! ## Final BKM closure -/

theorem h3PathVorticityL1LinfProducesH3Control_of_pdeTime_of_majorants_of_scalarEnergy
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData) :
    H3PathVorticityL1LinfProducesH3Control := by

  intro u T hH3 hControl

  rcases hControl with
    ⟨g, hgIntegrable, hgEnvelope⟩

  obtain
    ⟨a, hClass⟩ :=
    h3Preterminal_energyClass_of_h3PathAdmissible
      hH3

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hbOld :
      b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        ha.2

  have hb :
      b ∈ Set.Ioo (0 : ℝ) T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo_zero
        ha

  have hClassB :
      PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hbOld.1)
      hbOld.2

  have hgTail :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          VorticityEnvelope u g t := by

    intro t ht

    exact
      hgEnvelope
        t
        ⟨
          lt_trans hb.1 ht.1,
          ht.2
        ⟩

  have hProfile :
      H3EnergyProfileFrom
        u b T
        (velocityH3EnergyAt u) :=
    h3EnergyProfileFrom_h3Path
      hH3 hb

  have hKinetic :
      BKMKineticEnergyControlledFromAnchor
        u b T := by

    dsimp only [b]

    exact
      bkmKineticEnergyControlledFromAnchor_midpoint_of_h3Path_scalarEnergyData
        hTime
        hMajorants
        hScalar
        hH3
        hClass

  have hActual :
      ActualVelocityGradientLogBoundFrom
        u b T g
        (velocityH3EnergyAt u)
        (h3BKMCanonicalSelectedLogGradientConstant
          (Real.sqrt
            (velocityH3Energy0At u b))) :=
    actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_kineticEnergyControlledFromAnchor
      hH3.navier_stokes
      hb
      hgTail
      hProfile
      hKinetic

  let B : ℝ :=
    h3BKMCanonicalSelectedLogGradientConstant
      (Real.sqrt
        (velocityH3Energy0At u b))

  have hB :
      0 ≤ B := by
    dsimp only [B]
    exact
      h3BKMCanonicalSelectedLogGradientConstant_nonneg
        (Real.sqrt_nonneg _)

  let h : ℝ → ℝ :=
    h3BKMLogarithmicGradientEnvelope
      g
      (velocityH3EnergyAt u)
      B

  have hGradient :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          VelocityGradientEnvelope u h t := by

    intro t ht

    dsimp only [h, B]

    exact
      velocityGradientEnvelope_h3BKMLogarithmicGradientEnvelope
        hActual
        ht

  have hEndpointBound :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          1 + |h t|
            ≤
          (B + 1)
            * (1 + |g t|)
            * (1 + Real.log (velocityH3EnergyAt u t)) := by

    intro t ht

    have hEt :
        1 ≤ velocityH3EnergyAt u t :=
      (hProfile
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    dsimp only [h]

    exact
      one_add_abs_h3BKMLogarithmicGradientEnvelope_le
        hB
        hEt

  have hEnergyGrowth :
      H3GradientGrowthInequalityFrom
        b T h
        (velocityH3EnergyAt u)
        4422 :=
    h3GradientGrowthInequalityFrom_h3Path_scalarEnergyData
      hTime
      hMajorants
      hScalar
      hH3
      hClassB
      hGradient

  let C : ℝ :=
    4422 * (B + 1)

  have hC :
      0 ≤ C := by
    dsimp only [C]
    exact
      mul_nonneg
        (by norm_num)
        (by linarith)

  have hGrowth :
      BKMLogGrowthInequalityFrom
        b T g
        (velocityH3EnergyAt u)
        C := by

    intro t ht

    have hEtOne :
        1 ≤ velocityH3EnergyAt u t :=
      (hProfile
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    have hEtNonneg :
        0 ≤ velocityH3EnergyAt u t :=
      le_trans
        (by norm_num)
        hEtOne

    have hEndpointAt :
        1 + |h t|
          ≤
        (B + 1)
          * (1 + |g t|)
          * (1 + Real.log (velocityH3EnergyAt u t)) :=
      hEndpointBound t ht

    calc
      deriv (velocityH3EnergyAt u) t
          ≤
        4422
          * (1 + |h t|)
          * velocityH3EnergyAt u t :=
        hEnergyGrowth t ht

      _ ≤
        4422
          *
        ((B + 1)
          * (1 + |g t|)
          * (1 + Real.log (velocityH3EnergyAt u t)))
          * velocityH3EnergyAt u t := by

        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              hEndpointAt
              (by norm_num))
            hEtNonneg

      _ =
        C
          * (1 + |g t|)
          * velocityH3EnergyAt u t
          * (1 + Real.log (velocityH3EnergyAt u t)) := by

        dsimp only [C]
        ring

  have hgTailIntegrable :
      MeasureTheory.IntegrableOn
        g
        (Set.Ioo b T) := by

    apply
      hgIntegrable.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hb.1 ht.1,
        ht.2
      ⟩

  have hEOne :
      ∀ t : ℝ,
        t ∈ Set.Ico b T →
          1 ≤ velocityH3EnergyAt u t := by

    intro t ht

    exact
      (hProfile t ht).1

  have hContinuous :
      ∀ q : ℝ,
        q ∈ Set.Ico b T →
          ContinuousOn
            (velocityH3EnergyAt u)
            (Set.Icc b q) :=
    hH3.canonicalH3EnergyContinuousOnTail
      hb

  have hDerivative :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          HasDerivAt
            (velocityH3EnergyAt u)
            (deriv (velocityH3EnergyAt u) s)
            s := by

    intro s hs

    have hIds :
        H3OrderEnergyDerivativeIdentities u s :=
      h3Path_orderEnergyDerivativeIdentities_of_pdeTime_of_majorants
        hTime
        hMajorants
        hH3
        hClassB
        hs

    have hDeriv :
        deriv (velocityH3EnergyAt u) s
          =
        velocityH3FormalDerivativeAt u s :=
      deriv_velocityH3EnergyAt
        hIds

    rw [hDeriv]

    exact
      hasDerivAt_velocityH3EnergyAt
        hIds

  obtain
    ⟨M, hM, hEM⟩ :=
    logarithmicGronwallClosesEnergy_of_continuous_of_hasDeriv
      hb.2
      hgTailIntegrable
      hC
      hEOne
      hContinuous
      hDerivative
      hGrowth

  refine
    ⟨
      b,
      M,
      hb,
      hM,
      ?_
    ⟩

  intro t ht

  exact
    velocityH3BoundAt_mono
      (hProfile t ht).2
      (hEM t ht)

/--
H³-path BKM continuation at the exact scalar energy frontier.

The remaining explicit interfaces are now:

1. higher PDE time differentiability;
2. locally uniform integrable energy-derivative majorants;
3. diffusion pairing integrability;
4. pressure pairing integrability;
5. order-zero pressure cancellation;
6. order-zero diffusion nonpositivity;
7. total H³ pressure cancellation;
8. total H³ diffusion nonpositivity.

Items 3--8 are grouped in `H3PathEnergyClassProducesScalarEnergyData`.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_pdeTime_of_majorants_of_scalarEnergy
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  intro u T hH3 hControl

  have hTail :
      TerminalTailH3Control u T :=
    h3PathVorticityL1LinfProducesH3Control_of_pdeTime_of_majorants_of_scalarEnergy
      hTime
      hMajorants
      hScalar
      u T
      hH3
      hControl

  exact
    h3PathH3ControlProducesExtension
      u T
      hH3
      hTail

end

end Euclidean
end Bridge
end PrimeTensor

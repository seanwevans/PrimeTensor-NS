import PrimeTensor.Fluid.Vorticity.Continuation.H3.Analysis.Frontier.Split
import PrimeTensor.Fluid.Vorticity.H3.Energy.Class.Split.Regularity

/-!
# Pointwise H³-path energy frontier

`H3PathAnalyticFrontierSplit` still reconstructed the historical package

    H3EnergyEstimateAnalyticOnTail

before invoking the BKM argument.  That package imposes two pieces of
bookkeeping which the actual differential inequality does not need:

* one pressure witness fixed for the entire tail;
* `HigherOrderMomentumSplitRegularityAt`, although the energy algebra consumes
  only the resulting `HigherOrderMomentumRHSSplitsAt` equalities.

The canonical energy derivative is pointwise in time.  At each strict tail
time it is enough to choose a pressure witness for that time and provide

* the exact higher-order momentum RHS splits;
* PDE pairing integrability;
* pressure integration by parts;
* diffusion integration by parts.

The pressure witness may therefore vary with the time at which the estimate is
proved.

This file rebuilds the H³-path BKM argument directly at that lower layer.
The time-differentiation side continues to use the already-reduced PDE-time
derivative + locally uniform majorant machinery.

The remaining spatial frontier is consequently weaker and more literal than
`H3EnergyEstimateAnalyticOnTail`: it contains exactly the fixed-time
whole-space data consumed by the scalar energy decomposition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathPointwiseEnergyFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Pointwise spatial frontier -/

/--
Exact fixed-time spatial data needed by the canonical H³ energy identity.

No common pressure witness across different times is required, and no
`SpatialC1` momentum-split regularity is retained: only the resulting exact
higher-order split equalities appear.
-/
def H3PathEnergyClassProducesPointwiseSpatialEnergyData : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              ∃ p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three,
                PreterminalNavierStokes3
                    (logSpaceTimeVectorField u)
                    p
                    T
                  ∧
                HigherOrderMomentumRHSSplitsAt
                    (logSpaceTimeVectorField u)
                    p
                    t
                  ∧
                H3PDEPairingIntegrableAt
                    u p t
                  ∧
                H3PressureIntegrationByPartsAt
                    u p t
                  ∧
                H3DiffusionIntegrationByPartsAt
                    u t

/-! ## Derivative identities from the already-reduced time frontier -/

/--
The existing PDE-time + majorant frontiers give the exact four energy
derivative identities at every strict H³-path energy-class time.
-/
theorem h3Path_orderEnergyDerivativeIdentities_of_pdeTime_of_majorants
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    H3OrderEnergyDerivativeIdentities u t := by

  have hReduced :
      EnergyClassProducesH3EnergyDerivativeReducedDomination :=
    energyClassProducesH3EnergyDerivativeReducedDomination_of_majorants
      hMajorants

  have hDom :
      EnergyClassProducesH3EnergyDerivativeTailLocalDomination :=
    energyClassProducesH3EnergyDerivativeTailLocalDomination_of_reduced
      hReduced

  have hInputs :
      EnergyClassProducesH3EnergyDerivativeTailLocalInputs :=
    energyClassProducesH3EnergyDerivativeTailLocalInputs_of_pde_of_domination
      hTime
      hDom

  rcases
    hInputs u a T hClass
  with
    ⟨hMixed2, hMixed3, hLocalDom⟩

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_trans hClass.terminal_start.1 ht.1,
        ht.2
      ⟩

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable
      t htAbs

  rcases hLocalDom t ht with
    ⟨hDomAt⟩

  exact
    h3OrderEnergyDerivativeIdentities_of_integrable_of_tailLocalInputs
      hH3.navier_stokes
      htAbs
      hInt
      hMixed2
      hMixed3
      hDomAt

/-! ## Kinetic-energy monotonicity from pointwise spatial data -/

/--
Order-zero dissipation at one strict tail time using only pointwise spatial
energy data.
-/
theorem deriv_velocityH3Energy0At_nonpos_of_h3Path_pointwiseSpatial
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesPointwiseSpatialEnergyData)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3Energy0At u) t ≤ 0 := by

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T := by
    exact
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
    h3Path_orderEnergyDerivativeIdentities_of_pdeTime_of_majorants
      hTime
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
Kinetic energy is antitone on the strict high-order tail under the pointwise
spatial frontier.
-/
theorem antitoneOn_velocityH3Energy0At_of_h3Path_pointwiseSpatial
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
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
    deriv_velocityH3Energy0At_nonpos_of_h3Path_pointwiseSpatial
      hTime
      hMajorants
      hSpatial
      hH3
      hClass
      (interior_subset htInterior)

/--
Midpoint kinetic anchor control at the pointwise spatial frontier.
-/
theorem bkmKineticEnergyControlledFromAnchor_midpoint_of_h3Path_pointwiseSpatial
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesPointwiseSpatialEnergyData)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    BKMKineticEnergyControlledFromAnchor
      u
      (h3BKMKineticTailMidpoint a T)
      T := by

  have hAnti :=
    antitoneOn_velocityH3Energy0At_of_h3Path_pointwiseSpatial
      hTime
      hMajorants
      hSpatial
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

/-! ## Transport control from pointwise PDE pairing data -/

/--
The Landau transport estimate needs from the pointwise spatial frontier only
PDE pairing integrability.  The pressure used for this auxiliary pairing may
vary with time.
-/
theorem h3TransportControlledOnTail_of_h3Path_pointwiseSpatial
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
      t ∈ Set.Ioo (0 : ℝ) T := by
    exact
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

  rcases
    hSpatial u T hH3 a hClass t ht
  with
    ⟨
      pEnergy,
      hPDE,
      hHigher,
      hPDEPairing,
      hPressureIBP,
      hDiffusionIBP
    ⟩

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

/-! ## Pointwise canonical H³ growth -/

/--
Canonical H³ differential inequality using only pointwise spatial energy data.
-/
theorem h3GradientGrowthInequalityFrom_h3Path_pointwiseSpatial
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
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
      t ∈ Set.Ioo (0 : ℝ) T := by
    exact
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

/-! ## BKM control and continuation -/

/--
Terminal H³ control from the pointwise spatial frontier.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_pdeTime_of_majorants_of_pointwiseSpatial
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesPointwiseSpatialEnergyData) :
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
      bkmKineticEnergyControlledFromAnchor_midpoint_of_h3Path_pointwiseSpatial
        hTime
        hMajorants
        hSpatial
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
    h3GradientGrowthInequalityFrom_h3Path_pointwiseSpatial
      hTime
      hMajorants
      hSpatial
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
H³-path BKM continuation at the pointwise energy frontier.

Compared with the previous analytic-tail theorem, this statement no longer
assumes a globally coordinated pressure witness or momentum-split
`SpatialC1` regularity.  The spatial assumption contains only exact fixed-time
RHS splits and the whole-space integrability/IBP facts consumed by the energy
identity.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_pdeTime_of_majorants_of_pointwiseSpatial
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesPointwiseSpatialEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  intro u T hH3 hControl

  have hTail :
      TerminalTailH3Control u T :=
    h3PathVorticityL1LinfProducesH3Control_of_pdeTime_of_majorants_of_pointwiseSpatial
      hTime
      hMajorants
      hSpatial
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

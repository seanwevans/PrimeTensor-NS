import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Tail.Low.Scalar.Full.Frontier

/-!
# Exact H³-path energy frontier consumed by BKM

The preceding reductions still exposed implementation-level analytic
machinery at the final BKM theorem:

* higher mixed PDE-time derivative records;
* locally uniform derivative-majorant records;
* separate diffusion and pressure product-integrability records.

Those are useful sufficient mechanisms, but they are not what the BKM energy
argument itself consumes.

At one strict H³-path energy-class time, the downstream proof needs only:

1. the four orderwise scalar energy derivative identities;
2. the complete PDE pairing-integrability package for the canonical split
   pressure;
3. total H³ pressure cancellation;
4. total H³ diffusion nonpositivity.

The low-frequency physical `L²` tail remains a separate BKM endpoint input.

This file makes those exact facts the public frontier.  In particular, the
final theorem below no longer mentions

    EnergyClassProducesH3HigherTimeDerivativePDEOnTail

or

    EnergyClassProducesH3EnergyDerivativeMajorants.

Compatibility theorems show that the previous PDE-time/majorant/full-scalar
frontier implies the new exact one.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathExactEnergyFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Exact path-specific analytic interfaces -/

/--
The exact differentiation-under-the-integral conclusion consumed by BKM.
-/
def H3PathEnergyClassProducesOrderEnergyDerivativeIdentities : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              H3OrderEnergyDerivativeIdentities u t

/--
The exact fixed-time PDE triplet integrability consumed by the energy split
and top-order transport closure.
-/
def H3PathEnergyClassProducesPDEPairingIntegrability : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              H3PDEPairingIntegrableAt
                u
                (h3EnergyClassSplitPressureAt hClass ht)
                t

/--
The only scalar pressure/diffusion conclusions used by the full H³ growth
inequality.
-/
def H3PathEnergyClassProducesFullScalarSigns : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
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

/-! ## Compatibility with the previous frontier -/

/--
The previous PDE-time + majorant route implies the exact derivative-identity
frontier.
-/
theorem h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_pdeTime_of_majorants
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesOrderEnergyDerivativeIdentities := by

  intro u T hH3 a hClass t ht

  exact
    h3Path_orderEnergyDerivativeIdentities_of_pdeTime_of_majorants
      hTime
      hMajorants
      hH3
      hClass
      ht

/--
The previous majorant + diffusion/pressure product route implies the exact PDE
pairing frontier.
-/
theorem h3PathEnergyClassProducesPDEPairingIntegrability_of_majorants_of_fullScalarEnergy
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathEnergyClassProducesPDEPairingIntegrability := by

  intro u T hH3 a hClass t ht

  exact
    h3PDEPairingIntegrableAt_of_majorants_of_fullScalarEnergyData
      hMajorants
      hFull
      hH3
      hClass
      ht

/--
The previous full scalar package implies the exact two scalar signs.
-/
theorem h3PathEnergyClassProducesFullScalarSigns_of_fullScalarEnergy
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathEnergyClassProducesFullScalarSigns := by

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
    ⟨
      hPressure,
      hDiffusion
    ⟩

/-! ## Transport closure from exact PDE pairing data -/

/--
The Landau transport estimate needs no majorant record once complete PDE
pairing integrability is available pointwise.
-/
theorem h3TransportControlledOnTail_of_h3Path_exactPDEPairing
    (hPairing :
      H3PathEnergyClassProducesPDEPairingIntegrability)
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
    hPairing
      u T hH3
      a hClass
      t ht

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

/-! ## Full H³ differential inequality from exact inputs -/

/--
The full H³ growth inequality consumes only derivative identities, complete PDE
pairing integrability, and the two scalar pressure/diffusion signs.
-/
theorem h3GradientGrowthInequalityFrom_h3Path_exactEnergy
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hPairing :
      H3PathEnergyClassProducesPDEPairingIntegrability)
    (hSigns :
      H3PathEnergyClassProducesFullScalarSigns)
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
    h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      hPairing
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

  have hDerivativeAt :
      H3OrderEnergyDerivativeIdentities u t :=
    hDerivative
      u T hH3
      a hClass
      t ht

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
      H3PDEPairingIntegrableAt u p t := by
    dsimp only [p]
    exact
      hPairing
        u T hH3
        a hClass
        t ht

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
      hDerivativeAt
      hHigher
      hPDEPairing

  rcases
    hSigns
      u T hH3
      a hClass
      t ht
  with
    ⟨hPressureZero, hDiffusionNonpos⟩

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

/-! ## BKM closure at the exact energy frontier -/

/--
Terminal H³ control from the exact path-specific energy facts.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_lowTail_of_exactEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hPairing :
      H3PathEnergyClassProducesPDEPairingIntegrability)
    (hSigns :
      H3PathEnergyClassProducesFullScalarSigns) :
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

  obtain
    ⟨L, hLowB⟩ :=
    hLow
      u T hH3
      a hClass
      b hbOld

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

  have hActual :
      ActualVelocityGradientLogBoundFrom
        u b T g
        (velocityH3EnergyAt u)
        (h3BKMCanonicalSelectedLogGradientConstant L) :=
    actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_lowTail
      hH3.navier_stokes
      hb
      hgTail
      hProfile
      hLowB

  let B : ℝ :=
    h3BKMCanonicalSelectedLogGradientConstant L

  have hB :
      0 ≤ B := by
    dsimp only [B]
    exact
      h3BKMCanonicalSelectedLogGradientConstant_nonneg_of_lowTail
        hLowB

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
    h3GradientGrowthInequalityFrom_h3Path_exactEnergy
      hDerivative
      hPairing
      hSigns
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

  have hDerivativeAt :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          HasDerivAt
            (velocityH3EnergyAt u)
            (deriv (velocityH3EnergyAt u) s)
            s := by

    intro s hs

    have hIds :
        H3OrderEnergyDerivativeIdentities u s :=
      hDerivative
        u T hH3
        b hClassB
        s hs

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
      hDerivativeAt
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
H³-path BKM continuation at the exact energy frontier.

The remaining public analytic interfaces are now:

1. a uniform zeroth-order physical `L²` radius on each strict later tail;
2. the four scalar H³ order-energy derivative identities;
3. complete fixed-time PDE pairing integrability;
4. total H³ pressure cancellation;
5. total H³ diffusion nonpositivity.

The mixed-time PDE and majorant packages remain available as sufficient
mechanisms through the compatibility theorems above, but are no longer part of
this theorem's statement.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_exactEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hPairing :
      H3PathEnergyClassProducesPDEPairingIntegrability)
    (hSigns :
      H3PathEnergyClassProducesFullScalarSigns) :
    H3PathVorticityL1LinfProducesExtension := by

  intro u T hH3 hControl

  have hTail :
      TerminalTailH3Control u T :=
    h3PathVorticityL1LinfProducesH3Control_of_lowTail_of_exactEnergy
      hLow
      hDerivative
      hPairing
      hSigns
      u T
      hH3
      hControl

  exact
    h3PathH3ControlProducesExtension
      u T
      hH3
      hTail

/--
Backwards-compatible closure from the previous low-tail + PDE-time + majorant
+ full-scalar frontier through the exact energy interfaces.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_pdeTime_of_majorants_of_fullScalarEnergy_via_exact
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_exactEnergy
      hLow
      (h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_pdeTime_of_majorants
        hTime
        hMajorants)
      (h3PathEnergyClassProducesPDEPairingIntegrability_of_majorants_of_fullScalarEnergy
        hMajorants
        hFull)
      (h3PathEnergyClassProducesFullScalarSigns_of_fullScalarEnergy
        hFull)

end

end Euclidean
end Bridge
end PrimeTensor

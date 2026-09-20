import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathScalarEnergyFrontier

/-!
# Separate the BKM low-frequency tail from full H³ scalar energy analysis

`H3PathScalarEnergyFrontier` still grouped two logically different roles:

* order-zero pressure/diffusion signs were used only to manufacture the
  time-independent physical `L²` low-frequency radius required by the BKM
  logarithmic endpoint;
* the full H³ pressure cancellation and diffusion sign were used in the
  actual H³ differential inequality.

The BKM endpoint itself does not require kinetic-energy monotonicity.  It
requires only a `BKMZerothVelocityL2TailBound`.

This file therefore separates the low-frequency datum from the full H³ scalar
energy datum.

The new interfaces are:

    H3PathEnergyClassProducesBKMZerothVelocityL2LateTail

and

    H3PathEnergyClassProducesFullScalarEnergyData.

The first says that every strict later subtail of an H³ energy class admits
some time-independent zeroth-order physical `L²` radius.  No mechanism for
producing that radius is imposed.

The second retains exactly the full-order whole-space information needed by
the H³ growth estimate:

* diffusion product integrability;
* pressure product integrability;
* total H³ pressure contribution = 0;
* total H³ diffusion contribution ≤ 0.

Consequently the final BKM theorem below no longer assumes order-zero pressure
cancellation or order-zero diffusion nonpositivity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathLowTailFullScalarFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Minimal low-frequency BKM input -/

/--
Every strict later subtail admits a time-independent zeroth-order physical
`L²` radius.

The later anchor is explicit because the H³ path is only assumed on strict
preterminal times.
-/
def H3PathEnergyClassProducesBKMZerothVelocityL2LateTail : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
          ∀ b : ℝ,
            b ∈ Set.Ioo a T →
              ∃ L : ℝ,
                BKMZerothVelocityL2TailBound
                  u b T L

/--
The previous scalar-energy package implies the separated low-frequency input.

This theorem is only a backwards-compatibility bridge.  The new BKM theorem
below consumes the low-tail statement directly.
-/
theorem h3PathEnergyClassProducesBKMZerothVelocityL2LateTail_of_scalarEnergy
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData) :
    H3PathEnergyClassProducesBKMZerothVelocityL2LateTail := by

  intro u T hH3 a hClass b hb

  have hAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_scalarEnergyData
      hTime
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

/-! ## Full H³ scalar whole-space input -/

/--
The fixed-time whole-space data needed only by the full H³ differential
inequality.

Order-zero pressure/diffusion signs are intentionally absent.
-/
def H3PathEnergyClassProducesFullScalarEnergyData : Prop :=
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

/--
The previous six-field scalar-energy package implies the new full-order
package by projection.
-/
theorem h3PathEnergyClassProducesFullScalarEnergyData_of_scalarEnergy
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData) :
    H3PathEnergyClassProducesFullScalarEnergyData := by

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
      hDiffusionPairing,
      hPressurePairing,
      hPressure,
      hDiffusion
    ⟩

/-! ## Recover complete PDE pairing integrability -/

/--
Derivative majorants plus the two full-order product families reconstruct the
complete PDE pairing package.
-/
theorem h3PDEPairingIntegrableAt_of_majorants_of_fullScalarEnergyData
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData)
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
    hFull u T hH3 a hClass t ht
  with
    ⟨
      hDiffusionPairing,
      hPressurePairing,
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

/-! ## Transport closure from the full-order package -/

/--
The Landau transport estimate uses only the recovered PDE pairing package,
H³ integrability, and the gradient envelope.
-/
theorem h3TransportControlledOnTail_of_h3Path_fullScalarEnergyData
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData)
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
    h3PDEPairingIntegrableAt_of_majorants_of_fullScalarEnergyData
      hMajorants
      hFull
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

/-! ## Full H³ growth -/

/--
Canonical H³ differential inequality using the full-order scalar pressure and
diffusion conclusions.
-/
theorem h3GradientGrowthInequalityFrom_h3Path_fullScalarEnergyData
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData)
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
    h3TransportControlledOnTail_of_h3Path_fullScalarEnergyData
      hMajorants
      hFull
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
      h3PDEPairingIntegrableAt_of_majorants_of_fullScalarEnergyData
        hMajorants
        hFull
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
    hFull u T hH3 a hClass t ht
  with
    ⟨
      hDiffusionPairing,
      hPressurePairing,
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

/-! ## BKM closure with the low-frequency datum separated -/

/--
Terminal H³ control from the exact BKM low-frequency input plus the full-order
H³ energy-analysis interfaces.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_lowTail_of_pdeTime_of_majorants_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
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
    h3GradientGrowthInequalityFrom_h3Path_fullScalarEnergyData
      hTime
      hMajorants
      hFull
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
H³-path BKM continuation with the low-frequency tail completely separated
from the full H³ energy analysis.

The remaining explicit interfaces are:

1. a time-independent zeroth-order physical `L²` radius on every strict later
   H³ energy-class tail;
2. higher PDE time differentiability;
3. locally uniform integrable energy-derivative majorants;
4. diffusion pairing integrability;
5. pressure pairing integrability;
6. total H³ pressure cancellation;
7. total H³ diffusion nonpositivity.

Items 4--7 are grouped by
`H3PathEnergyClassProducesFullScalarEnergyData`.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_pdeTime_of_majorants_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  intro u T hH3 hControl

  have hTail :
      TerminalTailH3Control u T :=
    h3PathVorticityL1LinfProducesH3Control_of_lowTail_of_pdeTime_of_majorants_of_fullScalarEnergy
      hLow
      hTime
      hMajorants
      hFull
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

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.WholeSpace.Frontier
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.IntegrationByParts.OrderZero
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.IntegrationByParts.OrderOneTwo
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.IntegrationByParts.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Pairing.Integrability

/-!
# Separate the remaining H³ PDE pairing-integrability frontier

`H3PathWholeSpaceEnergyFrontier` removed the automatic higher momentum split
from the H³-path BKM assumptions.  Its spatial package still contains the
monolithic predicate

    H3PDEPairingIntegrableAt u p t,

which asks separately for diffusion, transport, and pressure product
integrability at orders zero through three.

Most of the transport part is already theorem-level.

For an H³-integrable energy-class slice:

* order-zero transport pairing integrability follows from the automatic
  kinetic transport IBP package;
* order-one and order-two pure transport IBP are automatic from H³ plus a
  velocity-gradient envelope;
* the corresponding commutator products are already integrable;
* at order three the gradient/interpolation commutator blocks are already
  integrable.

The only genuinely separate transport datum left is therefore honest
whole-space IBP for the pure transported third derivative.

This file isolates the other two product families as

    H3DiffusionPairingIntegrableAt
    H3PressurePairingIntegrableAt

and proves that

* those two families;
* top-order transport IBP;
* H³ integrability and the high-order energy class

reconstruct the complete `H3PDEPairingIntegrableAt` package.

The resulting H³-path spatial frontier now consists exactly of

1. diffusion pairing integrability;
2. pressure pairing integrability;
3. top-order transport IBP;
4. pressure IBP;
5. diffusion IBP.

No lower-order transport integrability remains external.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathSeparatedPairingFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Separated diffusion and pressure pairing integrability -/

/--
Integrability of every diffusion product appearing in the four H³ energy
blocks.
-/
def H3DiffusionPairingIntegrableAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (fun x : Point3 =>
          loggedVelocityComponent u t j x
            *
          momentumDiffusion0Component
            (logSpaceTimeVectorField u)
            t j x)
  )
    ∧
  (
    ∀ i j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (fun x : Point3 =>
          spatial3.d i
              (loggedVelocityComponent u t j) x
            *
          momentumDiffusion1Component
            (logSpaceTimeVectorField u)
            t i j x)
  )
    ∧
  (
    ∀ i k j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (fun x : Point3 =>
          spatial3.d i
              (spatial3.d k
                (loggedVelocityComponent u t j)) x
            *
          momentumDiffusion2Component
            (logSpaceTimeVectorField u)
            t i k j x)
  )
    ∧
  (
    ∀ i k l j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (fun x : Point3 =>
          spatial3.d i
              (spatial3.d k
                (spatial3.d l
                  (loggedVelocityComponent u t j))) x
            *
          momentumDiffusion3Component
            (logSpaceTimeVectorField u)
            t i k l j x)
  )

/--
Integrability of every pressure product appearing in the four H³ energy
blocks.
-/
def H3PressurePairingIntegrableAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (t : ℝ) : Prop :=
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (fun x : Point3 =>
          loggedVelocityComponent u t j x
            *
          momentumPressure0Component
            p t j x)
  )
    ∧
  (
    ∀ i j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (fun x : Point3 =>
          spatial3.d i
              (loggedVelocityComponent u t j) x
            *
          momentumPressure1Component
            p t i j x)
  )
    ∧
  (
    ∀ i k j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (fun x : Point3 =>
          spatial3.d i
              (spatial3.d k
                (loggedVelocityComponent u t j)) x
            *
          momentumPressure2Component
            p t i k j x)
  )
    ∧
  (
    ∀ i k l j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (fun x : Point3 =>
          spatial3.d i
              (spatial3.d k
                (spatial3.d l
                  (loggedVelocityComponent u t j))) x
            *
          momentumPressure3Component
            p t i k l j x)
  )

/-! ## Automatic transport pairing integrability -/

/--
At an H³-integrable energy-class slice, all four transport products are
integrable once the honest top-order scalar transport IBP datum is supplied.

The lower three orders are automatic.  At order three, the top IBP datum gives
the pure transported-third-derivative product while the already-proved Landau
gradient/interpolation bounds give the commutator product.
-/
theorem h3TransportPairings_integrable_of_energyClass_of_topIBP
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hH3 : VelocityH3IntegrableAt u t)
    (hTopIBP :
      H3ThirdDerivativeTransportIntegrationByPartsAt u t) :
    (
      (∀ j : PrimeTensor.Axis Depth.three,
        MeasureTheory.Integrable
          (fun x : Point3 =>
            loggedVelocityComponent u t j x
              *
            momentumTransport0Component
              (logSpaceTimeVectorField u)
              t j x))
        ∧
      (∀ i j : PrimeTensor.Axis Depth.three,
        MeasureTheory.Integrable
          (fun x : Point3 =>
            spatial3.d i
                (loggedVelocityComponent u t j) x
              *
            momentumTransport1Component
              (logSpaceTimeVectorField u)
              t i j x))
        ∧
      (∀ i k j : PrimeTensor.Axis Depth.three,
        MeasureTheory.Integrable
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)) x
              *
            momentumTransport2Component
              (logSpaceTimeVectorField u)
              t i k j x))
        ∧
      (∀ i k l j : PrimeTensor.Axis Depth.three,
        MeasureTheory.Integrable
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))) x
              *
            momentumTransport3Component
              (logSpaceTimeVectorField u)
              t i k l j x))
    ) := by

  rcases hClass.pressure_witness with
    ⟨p₀, hPDE₀, hp4⟩

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
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
        hClass ht hH3 i j x

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

  have hIBP0 :
      H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hH3 hGradient

  have hIBP1 :
      H3FirstDerivativeTransportIntegrationByPartsAt u t :=
    h3FirstDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass ht hH3 hGradient

  have hIBP2 :
      H3SecondDerivativeTransportIntegrationByPartsAt u t :=
    h3SecondDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass ht hH3 hGradient

  have hPure1 :
      H3OrderOnePureTransportPairingIntegrableAt u t :=
    h3OrderOnePureTransportPairingIntegrableAt_of_integrationByParts
      hClass ht hIBP1

  have hPair1 :
      H3OrderOneTransportPairingIntegrableAt u t :=
    h3OrderOneTransportPairingIntegrableAt_of_pure
      hClass ht hH3 hGradient hPure1

  have hPure2 :
      H3OrderTwoPureTransportPairingIntegrableAt u t :=
    h3OrderTwoPureTransportPairingIntegrableAt_of_integrationByParts
      hClass ht hIBP2

  have hPair2 :
      H3OrderTwoTransportPairingIntegrableAt u t :=
    h3OrderTwoTransportPairingIntegrableAt_of_pure
      hClass ht hH3 hGradient hPure2

  have hSobolev6 :
      WholeSpaceC1H1ToL6 :=
    wholeSpaceC1H1ToL6_of_fderiv
      wholeSpaceC1FDerivL2ToL6_cutoff

  have hSobolev :
      WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6
      hSobolev6

  have hAnalyticCore3 :
      H3OrderThreeInterpolationLandauCoreAnalyticDataAt
        u h t := by
    simpa [
      H3OrderThreeInterpolationLandauCoreAnalyticDataAt
    ] using hGradient

  have hAnalytic3 :
      H3OrderThreeInterpolationLandauAnalyticDataAt
        u h t :=
    h3OrderThreeInterpolationLandauAnalyticDataAt_of_core
      hSobolev
      wholeSpaceQuarticDerivativeIntegrationByParts_cutoff
      hClass
      ht
      hH3
      hAnalyticCore3

  have hGradientPairing3 :
      H3OrderThreeGradientPairingIntegrableAt u t :=
    h3OrderThreeGradientPairingIntegrableAt_of_energyClass
      hClass
      ht
      hH3
      hGradient

  have hMonomialPairing3 :
      H3OrderThreeInterpolationMonomialPairingIntegrableAt u t :=
    h3OrderThreeInterpolationMonomialPairingIntegrableAt_of_landauAnalyticData
      hAnalytic3

  have hInterpolationPairing3 :
      H3OrderThreeInterpolationPairingIntegrableAt u t :=
    h3OrderThreeInterpolationPairingIntegrableAt_of_monomials
      hMonomialPairing3

  have hPure3 :
      H3OrderThreePureTransportPairingIntegrableAt u t :=
    h3OrderThreePureTransportPairingIntegrableAt_of_integrationByParts
      hClass ht hTopIBP

  have hPair3 :
      H3OrderThreeTransportPairingIntegrableAt u t :=
    h3OrderThreeTransportPairingIntegrableAt_of_pure
      hClass
      ht
      hGradientPairing3
      hInterpolationPairing3
      hPure3

  have hRegular3 :
      H3OrderThreeTransportRegularityAt u t :=
    h3OrderThreeTransportRegularityAt_of_energyClass
      hClass ht

  refine
    ⟨
      ?_,
      ?_,
      ?_,
      ?_
    ⟩

  · intro j

    have h0 :=
      transportEnergyPairingIntegrable_of_integrationByParts
        hPDE₀
        htAbs
        hIBP0
        j

    simpa [
      loggedVelocityComponent,
      momentumTransport0Component
    ] using h0

  · intro i j

    have hSplit :=
      momentumTransport1Component_eq_commutator_add_transport
        hPDE₀
        htAbs
        i j

    have hSum :
        MeasureTheory.Integrable
          (fun x : Point3 =>
            spatial3.d i
                (loggedVelocityComponent u t j) x
              *
            firstTransportCommutator
                (logSpaceTimeVectorField u)
                t i j x
              +
            spatial3.d i
                (loggedVelocityComponent u t j) x
              *
            firstTransportedDerivative
                (logSpaceTimeVectorField u)
                t i j x) :=
      (hPair1 i j).1.add
        (hPair1 i j).2

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
          firstTransportCommutator
              (logSpaceTimeVectorField u)
              t i j x
            +
          spatial3.d i
              (loggedVelocityComponent u t j) x
            *
          firstTransportedDerivative
              (logSpaceTimeVectorField u)
              t i j x) := by

      funext x
      rw [congrFun hSplit x]
      ring

    rw [hEq]
    exact hSum

  · intro i k j

    have hSplit :=
      momentumTransport2Component_eq_commutator_add_transport
        hPDE₀
        htAbs
        i k j

    have hSum :
        MeasureTheory.Integrable
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)) x
              *
            secondTransportCommutator
                (logSpaceTimeVectorField u)
                t i k j x
              +
            spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)) x
              *
            secondTransportedDerivative
                (logSpaceTimeVectorField u)
                t i k j x) :=
      (hPair2 i k j).1.add
        (hPair2 i k j).2

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
          secondTransportCommutator
              (logSpaceTimeVectorField u)
              t i k j x
            +
          spatial3.d i
              (spatial3.d k
                (loggedVelocityComponent u t j)) x
            *
          secondTransportedDerivative
              (logSpaceTimeVectorField u)
              t i k j x) := by

      funext x
      rw [congrFun hSplit x]
      ring

    rw [hEq]
    exact hSum

  · intro i k l j

    have hSplit :=
      momentumTransport3Component_eq_commutator_add_transport
        hPDE₀
        htAbs
        hRegular3
        i k l j

    have hSum :
        MeasureTheory.Integrable
          (fun x : Point3 =>
            spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))) x
              *
            thirdTransportCommutator
                (logSpaceTimeVectorField u)
                t i k l j x
              +
            spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))) x
              *
            thirdTransportedDerivative
                (logSpaceTimeVectorField u)
                t i k l j x) :=
      (hPair3 i k l j).1.add
        (hPair3 i k l j).2

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
          thirdTransportCommutator
              (logSpaceTimeVectorField u)
              t i k l j x
            +
          spatial3.d i
              (spatial3.d k
                (spatial3.d l
                  (loggedVelocityComponent u t j))) x
            *
          thirdTransportedDerivative
              (logSpaceTimeVectorField u)
              t i k l j x) := by

      funext x
      rw [congrFun hSplit x]
      ring

    rw [hEq]
    exact hSum

/-! ## Reconstruct the monolithic PDE pairing package -/

/--
The separated diffusion/pressure product families plus top transport IBP
reconstruct all triplet integrability required by the PDE split.
-/
theorem h3PDEPairingIntegrableAt_of_separated
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hH3 : VelocityH3IntegrableAt u t)
    (hDiffusion : H3DiffusionPairingIntegrableAt u t)
    (hPressure : H3PressurePairingIntegrableAt u p t)
    (hTopIBP :
      H3ThirdDerivativeTransportIntegrationByPartsAt u t) :
    H3PDEPairingIntegrableAt u p t := by

  rcases
    h3TransportPairings_integrable_of_energyClass_of_topIBP
      hClass
      ht
      hH3
      hTopIBP
  with
    ⟨hTransport0, hTransport1, hTransport2, hTransport3⟩

  refine
    ⟨
      ?_,
      ?_,
      ?_,
      ?_
    ⟩

  · intro j
    exact
      ⟨
        hDiffusion.1 j,
        hTransport0 j,
        hPressure.1 j
      ⟩

  · intro i j
    exact
      ⟨
        hDiffusion.2.1 i j,
        hTransport1 i j,
        hPressure.2.1 i j
      ⟩

  · intro i k j
    exact
      ⟨
        hDiffusion.2.2.1 i k j,
        hTransport2 i k j,
        hPressure.2.2.1 i k j
      ⟩

  · intro i k l j
    exact
      ⟨
        hDiffusion.2.2.2 i k l j,
        hTransport3 i k l j,
        hPressure.2.2.2 i k l j
      ⟩

/-! ## Refined H³-path whole-space frontier -/

/--
The genuine separated whole-space frontier after all lower transport products
have been discharged automatically.
-/
def H3PathEnergyClassProducesSeparatedWholeSpaceEnergyData : Prop :=
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
              H3ThirdDerivativeTransportIntegrationByPartsAt
                u t
                ∧
              H3PressureIntegrationByPartsAt
                u
                (h3EnergyClassSplitPressureAt hClass ht)
                t
                ∧
              H3DiffusionIntegrationByPartsAt
                u t

/--
The separated frontier reconstructs the previous monolithic whole-space
package.
-/
theorem h3PathEnergyClassProducesWholeSpaceEnergyData_of_separated
    (hSeparated :
      H3PathEnergyClassProducesSeparatedWholeSpaceEnergyData) :
    H3PathEnergyClassProducesWholeSpaceEnergyData := by

  intro u T hH3 a hClass t ht

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

  rcases
    hSeparated u T hH3 a hClass t ht
  with
    ⟨
      hDiffusionPairing,
      hPressurePairing,
      hTopIBP,
      hPressureIBP,
      hDiffusionIBP
    ⟩

  have hPDEPairing :
      H3PDEPairingIntegrableAt
        u
        (h3EnergyClassSplitPressureAt hClass ht)
        t :=
    h3PDEPairingIntegrableAt_of_separated
      hClass
      ht
      hH3At
      hDiffusionPairing
      hPressurePairing
      hTopIBP

  exact
    ⟨
      hPDEPairing,
      hPressureIBP,
      hDiffusionIBP
    ⟩

/-! ## BKM closure at the separated frontier -/

/--
Terminal H³ control with all lower-order transport pairing integrability
removed from the external assumptions.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_pdeTime_of_majorants_of_separatedWholeSpace
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hSeparated :
      H3PathEnergyClassProducesSeparatedWholeSpaceEnergyData) :
    H3PathVorticityL1LinfProducesH3Control := by

  exact
    h3PathVorticityL1LinfProducesH3Control_of_pdeTime_of_majorants_of_wholeSpace
      hTime
      hMajorants
      (h3PathEnergyClassProducesWholeSpaceEnergyData_of_separated
        hSeparated)

/--
H³-path BKM continuation at the separated whole-space frontier.

The remaining inputs are now explicit and nonredundant:

1. higher PDE time differentiability;
2. locally uniform integrable energy-derivative majorants;
3. diffusion pairing integrability;
4. pressure pairing integrability;
5. top-order pure-transport IBP;
6. pressure IBP;
7. diffusion IBP.

Items 3--7 are grouped by
`H3PathEnergyClassProducesSeparatedWholeSpaceEnergyData`.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_pdeTime_of_majorants_of_separatedWholeSpace
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hSeparated :
      H3PathEnergyClassProducesSeparatedWholeSpaceEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_pdeTime_of_majorants_of_wholeSpace
      hTime
      hMajorants
      (h3PathEnergyClassProducesWholeSpaceEnergyData_of_separated
        hSeparated)

end

end Euclidean
end Bridge
end PrimeTensor

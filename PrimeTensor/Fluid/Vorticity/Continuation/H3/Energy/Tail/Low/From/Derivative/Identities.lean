import PrimeTensor.Fluid.Vorticity.Continuation.H3.Pressure.Cancel.Zero
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Energy.Kinetic.Monotonicity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Remove the H³-path BKM low-tail frontier from exact energy differentiation

The active H³-path continuation theorem currently assumes both

* exact orderwise H³ energy derivative identities, and
* a time-independent zeroth-order physical `L²` radius on every strict later
  tail.

The second hypothesis is no longer independent once the fixed-time spatial
energy algebra has been closed.

At every strict energy-class time:

* the exact order-zero energy derivative is supplied by the derivative-identity
  frontier;
* the complete PDE pairing package is already closed from physical `L²` mass;
* the order-zero transport contribution vanishes by the standard whole-space
  incompressible flux argument;
* the pressure contribution vanishes by the gauge-safe pressure closure;
* the diffusion contribution is nonpositive by the closed whole-space
  diffusion integration-by-parts theorem.

Hence the zeroth-order kinetic energy has nonpositive derivative throughout the
strict tail.  The real mean-value theorem makes it antitone, and every later
anchor therefore supplies the exact BKM low-frequency `L²` radius.

Consequently the current continuation interface needs only the exact H³ energy
order-derivative identities.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3PathLowTailFromDerivativeIdentities
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Order-zero dissipation from the exact derivative frontier -/

/--
Exact H³ energy differentiation plus the now-closed spatial energy identities
force the zeroth-order kinetic energy derivative to be nonpositive.
-/
theorem deriv_velocityH3Energy0At_nonpos_of_h3Path_derivativeIdentities
    (hDerivative : H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
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
    hH3.velocity_h3_integrable t htAbs

  have hDerivativeAt :
      H3OrderEnergyDerivativeIdentities u t :=
    hDerivative u T hH3 a hClass t ht

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
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
        u T hH3 a hClass t ht

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

  have hPressureZero :
      velocityH3PressureDerivative0At u p t = 0 := by
    dsimp only [p]
    exact
      h3PathEnergyClassProducesPressure0Cancellation_closed
        u T hH3 a hClass t ht

  have hDiffusionIBP :
      H3DiffusionIntegrationByPartsAt u t :=
    h3PathEnergyClassProducesDiffusionIntegrationByParts_closed
      u T hH3 a hClass t ht

  have hDiffusionNonpos :
      velocityH3DiffusionDerivative0At u t ≤ 0 :=
    velocityH3DiffusionDerivative0At_nonpos
      hDiffusionIBP

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
        - velocityH3TransportDerivative0At u t
        - velocityH3PressureDerivative0At u p t :=
    velocityH3PDEDerivative0At_eq_split
      hPairing

  calc
    deriv (velocityH3Energy0At u) t
        = velocityH3FormalDerivative0At u t :=
      hDerivativeAt.1.deriv
    _ = velocityH3PDEDerivative0At u p t :=
      hFormalPDE
    _ =
        velocityH3DiffusionDerivative0At u t
          - velocityH3TransportDerivative0At u t
          - velocityH3PressureDerivative0At u p t :=
      hSplit
    _ = velocityH3DiffusionDerivative0At u t := by
      rw [hTransportZero, hPressureZero]
      ring
    _ ≤ 0 :=
      hDiffusionNonpos

/-! ## Kinetic antitonicity and the BKM low tail -/

/-- The zeroth-order kinetic energy is antitone on every strict H³ path tail. -/
theorem antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
    (hDerivative : H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
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
    have hAt :
        HasDerivAt
          (velocityH3Energy0At u)
          (velocityH3FormalDerivative0At u t)
          t :=
      (hDerivative u T hH3 a hClass t ht).1
    exact hAt.differentiableAt.differentiableWithinAt

  refine
    antitoneOn_of_deriv_nonpos
      (convex_Ioo a T)
      hDifferentiable.continuousOn
      (hDifferentiable.mono interior_subset)
      ?_

  intro t htInterior

  exact
    deriv_velocityH3Energy0At_nonpos_of_h3Path_derivativeIdentities
      hDerivative
      hH3
      hClass
      (interior_subset htInterior)

/--
Exact energy differentiation automatically manufactures the late-tail physical
`L²` radius required by the BKM endpoint.
-/
theorem h3PathEnergyClassProducesBKMZerothVelocityL2LateTail_of_derivativeIdentities
    (hDerivative : H3PathEnergyClassProducesOrderEnergyDerivativeIdentities) :
    H3PathEnergyClassProducesBKMZerothVelocityL2LateTail := by

  intro u T hH3 a hClass b hb

  have hAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      hDerivative hH3 hClass

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

/-! ## One-frontier continuation theorem -/

/--
After the fixed-time spatial closures, exact H³ energy differentiation is the
only remaining public analytic hypothesis in the H³-path BKM continuation
route.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_derivativeIdentities
    (hDerivative : H3PathEnergyClassProducesOrderEnergyDerivativeIdentities) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities
      (h3PathEnergyClassProducesBKMZerothVelocityL2LateTail_of_derivativeIdentities
        hDerivative)
      hDerivative

end

end Euclidean
end Bridge
end PrimeTensor

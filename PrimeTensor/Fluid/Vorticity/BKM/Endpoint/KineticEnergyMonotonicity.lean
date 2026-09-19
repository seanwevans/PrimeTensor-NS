import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.KineticEnergyLowTail
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.GradientEnvelope
import PrimeTensor.Fluid.Vorticity.H3.Energy.Estimate.Landau.Tail
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# BKM endpoint: kinetic-energy monotonicity on a canonical H³ tail

The endpoint reduction has isolated one final low-frequency input:

    E₀(t) ≤ E₀(a),

where `E₀` is the zeroth-order physical velocity energy.

For a canonical H³ energy-class tail all analytic ingredients needed for the
order-zero energy identity are already present:

* differentiation under the spatial integral;
* the exact Navier--Stokes PDE decomposition;
* diffusion integration by parts;
* pressure integration by parts and incompressibility;
* order-zero transport integration by parts.

The ordinary H³ spectral evaluation estimate supplies the finite gradient
envelope needed to derive the transport integration-by-parts package, without
using the logarithmic BKM estimate.

Consequently

    d/dt E₀(t) ≤ 0

at every strict tail time.  The real mean-value theorem then gives antitonicity
of `E₀` on the open tail.

To avoid imposing a continuity statement at the original left endpoint `a`,
we restart once at the midpoint

    b = (a + T) / 2.

Since `b ∈ (a,T)`, antitonicity immediately gives

    E₀(t) ≤ E₀(b)    for t ∈ (b,T),

which is exactly `BKMKineticEnergyControlledFromAnchor u b T`.

This closes the low-frequency kinetic input directly from the already-existing
canonical H³ energy package.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeBKMEndpointKineticEnergyMonotonicity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Pointwise order-zero dissipation -/

/--
On a canonical H³ energy-class tail, the zeroth-order physical velocity energy
has nonpositive derivative at every strict tail time.
-/
theorem deriv_velocityH3Energy0At_nonpos_of_energyClass_canonical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3Energy0At u) t ≤ 0 := by

  have htIco :
      t ∈ Set.Ico a T :=
    ⟨le_of_lt ht.1, ht.2⟩

  have hH3 :
      VelocityH3IntegrableAt u t :=
    hData.1 t htIco

  rcases hData.2.2 with
    ⟨p, hPDE, hAnalytic⟩

  rcases hAnalytic t ht with
    ⟨
      hDerivative,
      hRegular,
      hPairing,
      hPressureIBP,
      hDiffusionIBP
    ⟩

  have htNS :
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

  have hTransportIBP :
      H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hH3 hGradient

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
      hPressureIBP hDiv

  have hDiffusion :
      velocityH3DiffusionDerivative0At u t ≤ 0 :=
    velocityH3DiffusionDerivative0At_nonpos
      hDiffusionIBP

  have hFormalPDE :
      velocityH3FormalDerivative0At u t
        =
      velocityH3PDEDerivative0At u p t :=
    velocityH3FormalDerivative0At_eq_pde
      hPDE htNS

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

/-! ## Antitonicity on the strict tail -/

/--
The zeroth-order physical velocity energy is antitone on the open canonical
energy-class tail.
-/
theorem antitoneOn_velocityH3Energy0At_of_energyClass_canonical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T) :
    AntitoneOn
      (velocityH3Energy0At u)
      (Set.Ioo a T) := by

  have hDifferentiable :
      DifferentiableOn ℝ
        (velocityH3Energy0At u)
        (Set.Ioo a T) := by

    intro t ht

    rcases hData.2.2 with
      ⟨p, hPDE, hAnalytic⟩

    have hDerivative :=
      (hAnalytic t ht).1

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
    deriv_velocityH3Energy0At_nonpos_of_energyClass_canonical
      hClass
      hData
      (interior_subset htInterior)

/-! ## Midpoint restart -/

/-- A strict interior restart point used to avoid a left-endpoint continuity
obligation for the kinetic energy. -/
noncomputable def h3BKMKineticTailMidpoint
    (a T : ℝ) : ℝ :=
  (a + T) / 2

theorem h3BKMKineticTailMidpoint_mem_Ioo
    {a T : ℝ}
    (haT : a < T) :
    h3BKMKineticTailMidpoint a T
      ∈ Set.Ioo a T := by

  unfold h3BKMKineticTailMidpoint

  constructor <;> linarith

theorem h3BKMKineticTailMidpoint_mem_Ioo_zero
    {a T : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) T) :
    h3BKMKineticTailMidpoint a T
      ∈ Set.Ioo (0 : ℝ) T := by

  have hMid :=
    h3BKMKineticTailMidpoint_mem_Ioo
      ha.2

  exact
    ⟨
      lt_trans ha.1 hMid.1,
      hMid.2
    ⟩

/--
After restarting at the midpoint of a canonical H³ energy-class tail, the
zeroth-order kinetic energy is controlled by its value at that midpoint.
-/
theorem bkmKineticEnergyControlledFromAnchor_midpoint_of_energyClass_canonical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T) :
    BKMKineticEnergyControlledFromAnchor
      u
      (h3BKMKineticTailMidpoint a T)
      T := by

  have hAnti :=
    antitoneOn_velocityH3Energy0At_of_energyClass_canonical
      hClass hData

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

/-! ## Canonical BKM endpoint after the midpoint restart -/

/--
Canonical H³ energy data close the selected BKM actual-gradient logarithmic
estimate on the midpoint-restarted tail.
-/
theorem actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_energyClass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {g : ℝ → ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (hg :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VorticityEnvelope u g t) :
    ActualVelocityGradientLogBoundFrom
      u
      (h3BKMKineticTailMidpoint a T)
      T
      g
      (velocityH3EnergyAt u)
      (h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt
          (velocityH3Energy0At
            u
            (h3BKMKineticTailMidpoint a T)))) := by

  rcases hClass.pressure_witness with
    ⟨p, hPDE, hp4⟩

  let hNS :
      LoggedPreterminalNavierStokesAdmissible u T :=
    ⟨p, hPDE⟩

  have hMidOld :
      h3BKMKineticTailMidpoint a T
        ∈ Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo
      hClass.terminal_start.2

  have hMid :
      h3BKMKineticTailMidpoint a T
        ∈ Set.Ioo (0 : ℝ) T :=
    h3BKMKineticTailMidpoint_mem_Ioo_zero
      hClass.terminal_start

  have hProfileOld :
      H3EnergyProfileFrom
        u a T
        (velocityH3EnergyAt u) :=
    h3EnergyProfileFrom_canonical
      hData

  have hProfile :
      H3EnergyProfileFrom
        u
        (h3BKMKineticTailMidpoint a T)
        T
        (velocityH3EnergyAt u) := by

    intro t ht

    exact
      hProfileOld
        t
        ⟨
          le_trans
            (le_of_lt hMidOld.1)
            ht.1,
          ht.2
        ⟩

  have hgMid :
      ∀ t : ℝ,
        t ∈ Set.Ioo
          (h3BKMKineticTailMidpoint a T)
          T →
        VorticityEnvelope u g t := by

    intro t ht

    exact
      hg t
        ⟨
          lt_trans hMidOld.1 ht.1,
          ht.2
        ⟩

  exact
    actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_kineticEnergyControlledFromAnchor
      hNS
      hMid
      hgMid
      hProfile
      (bkmKineticEnergyControlledFromAnchor_midpoint_of_energyClass_canonical
        hClass hData)

/--
The coefficient in the midpoint-restarted canonical BKM endpoint is
nonnegative.
-/
theorem h3BKMCanonicalSelectedLogGradientConstant_midpoint_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ} :
    0 ≤
      h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt
          (velocityH3Energy0At
            u
            (h3BKMKineticTailMidpoint a T))) := by

  exact
    h3BKMCanonicalSelectedLogGradientConstant_nonneg
      (Real.sqrt_nonneg _)

end

end Euclidean
end Bridge
end PrimeTensor

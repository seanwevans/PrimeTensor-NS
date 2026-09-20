import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSeparatedPairingFrontier

/-!
# Recover H³ PDE pairing integrability from the energy-derivative majorants

`H3PathSeparatedPairingFrontier` isolated an honest top-order transport IBP
datum in order to reconstruct `H3PDEPairingIntegrableAt`.

That datum is not actually independent once the energy-derivative majorant
frontier is already assumed.

At a strict energy-class time, `EnergyClassProducesH3EnergyDerivativeMajorants`
gives an integrable spatial majorant for

    2 D^α u · D^α ∂ₜu,    |α| ≤ 3,

on a time neighborhood containing the target time.  The target-time products
are automatically measurable, so each is integrable.  The old preterminal
momentum equation identifies the spatial derivatives of `∂ₜu` with the
corresponding momentum RHS fields.  Therefore

    D^α u · D^α RHS

is integrable at all four orders.

Once the diffusion and pressure products are integrable, the exact pointwise
identity

    RHS = diffusion - transport - pressure

solves for the transport product and proves its integrability by subtraction.
Thus the full `H3PDEPairingIntegrableAt` package follows without a separate
transport boundary hypothesis.

After this file, the fixed-time whole-space frontier contains only

* diffusion pairing integrability;
* pressure pairing integrability;
* pressure integration by parts;
* diffusion integration by parts.

The top-order transport IBP is then recoverable downstream from the complete
PDE pairing package by the existing automatic top-flux theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathMajorantPDEPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## A small domination helper -/

private theorem integrable_of_integrable_bound
    {f b : Point3 → ℝ}
    (hf : AEStronglyMeasurable f (volume : Measure Point3))
    (hb : Integrable b (volume : Measure Point3))
    (hfb :
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ‖f x‖ ≤ b x) :
    Integrable f (volume : Measure Point3) := by

  apply hb.mono' hf

  filter_upwards [hfb] with x hx

  exact hx

private theorem integrable_product_of_twice
    {f g : Point3 → ℝ}
    (h :
      Integrable
        (fun x : Point3 =>
          2 * f x * g x)
        (volume : Measure Point3)) :
    Integrable
      (fun x : Point3 =>
        f x * g x)
      (volume : Measure Point3) := by

  have hHalf :=
    h.const_mul (1 / 2 : ℝ)

  have hEq :
      (fun x : Point3 =>
        (1 / 2 : ℝ)
          * (2 * f x * g x))
        =
      (fun x : Point3 =>
        f x * g x) := by
    funext x
    ring

  rw [hEq] at hHalf

  exact hHalf

/-! ## Target-time derivative products are integrable -/

private theorem h3Order0_derivativeProduct_integrable_of_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (h :
      H3Order0EnergyDerivativeMajorantOnTailAt
        u a T t)
    (j : PrimeTensor.Axis Depth.three) :
    Integrable
      (fun x : Point3 =>
        loggedVelocityComponent u t j x
          *
        loggedVelocityTemporalComponent u t j x)
      (volume : Measure Point3) := by

  have htSet :
      t ∈ h.timeSet j :=
    mem_of_mem_nhds
      (h.timeSet_mem_nhds j)

  have hTwice :
      Integrable
        (fun x : Point3 =>
          2
            * loggedVelocityComponent u t j x
            * loggedVelocityTemporalComponent u t j x)
        (volume : Measure Point3) := by

    apply
      integrable_of_integrable_bound
        (h3Order0_derivativeProduct_aestronglyMeasurable_of_energyClass
          hClass ht j)
        (h.bound_integrable j)

    filter_upwards [h.derivative_le_bound j] with x hx

    exact
      hx t htSet

  exact
    integrable_product_of_twice
      hTwice

private theorem h3Order1_derivativeProduct_integrable_of_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (h :
      H3Order1EnergyDerivativeMajorantOnTailAt
        u a T t)
    (j i : PrimeTensor.Axis Depth.three) :
    Integrable
      (fun x : Point3 =>
        spatial3.d i
            (loggedVelocityComponent u t j) x
          *
        spatial3.d i
            (loggedVelocityTemporalComponent u t j) x)
      (volume : Measure Point3) := by

  have htSet :
      t ∈ h.timeSet j i :=
    mem_of_mem_nhds
      (h.timeSet_mem_nhds j i)

  have hTwice :
      Integrable
        (fun x : Point3 =>
          2
            * spatial3.d i
                (loggedVelocityComponent u t j) x
            * spatial3.d i
                (loggedVelocityTemporalComponent u t j) x)
        (volume : Measure Point3) := by

    apply
      integrable_of_integrable_bound
        (h3Order1_derivativeProduct_aestronglyMeasurable_of_energyClass
          hClass ht j i)
        (h.bound_integrable j i)

    filter_upwards [h.derivative_le_bound j i] with x hx

    exact
      hx t htSet

  exact
    integrable_product_of_twice
      hTwice

private theorem h3Order2_derivativeProduct_integrable_of_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (h :
      H3Order2EnergyDerivativeMajorantOnTailAt
        u a T t)
    (j i k : PrimeTensor.Axis Depth.three) :
    Integrable
      (fun x : Point3 =>
        spatial3.d i
            (spatial3.d k
              (loggedVelocityComponent u t j)) x
          *
        spatial3.d i
            (spatial3.d k
              (loggedVelocityTemporalComponent u t j)) x)
      (volume : Measure Point3) := by

  have htSet :
      t ∈ h.timeSet j i k :=
    mem_of_mem_nhds
      (h.timeSet_mem_nhds j i k)

  have hTwice :
      Integrable
        (fun x : Point3 =>
          2
            * spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)) x
            * spatial3.d i
                (spatial3.d k
                  (loggedVelocityTemporalComponent u t j)) x)
        (volume : Measure Point3) := by

    apply
      integrable_of_integrable_bound
        (h3Order2_derivativeProduct_aestronglyMeasurable_of_energyClass
          hClass ht j i k)
        (h.bound_integrable j i k)

    filter_upwards [h.derivative_le_bound j i k] with x hx

    exact
      hx t htSet

  exact
    integrable_product_of_twice
      hTwice

private theorem h3Order3_derivativeProduct_integrable_of_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (h :
      H3Order3EnergyDerivativeMajorantOnTailAt
        u a T t)
    (j i k l : PrimeTensor.Axis Depth.three) :
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
      (volume : Measure Point3) := by

  have htSet :
      t ∈ h.timeSet j i k l :=
    mem_of_mem_nhds
      (h.timeSet_mem_nhds j i k l)

  have hTwice :
      Integrable
        (fun x : Point3 =>
          2
            * spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))) x
            * spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityTemporalComponent u t j))) x)
        (volume : Measure Point3) := by

    apply
      integrable_of_integrable_bound
        (h3Order3_derivativeProduct_aestronglyMeasurable_of_energyClass
          hClass ht j i k l)
        (h.bound_integrable j i k l)

    filter_upwards [h.derivative_le_bound j i k l] with x hx

    exact
      hx t htSet

  exact
    integrable_product_of_twice
      hTwice

/-! ## The majorants integrate the complete momentum RHS pairing -/

theorem h3MomentumRHSPairings_integrable_of_majorants
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
    (hMajorant :
      H3EnergyDerivativeMajorantDataAt
        u a T t) :
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

  refine
    ⟨
      ?_,
      ?_,
      ?_,
      ?_
    ⟩

  · intro j

    have hInt :=
      h3Order0_derivativeProduct_integrable_of_majorant
        hClass ht hMajorant.order0 j

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

    have hInt :=
      h3Order1_derivativeProduct_integrable_of_majorant
        hClass ht hMajorant.order1 j i

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

    have hInt :=
      h3Order2_derivativeProduct_integrable_of_majorant
        hClass ht hMajorant.order2 j i k

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

    have hInt :=
      h3Order3_derivativeProduct_integrable_of_majorant
        hClass ht hMajorant.order3 j i k l

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

/-! ## Recover the transport products by subtraction -/

/--
Derivative majorants integrate the full momentum RHS product.  Therefore
diffusion-product and pressure-product integrability force transport-product
integrability at every H³ order.
-/
theorem h3PDEPairingIntegrableAt_of_majorants_of_diffusion_pressure
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
    (hMajorant :
      H3EnergyDerivativeMajorantDataAt
        u a T t)
    (hDiffusion :
      H3DiffusionPairingIntegrableAt u t)
    (hPressure :
      H3PressurePairingIntegrableAt u p t) :
    H3PDEPairingIntegrableAt u p t := by

  rcases
    h3MomentumRHSPairings_integrable_of_majorants
      hClass
      ht
      hPDE
      hMajorant
  with
    ⟨hRHS0, hRHS1, hRHS2, hRHS3⟩

  refine
    ⟨
      ?_,
      ?_,
      ?_,
      ?_
    ⟩

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
          (hRHS0 j)

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
          (hRHS1 i j)

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

        rw [
          congrFun
            (hHigher.1 i k j)
            x
        ]

        ring

      rw [hEq]

      exact
        ((hDiffusion.2.2.1 i k j).sub
          (hPressure.2.2.1 i k j)).sub
          (hRHS2 i k j)

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

        rw [
          congrFun
            (hHigher.2 i k l j)
            x
        ]

        ring

      rw [hEq]

      exact
        ((hDiffusion.2.2.2 i k l j).sub
          (hPressure.2.2.2 i k l j)).sub
          (hRHS3 i k l j)

    exact
      ⟨
        hDiffusion.2.2.2 i k l j,
        hTransport,
        hPressure.2.2.2 i k l j
      ⟩

/-! ## Whole-space frontier with no transport assumption -/

/--
After using the energy-derivative majorants to recover all momentum-RHS
pairings, the remaining fixed-time whole-space data contain no transport
hypothesis.
-/
def H3PathEnergyClassProducesDiffusionPressureWholeSpaceEnergyData : Prop :=
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
              H3PressureIntegrationByPartsAt
                u
                (h3EnergyClassSplitPressureAt hClass ht)
                t
                ∧
              H3DiffusionIntegrationByPartsAt
                u t

/--
Derivative majorants plus the diffusion/pressure whole-space data reconstruct
the previous complete fixed-time whole-space package.
-/
theorem h3PathEnergyClassProducesWholeSpaceEnergyData_of_majorants_of_diffusionPressure
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hWhole :
      H3PathEnergyClassProducesDiffusionPressureWholeSpaceEnergyData) :
    H3PathEnergyClassProducesWholeSpaceEnergyData := by

  intro u T hH3 a hClass t ht

  rcases
    hMajorants u a T hClass t ht
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
      ?_,
      ?_,
      hDiffusionIBP
    ⟩

  · simpa only [p] using hPDEPairing
  · simpa only [p] using hPressureIBP

/-! ## BKM closure at the transport-free spatial frontier -/

/--
Terminal H³ control with the entire transport-pairing frontier reconstructed
from the derivative majorants.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_pdeTime_of_majorants_of_diffusionPressureWholeSpace
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hWhole :
      H3PathEnergyClassProducesDiffusionPressureWholeSpaceEnergyData) :
    H3PathVorticityL1LinfProducesH3Control := by

  exact
    h3PathVorticityL1LinfProducesH3Control_of_pdeTime_of_majorants_of_wholeSpace
      hTime
      hMajorants
      (h3PathEnergyClassProducesWholeSpaceEnergyData_of_majorants_of_diffusionPressure
        hMajorants
        hWhole)

/--
H³-path BKM continuation with no independent transport assumption.

The remaining explicit interfaces are now:

1. higher PDE time differentiability;
2. locally uniform integrable energy-derivative majorants;
3. diffusion pairing integrability;
4. pressure pairing integrability;
5. pressure integration by parts;
6. diffusion integration by parts.

Items 3--6 are grouped by
`H3PathEnergyClassProducesDiffusionPressureWholeSpaceEnergyData`.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_pdeTime_of_majorants_of_diffusionPressureWholeSpace
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hWhole :
      H3PathEnergyClassProducesDiffusionPressureWholeSpaceEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_pdeTime_of_majorants_of_wholeSpace
      hTime
      hMajorants
      (h3PathEnergyClassProducesWholeSpaceEnergyData_of_majorants_of_diffusionPressure
        hMajorants
        hWhole)

end

end Euclidean
end Bridge
end PrimeTensor

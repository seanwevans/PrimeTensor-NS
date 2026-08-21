import PrimeTensor.Fluid.VorticityH3EnergyPressureClass

/-!
# Nonpositivity of the H³ diffusion contribution

This file isolates the whole-space integration-by-parts identity needed by the
diffusion term of the canonical H³ energy derivative.

For one scalar field `f` paired with its differentiated Laplacian contribution
`g`, the exact analytic datum is

    ⟨f, g⟩ = -2 * Σ_r ∫ (∂_r f)^2.

The right-hand side is nonpositive because every squared spatial energy is
nonnegative.  The four H³ derivative orders are then finite sums of such
pairings.

No decay-at-infinity or boundary theorem is hidden here: those facts are
represented precisely by `H3DiffusionIntegrationByPartsAt`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyDiffusion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
Exact whole-space diffusion integration-by-parts identity for one scalar
energy pairing.
-/
def DiffusionPairingIntegrationByParts
    (f g : ScalarField3) : Prop :=
  spatialEnergyPairing f g
    =
  -2 *
    ∑ r : PrimeTensor.Axis Depth.three,
      spatialSquareEnergy
        (spatial3.d r f)

/--
A scalar diffusion pairing satisfying the exact whole-space
integration-by-parts identity is nonpositive.
-/
theorem diffusionPairing_nonpos
    {f g : ScalarField3}
    (
      hIBP :
        DiffusionPairingIntegrationByParts
          f g
    ) :
    spatialEnergyPairing f g ≤ 0 := by

  have hSquares :
      0 ≤
        ∑ r : PrimeTensor.Axis Depth.three,
          spatialSquareEnergy
            (spatial3.d r f) := by

    exact
      Finset.sum_nonneg
        (fun r _ =>
          spatialSquareEnergy_nonneg
            (spatial3.d r f))

  unfold DiffusionPairingIntegrationByParts at hIBP
  rw [hIBP]

  nlinarith

/--
The exact diffusion integration-by-parts data for every scalar pairing
appearing in the four H³ derivative blocks.
-/
def H3DiffusionIntegrationByPartsAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      DiffusionPairingIntegrationByParts
        (loggedVelocityComponent u t j)
        (
          momentumDiffusion0Component
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t j
        )
  )
    ∧
  (
    ∀ i j : PrimeTensor.Axis Depth.three,
      DiffusionPairingIntegrationByParts
        (
          spatial3.d
            i
            (loggedVelocityComponent u t j)
        )
        (
          momentumDiffusion1Component
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i j
        )
  )
    ∧
  (
    ∀ i k j : PrimeTensor.Axis Depth.three,
      DiffusionPairingIntegrationByParts
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (loggedVelocityComponent u t j)
            )
        )
        (
          momentumDiffusion2Component
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k j
        )
  )
    ∧
  (
    ∀ i k l j : PrimeTensor.Axis Depth.three,
      DiffusionPairingIntegrationByParts
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (
                  spatial3.d
                    l
                    (loggedVelocityComponent u t j)
                )
            )
        )
        (
          momentumDiffusion3Component
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j
        )
  )

/-! ## Orderwise nonpositivity -/

theorem velocityH3DiffusionDerivative0At_nonpos
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3DiffusionIntegrationByPartsAt
          u t
    ) :
    velocityH3DiffusionDerivative0At
        u t
      ≤
    0 := by

  unfold velocityH3DiffusionDerivative0At

  exact
    Finset.sum_nonpos
      (fun j _ =>
        diffusionPairing_nonpos
          (hIBP.1 j))

theorem velocityH3DiffusionDerivative1At_nonpos
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3DiffusionIntegrationByPartsAt
          u t
    ) :
    velocityH3DiffusionDerivative1At
        u t
      ≤
    0 := by

  unfold velocityH3DiffusionDerivative1At

  exact
    Finset.sum_nonpos
      (fun j _ =>
        Finset.sum_nonpos
          (fun i _ =>
            diffusionPairing_nonpos
              (hIBP.2.1 i j)))

theorem velocityH3DiffusionDerivative2At_nonpos
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3DiffusionIntegrationByPartsAt
          u t
    ) :
    velocityH3DiffusionDerivative2At
        u t
      ≤
    0 := by

  unfold velocityH3DiffusionDerivative2At

  exact
    Finset.sum_nonpos
      (fun j _ =>
        Finset.sum_nonpos
          (fun i _ =>
            Finset.sum_nonpos
              (fun k _ =>
                diffusionPairing_nonpos
                  (hIBP.2.2.1 i k j))))

theorem velocityH3DiffusionDerivative3At_nonpos
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3DiffusionIntegrationByPartsAt
          u t
    ) :
    velocityH3DiffusionDerivative3At
        u t
      ≤
    0 := by

  unfold velocityH3DiffusionDerivative3At

  exact
    Finset.sum_nonpos
      (fun j _ =>
        Finset.sum_nonpos
          (fun i _ =>
            Finset.sum_nonpos
              (fun k _ =>
                Finset.sum_nonpos
                  (fun l _ =>
                    diffusionPairing_nonpos
                      (hIBP.2.2.2 i k l j)))))

/--
The full diffusion contribution to the canonical H³ energy derivative is
nonpositive under the exact whole-space integration-by-parts package.
-/
theorem velocityH3DiffusionDerivativeAt_nonpos
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3DiffusionIntegrationByPartsAt
          u t
    ) :
    velocityH3DiffusionDerivativeAt
        u t
      ≤
    0 := by

  have h0 :=
    velocityH3DiffusionDerivative0At_nonpos
      hIBP

  have h1 :=
    velocityH3DiffusionDerivative1At_nonpos
      hIBP

  have h2 :=
    velocityH3DiffusionDerivative2At_nonpos
      hIBP

  have h3 :=
    velocityH3DiffusionDerivative3At_nonpos
      hIBP

  unfold velocityH3DiffusionDerivativeAt

  linarith

end Euclidean
end Bridge
end PrimeTensor

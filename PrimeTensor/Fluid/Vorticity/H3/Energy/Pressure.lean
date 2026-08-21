import PrimeTensor.Fluid.Vorticity.H3.Energy.Class.Split.Regularity

/-!
# Pressure cancellation in the canonical H³ energy identity

The exact PDE split now isolates

    velocityH3PressureDerivativeAt u p t.

For incompressible flow this contribution vanishes.  The mechanism is the
standard one:

    Σ_j ∫ F_j ∂_j q
      = - Σ_j ∫ (∂_j F_j) q
      = - ∫ (Σ_j ∂_j F_j) q
      = 0.

This file formalizes that mechanism without hiding the genuinely whole-space
analytic input.

`PressurePairingIntegrationByParts` records the one-coordinate integration by
parts identity, including whatever decay / cutoff limiting argument is needed
to justify the disappearance of the boundary term.  It does *not* follow from
the local `SpatialCk` regularity assumptions alone.

`DifferentiatedDivergenceFree` is the pointwise differentiated
incompressibility statement.

The generic theorem `sum_pressurePairing_eq_zero` combines these with
Mathlib's finite-sum linearity of the Bochner integral.  The four H³ orders are
then instances of that theorem.

A later module can derive the differentiated divergence identities from the
high-order energy class and can discharge the integration-by-parts hypotheses
from explicit decay / Sobolev data.  This file contains the cancellation
algebra itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyPressure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-! ## Generic pressure cancellation -/

/--
Whole-space integration by parts for one family of pressure pairings.

`F j` is the `j`th velocity component after some common collection of spatial
derivatives.  `P j` is the corresponding differentiated pressure-gradient
field appearing in the momentum equation.  `q` is the common pressure
potential after those same derivatives.

The equality records both derivative commutation needed to identify `P j`
with `∂_j q` and the vanishing-boundary integration-by-parts step.
The integrability clause is retained separately because it is needed to move
the finite sum through the Lebesgue integral.
-/
def PressurePairingIntegrationByParts
    (F P : PrimeTensor.Axis Depth.three → ScalarField3)
    (q : ScalarField3) : Prop :=
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            spatial3.d j (F j) x * q x
        )
  )
    ∧
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      spatialEnergyPairing
          (F j)
          (P j)
        =
      -2 *
        ∫ x : Point3,
          spatial3.d j (F j) x * q x
  )

/--
Pointwise divergence-freeness of a family of scalar component fields.
-/
def DifferentiatedDivergenceFree
    (F : PrimeTensor.Axis Depth.three → ScalarField3) : Prop :=
  ∀ x : Point3,
    (∑ j : PrimeTensor.Axis Depth.three,
      spatial3.d j (F j) x)
      =
    0

/--
The generic pressure cancellation lemma.

After integration by parts, finite-sum linearity moves the component sum
inside the integral.  Pointwise differentiated incompressibility then makes
the integrand identically zero.
-/
theorem sum_pressurePairing_eq_zero
    {
      F P :
        PrimeTensor.Axis Depth.three →
          ScalarField3
    }
    {
      q : ScalarField3
    }
    (
      hIBP :
        PressurePairingIntegrationByParts
          F P q
    )
    (
      hDiv :
        DifferentiatedDivergenceFree
          F
    ) :
    (∑ j : PrimeTensor.Axis Depth.three,
      spatialEnergyPairing
        (F j)
        (P j))
      =
    0 := by

  rcases hIBP with
    ⟨hIntegrable, hPairing⟩

  have hIntegralSum :
      (
        ∫ x : Point3,
          ∑ j : PrimeTensor.Axis Depth.three,
            spatial3.d j (F j) x * q x
      )
        =
      ∑ j : PrimeTensor.Axis Depth.three,
        ∫ x : Point3,
          spatial3.d j (F j) x * q x := by

    simpa using
      MeasureTheory.integral_finsetSum
        (Finset.univ :
          Finset (PrimeTensor.Axis Depth.three))
        (by
          intro j hj
          exact hIntegrable j)

  have hPointwise :
      (
        fun x : Point3 =>
          ∑ j : PrimeTensor.Axis Depth.three,
            spatial3.d j (F j) x * q x
      )
        =
      fun _ : Point3 => 0 := by

    funext x

    rw [← Finset.sum_mul]

    rw [hDiv x]

    simp

  have hSumIntegralZero :
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∫ x : Point3,
            spatial3.d j (F j) x * q x
      )
        =
      0 := by

    rw [← hIntegralSum]

    rw [hPointwise]

    simp

  calc
    (∑ j : PrimeTensor.Axis Depth.three,
      spatialEnergyPairing
        (F j)
        (P j))
        =
      ∑ j : PrimeTensor.Axis Depth.three,
        (
          -2 *
            ∫ x : Point3,
              spatial3.d j (F j) x * q x
        ) := by

          apply Finset.sum_congr rfl
          intro j hj
          exact hPairing j

    _ =
      -2 *
        (
          ∑ j : PrimeTensor.Axis Depth.three,
            ∫ x : Point3,
              spatial3.d j (F j) x * q x
        ) := by
          rw [Finset.mul_sum]

    _ = 0 := by
      rw [hSumIntegralZero]
      ring

/-! ## H³ orderwise families -/

noncomputable def h3PressureVelocityFamily0
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    PrimeTensor.Axis Depth.three → ScalarField3 :=
  fun j =>
    loggedVelocityComponent u t j

noncomputable def h3PressureFieldFamily0
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) :
    PrimeTensor.Axis Depth.three → ScalarField3 :=
  fun j =>
    momentumPressure0Component p t j

noncomputable def h3PressureVelocityFamily1
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i : PrimeTensor.Axis Depth.three) :
    PrimeTensor.Axis Depth.three → ScalarField3 :=
  fun j =>
    spatial3.d i
      (loggedVelocityComponent u t j)

noncomputable def h3PressureFieldFamily1
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i : PrimeTensor.Axis Depth.three) :
    PrimeTensor.Axis Depth.three → ScalarField3 :=
  fun j =>
    momentumPressure1Component p t i j

noncomputable def h3PressurePotential1
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d i (p t)

noncomputable def h3PressureVelocityFamily2
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k : PrimeTensor.Axis Depth.three) :
    PrimeTensor.Axis Depth.three → ScalarField3 :=
  fun j =>
    spatial3.d i
      (
        spatial3.d k
          (loggedVelocityComponent u t j)
      )

noncomputable def h3PressureFieldFamily2
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k : PrimeTensor.Axis Depth.three) :
    PrimeTensor.Axis Depth.three → ScalarField3 :=
  fun j =>
    momentumPressure2Component p t i k j

noncomputable def h3PressurePotential2
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d i
    (spatial3.d k (p t))

noncomputable def h3PressureVelocityFamily3
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k l : PrimeTensor.Axis Depth.three) :
    PrimeTensor.Axis Depth.three → ScalarField3 :=
  fun j =>
    spatial3.d i
      (
        spatial3.d k
          (
            spatial3.d l
              (loggedVelocityComponent u t j)
          )
      )

noncomputable def h3PressureFieldFamily3
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l : PrimeTensor.Axis Depth.three) :
    PrimeTensor.Axis Depth.three → ScalarField3 :=
  fun j =>
    momentumPressure3Component p t i k l j

noncomputable def h3PressurePotential3
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d i
    (
      spatial3.d k
        (
          spatial3.d l
            (p t)
        )
    )

/-! ## Exact whole-space pressure hypotheses at one time -/

/--
The exact integration-by-parts data needed for the four H³ pressure blocks.
-/
def H3PressureIntegrationByPartsAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : Prop :=
  PressurePairingIntegrationByParts
      (h3PressureVelocityFamily0 u t)
      (h3PressureFieldFamily0 p t)
      (p t)
    ∧
  (
    ∀ i : PrimeTensor.Axis Depth.three,
      PressurePairingIntegrationByParts
        (h3PressureVelocityFamily1 u t i)
        (h3PressureFieldFamily1 p t i)
        (h3PressurePotential1 p t i)
  )
    ∧
  (
    ∀ i k : PrimeTensor.Axis Depth.three,
      PressurePairingIntegrationByParts
        (h3PressureVelocityFamily2 u t i k)
        (h3PressureFieldFamily2 p t i k)
        (h3PressurePotential2 p t i k)
  )
    ∧
  (
    ∀ i k l : PrimeTensor.Axis Depth.three,
      PressurePairingIntegrationByParts
        (h3PressureVelocityFamily3 u t i k l)
        (h3PressureFieldFamily3 p t i k l)
        (h3PressurePotential3 p t i k l)
  )

/--
Pointwise incompressibility after zero through three common spatial
derivatives.
-/
def H3DifferentiatedIncompressibilityAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  DifferentiatedDivergenceFree
      (h3PressureVelocityFamily0 u t)
    ∧
  (
    ∀ i : PrimeTensor.Axis Depth.three,
      DifferentiatedDivergenceFree
        (h3PressureVelocityFamily1 u t i)
  )
    ∧
  (
    ∀ i k : PrimeTensor.Axis Depth.three,
      DifferentiatedDivergenceFree
        (h3PressureVelocityFamily2 u t i k)
  )
    ∧
  (
    ∀ i k l : PrimeTensor.Axis Depth.three,
      DifferentiatedDivergenceFree
        (h3PressureVelocityFamily3 u t i k l)
  )

/-! ## Orderwise pressure cancellation -/

theorem velocityH3PressureDerivative0At_eq_zero
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3PressureIntegrationByPartsAt
          u p t
    )
    (
      hDiv :
        H3DifferentiatedIncompressibilityAt
          u t
    ) :
    velocityH3PressureDerivative0At
        u p t
      =
    0 := by

  unfold velocityH3PressureDerivative0At

  simpa [
    h3PressureVelocityFamily0,
    h3PressureFieldFamily0
  ] using
    sum_pressurePairing_eq_zero
      hIBP.1
      hDiv.1

theorem velocityH3PressureDerivative1At_eq_zero
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3PressureIntegrationByPartsAt
          u p t
    )
    (
      hDiv :
        H3DifferentiatedIncompressibilityAt
          u t
    ) :
    velocityH3PressureDerivative1At
        u p t
      =
    0 := by

  unfold velocityH3PressureDerivative1At

  rw [Finset.sum_comm]

  apply Finset.sum_eq_zero

  intro i hi

  simpa [
    h3PressureVelocityFamily1,
    h3PressureFieldFamily1
  ] using
    sum_pressurePairing_eq_zero
      (hIBP.2.1 i)
      (hDiv.2.1 i)

theorem velocityH3PressureDerivative2At_eq_zero
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3PressureIntegrationByPartsAt
          u p t
    )
    (
      hDiv :
        H3DifferentiatedIncompressibilityAt
          u t
    ) :
    velocityH3PressureDerivative2At
        u p t
      =
    0 := by

  unfold velocityH3PressureDerivative2At

  calc
    (∑ j : PrimeTensor.Axis Depth.three,
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          spatialEnergyPairing
            (
              spatial3.d i
                (
                  spatial3.d k
                    (loggedVelocityComponent u t j)
                )
            )
            (momentumPressure2Component p t i k j))
        =
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ j : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (
                spatial3.d i
                  (
                    spatial3.d k
                      (loggedVelocityComponent u t j)
                  )
              )
              (momentumPressure2Component p t i k j) := by

          rw [Finset.sum_comm]

          apply Finset.sum_congr rfl
          intro i hi

          rw [Finset.sum_comm]

    _ = 0 := by

      apply Finset.sum_eq_zero
      intro i hi

      apply Finset.sum_eq_zero
      intro k hk

      simpa [
        h3PressureVelocityFamily2,
        h3PressureFieldFamily2
      ] using
        sum_pressurePairing_eq_zero
          (hIBP.2.2.1 i k)
          (hDiv.2.2.1 i k)

theorem velocityH3PressureDerivative3At_eq_zero
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3PressureIntegrationByPartsAt
          u p t
    )
    (
      hDiv :
        H3DifferentiatedIncompressibilityAt
          u t
    ) :
    velocityH3PressureDerivative3At
        u p t
      =
    0 := by

  unfold velocityH3PressureDerivative3At

  calc
    (∑ j : PrimeTensor.Axis Depth.three,
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (
                spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                  )
              )
              (momentumPressure3Component p t i k l j))
        =
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three,
            ∑ j : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (
                  spatial3.d i
                    (
                      spatial3.d k
                        (
                          spatial3.d l
                            (loggedVelocityComponent u t j)
                        )
                    )
                )
                (momentumPressure3Component p t i k l j) := by

          rw [Finset.sum_comm]

          apply Finset.sum_congr rfl
          intro i hi

          rw [Finset.sum_comm]

          apply Finset.sum_congr rfl
          intro k hk

          rw [Finset.sum_comm]

    _ = 0 := by

      apply Finset.sum_eq_zero
      intro i hi

      apply Finset.sum_eq_zero
      intro k hk

      apply Finset.sum_eq_zero
      intro l hl

      simpa [
        h3PressureVelocityFamily3,
        h3PressureFieldFamily3
      ] using
        sum_pressurePairing_eq_zero
          (hIBP.2.2.2 i k l)
          (hDiv.2.2.2 i k l)

/--
The full pressure contribution to the canonical H³ energy derivative vanishes
under whole-space integration by parts and differentiated incompressibility.
-/
theorem velocityH3PressureDerivativeAt_eq_zero
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3PressureIntegrationByPartsAt
          u p t
    )
    (
      hDiv :
        H3DifferentiatedIncompressibilityAt
          u t
    ) :
    velocityH3PressureDerivativeAt
        u p t
      =
    0 := by

  unfold velocityH3PressureDerivativeAt

  rw [
    velocityH3PressureDerivative0At_eq_zero hIBP hDiv,
    velocityH3PressureDerivative1At_eq_zero hIBP hDiv,
    velocityH3PressureDerivative2At_eq_zero hIBP hDiv,
    velocityH3PressureDerivative3At_eq_zero hIBP hDiv
  ]

  ring

end Euclidean
end Bridge
end PrimeTensor

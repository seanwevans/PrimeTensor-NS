import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationLandauHolderClosure

/-!
# Third-order H³ interpolation: corrected Landau monomial closure

This file replaces the too-strong tuple energy condition

    A² + B² + C² ≤ E₃

by the three conditions that the actual H³ energy can always support:

    A² ≤ E₃,  B² ≤ E₃,  C² ≤ E₃.

This matters when derivative indices collide.  In the extreme case the three
quantities can be the same H³ energy summand, so their unweighted sum is not
bounded by `E₃`.

With individual energy domination, the scalar Landau closure is

    2 A G Q ≤ 6 h E,

which is sharp for this bookkeeping in the fully-collided case.

Whole-space quartic integration by parts and integrability remain explicit
analytic data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable local instance axisFintypeH3LandauMonomials
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3EnergyDerivative d

noncomputable local instance point3MeasureSpaceH3LandauMonomials :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3EnergyDerivative Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## One Landau-controlled second derivative -/

def LandauDerivativeControl
    (v g dg : ScalarField3)
    (h : ℝ) : Prop :=
  MeasureTheory.MemLp
      g
      (ENNReal.ofReal 4)
      volume
    ∧
  LandauQuarticIntegrationByParts
      v g dg
    ∧
  LandauQuarticEnvelopeIntegrable
      v g dg h
    ∧
  LandauCauchyMemLp
      g dg

theorem landauL4_sq_le_of_derivativeControl
    {v g dg : ScalarField3}
    {h : ℝ}
    (hEnv : LandauScalarEnvelope v h)
    (hControl : LandauDerivativeControl v g dg h) :
    landauL4 g ^ 2
      ≤
    3 * h * landauL2 dg := by

  rcases hControl with
    ⟨hg4, hIBP, hInt, hCauchy⟩

  have hLandau :
      landauL4Squared g
        ≤
      3 * h * landauL2 dg :=
    landau_L4_sq_le_three_mul_envelope_mul_L2
      hIBP
      hEnv
      hInt
      hCauchy

  exact
    landauL4_sq_le_of_landauL4Squared_le
      hLandau

/-! ## Corrected scalar energy closure -/

/--
If each of the three L² squares is individually dominated by the same energy
`E`, the Landau bounds imply the `2-4-4` product estimate with constant `6`.
-/
theorem landau_three_factor_algebra_of_each_energy
    {A B C G Q h E : ℝ}
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (hG : 0 ≤ G)
    (hQ : 0 ≤ Q)
    (hh : 0 ≤ h)
    (hG2 : G ^ 2 ≤ 3 * h * B)
    (hQ2 : Q ^ 2 ≤ 3 * h * C)
    (hA2 : A ^ 2 ≤ E)
    (hB2 : B ^ 2 ≤ E)
    (hC2 : C ^ 2 ≤ E) :
    2 * A * G * Q ≤ 6 * h * E := by

  have hGQ :
      2 * G * Q
        ≤
      3 * h * (B + C) := by
    calc
      2 * G * Q
          ≤
        G ^ 2 + Q ^ 2 := by
          nlinarith [sq_nonneg (G - Q)]
      _ ≤
        3 * h * B + 3 * h * C :=
          add_le_add hG2 hQ2
      _ =
        3 * h * (B + C) := by
          ring

  have hAB :
      A * B ≤ E := by
    have hYoung :
        2 * A * B ≤ A ^ 2 + B ^ 2 := by
      nlinarith [sq_nonneg (A - B)]
    nlinarith [hA2, hB2]

  have hAC :
      A * C ≤ E := by
    have hYoung :
        2 * A * C ≤ A ^ 2 + C ^ 2 := by
      nlinarith [sq_nonneg (A - C)]
    nlinarith [hA2, hC2]

  have hAsum :
      A * (B + C) ≤ 2 * E := by
    rw [mul_add]
    linarith

  have hScaledGQ :
      A * (2 * G * Q)
        ≤
      A * (3 * h * (B + C)) :=
    mul_le_mul_of_nonneg_left hGQ hA

  have hScaledEnergy :
      3 * h * (A * (B + C))
        ≤
      3 * h * (2 * E) :=
    mul_le_mul_of_nonneg_left
      hAsum
      (mul_nonneg (by norm_num) hh)

  calc
    2 * A * G * Q
        =
      A * (2 * G * Q) := by
        ring
    _ ≤
      A * (3 * h * (B + C)) :=
        hScaledGQ
    _ =
      3 * h * (A * (B + C)) := by
        ring
    _ ≤
      3 * h * (2 * E) :=
        hScaledEnergy
    _ =
      6 * h * E := by
        ring

/--
Two Landau-controlled D² factors plus individual D³ energy domination produce
the exact `Holder244ProductBound` for one interpolation monomial, with constant
`6`.
-/
theorem holder244ProductBound_of_two_derivativeControls
    {f vG g dg vQ q dq : ScalarField3}
    {h E : ℝ}
    (
      hf2 :
        MeasureTheory.MemLp
          f
          (ENNReal.ofReal 2)
          volume
    )
    (hEnvG : LandauScalarEnvelope vG h)
    (hEnvQ : LandauScalarEnvelope vQ h)
    (hG : LandauDerivativeControl vG g dg h)
    (hQ : LandauDerivativeControl vQ q dq h)
    (hEnergyF : landauL2 f ^ 2 ≤ E)
    (hEnergyG : landauL2 dg ^ 2 ≤ E)
    (hEnergyQ : landauL2 dq ^ 2 ≤ E) :
    Holder244ProductBound
      f g q
      (6 * h * E) := by

  rcases hG with
    ⟨hg4, hGIBP, hGInt, hGCauchy⟩

  rcases hQ with
    ⟨hq4, hQIBP, hQInt, hQCauchy⟩

  have hGsq :
      landauL4 g ^ 2
        ≤
      3 * h * landauL2 dg := by
    apply
      landauL4_sq_le_of_derivativeControl
        hEnvG
    exact
      ⟨hg4, hGIBP, hGInt, hGCauchy⟩

  have hQsq :
      landauL4 q ^ 2
        ≤
      3 * h * landauL2 dq := by
    apply
      landauL4_sq_le_of_derivativeControl
        hEnvQ
    exact
      ⟨hq4, hQIBP, hQInt, hQCauchy⟩

  apply
    holder244ProductBound_of_real_norm_product
      hf2 hg4 hq4

  exact
    landau_three_factor_algebra_of_each_energy
      (landauL2_nonneg f)
      (landauL2_nonneg dg)
      (landauL2_nonneg dq)
      (landauL4_nonneg g)
      (landauL4_nonneg q)
      hEnvG.1
      hGsq
      hQsq
      hEnergyF
      hEnergyG
      hEnergyQ

/-! ## Gradient-envelope specialization -/

theorem landauScalarEnvelope_of_velocityGradientEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {h : ℝ → ℝ}
    {t : ℝ}
    (hh : 0 ≤ h t)
    (hGrad : VelocityGradientEnvelope u h t)
    (a c : Axis Depth.three) :
    LandauScalarEnvelope
      (
        spatial3.d a
          (loggedVelocityComponent u t c)
      )
      (h t) := by

  refine ⟨hh, ?_⟩
  intro x
  exact hGrad a c x

/-! ## Tuplewise analytic data -/

structure H3InterpolationTupleLandauData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (h : ℝ → ℝ)
    (t : ℝ)
    (i k l j r : Axis Depth.three) : Prop where

  f_memLp2 :
    MeasureTheory.MemLp
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
      (ENNReal.ofReal 2)
      volume

  f_energy :
    landauL2
        (
          spatial3.d i
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t j)
                )
            )
        ) ^ 2
      ≤
    velocityH3Energy3At u t

  g1_control :
    LandauDerivativeControl
      (
        spatial3.d l
          (loggedVelocityComponent u t r)
      )
      (
        spatial3.d k
          (
            spatial3.d l
              (loggedVelocityComponent u t r)
          )
      )
      (
        spatial3.d k
          (
            spatial3.d k
              (
                spatial3.d l
                  (loggedVelocityComponent u t r)
              )
          )
      )
      (h t)

  g1_energy :
    landauL2
        (
          spatial3.d k
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t r)
                )
            )
        ) ^ 2
      ≤
    velocityH3Energy3At u t

  q1_control :
    LandauDerivativeControl
      (
        spatial3.d r
          (loggedVelocityComponent u t j)
      )
      (
        spatial3.d i
          (
            spatial3.d r
              (loggedVelocityComponent u t j)
          )
      )
      (
        spatial3.d i
          (
            spatial3.d i
              (
                spatial3.d r
                  (loggedVelocityComponent u t j)
              )
          )
      )
      (h t)

  q1_energy :
    landauL2
        (
          spatial3.d i
            (
              spatial3.d i
                (
                  spatial3.d r
                    (loggedVelocityComponent u t j)
                )
            )
        ) ^ 2
      ≤
    velocityH3Energy3At u t

  g2_control :
    LandauDerivativeControl
      (
        spatial3.d l
          (loggedVelocityComponent u t r)
      )
      (
        spatial3.d i
          (
            spatial3.d l
              (loggedVelocityComponent u t r)
          )
      )
      (
        spatial3.d i
          (
            spatial3.d i
              (
                spatial3.d l
                  (loggedVelocityComponent u t r)
              )
          )
      )
      (h t)

  g2_energy :
    landauL2
        (
          spatial3.d i
            (
              spatial3.d i
                (
                  spatial3.d l
                    (loggedVelocityComponent u t r)
                )
            )
        ) ^ 2
      ≤
    velocityH3Energy3At u t

  q2_control :
    LandauDerivativeControl
      (
        spatial3.d r
          (loggedVelocityComponent u t j)
      )
      (
        spatial3.d k
          (
            spatial3.d r
              (loggedVelocityComponent u t j)
          )
      )
      (
        spatial3.d k
          (
            spatial3.d k
              (
                spatial3.d r
                  (loggedVelocityComponent u t j)
              )
          )
      )
      (h t)

  q2_energy :
    landauL2
        (
          spatial3.d k
            (
              spatial3.d k
                (
                  spatial3.d r
                    (loggedVelocityComponent u t j)
                )
            )
        ) ^ 2
      ≤
    velocityH3Energy3At u t

  g3_control :
    LandauDerivativeControl
      (
        spatial3.d k
          (loggedVelocityComponent u t r)
      )
      (
        spatial3.d i
          (
            spatial3.d k
              (loggedVelocityComponent u t r)
          )
      )
      (
        spatial3.d i
          (
            spatial3.d i
              (
                spatial3.d k
                  (loggedVelocityComponent u t r)
              )
          )
      )
      (h t)

  g3_energy :
    landauL2
        (
          spatial3.d i
            (
              spatial3.d i
                (
                  spatial3.d k
                    (loggedVelocityComponent u t r)
                )
            )
        ) ^ 2
      ≤
    velocityH3Energy3At u t

  q3_control :
    LandauDerivativeControl
      (
        spatial3.d l
          (loggedVelocityComponent u t j)
      )
      (
        spatial3.d r
          (
            spatial3.d l
              (loggedVelocityComponent u t j)
          )
      )
      (
        spatial3.d r
          (
            spatial3.d r
              (
                spatial3.d l
                  (loggedVelocityComponent u t j)
              )
          )
      )
      (h t)

  q3_energy :
    landauL2
        (
          spatial3.d r
            (
              spatial3.d r
                (
                  spatial3.d l
                    (loggedVelocityComponent u t j)
                )
            )
        ) ^ 2
      ≤
    velocityH3Energy3At u t

def H3OrderThreeInterpolationLandauDataAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (h : ℝ → ℝ)
    (t : ℝ) : Prop :=
  0 ≤ h t
    ∧
  VelocityGradientEnvelope u h t
    ∧
  ∀ i k l j r : Axis Depth.three,
    H3InterpolationTupleLandauData
      u h t i k l j r

/--
The corrected tuplewise Landau data imply the existing Hölder-Landau condition
with constant `6`.
-/
theorem h3OrderThreeInterpolationHolderLandauAt_of_landauData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hData :
        H3OrderThreeInterpolationLandauDataAt
          u h t
    ) :
    H3OrderThreeInterpolationHolderLandauAt
      u h t 6 := by

  rcases hData with
    ⟨hh, hGrad, hTuple⟩

  refine ⟨by norm_num, hh, ?_⟩

  intro i k l j r

  have hD :=
    hTuple i k l j r

  let f : ScalarField3 :=
    spatial3.d i
      (
        spatial3.d k
          (
            spatial3.d l
              (loggedVelocityComponent u t j)
          )
      )

  let g1 : ScalarField3 :=
    spatial3.d k
      (
        spatial3.d l
          (loggedVelocityComponent u t r)
      )

  let q1 : ScalarField3 :=
    spatial3.d i
      (
        spatial3.d r
          (loggedVelocityComponent u t j)
      )

  let g2 : ScalarField3 :=
    spatial3.d i
      (
        spatial3.d l
          (loggedVelocityComponent u t r)
      )

  let q2 : ScalarField3 :=
    spatial3.d k
      (
        spatial3.d r
          (loggedVelocityComponent u t j)
      )

  let g3 : ScalarField3 :=
    spatial3.d i
      (
        spatial3.d k
          (loggedVelocityComponent u t r)
      )

  let q3 : ScalarField3 :=
    spatial3.d r
      (
        spatial3.d l
          (loggedVelocityComponent u t j)
      )

  let dg1 : ScalarField3 := spatial3.d k g1
  let dq1 : ScalarField3 := spatial3.d i q1
  let dg2 : ScalarField3 := spatial3.d i g2
  let dq2 : ScalarField3 := spatial3.d k q2
  let dg3 : ScalarField3 := spatial3.d i g3
  let dq3 : ScalarField3 := spatial3.d r q3

  have hEnvG1 :
      LandauScalarEnvelope
        (
          spatial3.d l
            (loggedVelocityComponent u t r)
        )
        (h t) :=
    landauScalarEnvelope_of_velocityGradientEnvelope
      hh hGrad l r

  have hEnvQ1 :
      LandauScalarEnvelope
        (
          spatial3.d r
            (loggedVelocityComponent u t j)
        )
        (h t) :=
    landauScalarEnvelope_of_velocityGradientEnvelope
      hh hGrad r j

  have hEnvG3 :
      LandauScalarEnvelope
        (
          spatial3.d k
            (loggedVelocityComponent u t r)
        )
        (h t) :=
    landauScalarEnvelope_of_velocityGradientEnvelope
      hh hGrad k r

  have hEnvQ3 :
      LandauScalarEnvelope
        (
          spatial3.d l
            (loggedVelocityComponent u t j)
        )
        (h t) :=
    landauScalarEnvelope_of_velocityGradientEnvelope
      hh hGrad l j

  have h1 :
      Holder244ProductBound
        f g1 q1
        (6 * h t * velocityH3Energy3At u t) := by

    apply
      holder244ProductBound_of_two_derivativeControls
        hD.f_memLp2
        hEnvG1
        hEnvQ1

    · simpa [g1, dg1] using hD.g1_control
    · simpa [q1, dq1] using hD.q1_control
    · simpa [f] using hD.f_energy
    · simpa [dg1, g1] using hD.g1_energy
    · simpa [dq1, q1] using hD.q1_energy

  have h2 :
      Holder244ProductBound
        f g2 q2
        (6 * h t * velocityH3Energy3At u t) := by

    apply
      holder244ProductBound_of_two_derivativeControls
        hD.f_memLp2
        hEnvG1
        hEnvQ1

    · simpa [g2, dg2] using hD.g2_control
    · simpa [q2, dq2] using hD.q2_control
    · simpa [f] using hD.f_energy
    · simpa [dg2, g2] using hD.g2_energy
    · simpa [dq2, q2] using hD.q2_energy

  have h3 :
      Holder244ProductBound
        f g3 q3
        (6 * h t * velocityH3Energy3At u t) := by

    apply
      holder244ProductBound_of_two_derivativeControls
        hD.f_memLp2
        hEnvG3
        hEnvQ3

    · simpa [g3, dg3] using hD.g3_control
    · simpa [q3, dq3] using hD.q3_control
    · simpa [f] using hD.f_energy
    · simpa [dg3, g3] using hD.g3_energy
    · simpa [dq3, q3] using hD.q3_energy

  simpa [f, g1, q1, g2, q2, g3, q3] using
    And.intro h1 (And.intro h2 h3)

end Euclidean
end Bridge
end PrimeTensor

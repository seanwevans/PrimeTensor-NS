import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationLandauMonomials

/-!
# Third-order H³ interpolation: Landau energy bookkeeping

The analytic Landau controls are now separated from the finite H³ energy
bookkeeping.

This file proves three facts:

1. The real root-form quantity used by the Landau argument satisfies

       landauL2 f ^ 2 = spatialSquareEnergy f.

2. Every individual third-order spatial square-energy summand is bounded by
   the total third-order velocity energy `velocityH3Energy3At`.

3. Consequently all seven energy fields in
   `H3InterpolationTupleLandauData` can be filled automatically.  The caller
   only supplies the genuinely analytic information: Lp membership, whole-space
   quartic integration by parts/integrability, and the gradient envelope.

No decay or integration-by-parts fact is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable local instance axisFintypeH3LandauEnergyBookkeeping
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3EnergyDerivative d

noncomputable local instance point3MeasureSpaceH3LandauEnergyBookkeeping :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3EnergyDerivative Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Root form = square energy -/

theorem landauL2_sq_eq_spatialSquareEnergy
    (f : ScalarField3) :
    landauL2 f ^ 2
      =
    spatialSquareEnergy f := by

  have hI :
      0 ≤
        ∫ x : Point3,
          (f x) ^ 2 := by
    exact
      MeasureTheory.integral_nonneg
        (fun x : Point3 => by positivity)

  unfold landauL2 spatialSquareEnergy

  rw [pow_two]

  rw [
    ← Real.rpow_add_of_nonneg
        hI
        (by norm_num : 0 ≤ (1 / (2 : ℝ)))
        (by norm_num : 0 ≤ (1 / (2 : ℝ)))
  ]

  norm_num

/-! ## One H³ summand is bounded by the total H³ energy -/

theorem spatialSquareEnergy_third_le_velocityH3Energy3At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (j i k l : Axis Depth.three) :
    spatialSquareEnergy
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
      ≤
    velocityH3Energy3At u t := by

  unfold velocityH3Energy3At

  have hL :
      spatialSquareEnergy
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
        ≤
      ∑ l' : Axis Depth.three,
        spatialSquareEnergy
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l'
                      (loggedVelocityComponent u t j)
                  )
              )
          ) := by

    simpa using
      (
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Axis Depth.three)))
          (f := fun l' =>
            spatialSquareEnergy
              (
                spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l'
                          (loggedVelocityComponent u t j)
                      )
                  )
              ))
          (fun l' _ =>
            spatialSquareEnergy_nonneg _)
          (Finset.mem_univ l)
      )

  have hK :
      (
        ∑ l' : Axis Depth.three,
          spatialSquareEnergy
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l'
                        (loggedVelocityComponent u t j)
                    )
                )
            )
      )
        ≤
      ∑ k' : Axis Depth.three,
        ∑ l' : Axis Depth.three,
          spatialSquareEnergy
            (
              spatial3.d i
                (
                  spatial3.d k'
                    (
                      spatial3.d l'
                        (loggedVelocityComponent u t j)
                    )
                )
            ) := by

    simpa using
      (
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Axis Depth.three)))
          (f := fun k' =>
            ∑ l' : Axis Depth.three,
              spatialSquareEnergy
                (
                  spatial3.d i
                    (
                      spatial3.d k'
                        (
                          spatial3.d l'
                            (loggedVelocityComponent u t j)
                        )
                    )
                ))
          (fun k' _ =>
            Finset.sum_nonneg
              (fun l' _ =>
                spatialSquareEnergy_nonneg _))
          (Finset.mem_univ k)
      )

  have hI :
      (
        ∑ k' : Axis Depth.three,
          ∑ l' : Axis Depth.three,
            spatialSquareEnergy
              (
                spatial3.d i
                  (
                    spatial3.d k'
                      (
                        spatial3.d l'
                          (loggedVelocityComponent u t j)
                      )
                  )
              )
      )
        ≤
      ∑ i' : Axis Depth.three,
        ∑ k' : Axis Depth.three,
          ∑ l' : Axis Depth.three,
            spatialSquareEnergy
              (
                spatial3.d i'
                  (
                    spatial3.d k'
                      (
                        spatial3.d l'
                          (loggedVelocityComponent u t j)
                      )
                  )
              ) := by

    simpa using
      (
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Axis Depth.three)))
          (f := fun i' =>
            ∑ k' : Axis Depth.three,
              ∑ l' : Axis Depth.three,
                spatialSquareEnergy
                  (
                    spatial3.d i'
                      (
                        spatial3.d k'
                          (
                            spatial3.d l'
                              (loggedVelocityComponent u t j)
                          )
                      )
                  ))
          (fun i' _ =>
            Finset.sum_nonneg
              (fun k' _ =>
                Finset.sum_nonneg
                  (fun l' _ =>
                    spatialSquareEnergy_nonneg _)))
          (Finset.mem_univ i)
      )

  have hJ :
      (
        ∑ i' : Axis Depth.three,
          ∑ k' : Axis Depth.three,
            ∑ l' : Axis Depth.three,
              spatialSquareEnergy
                (
                  spatial3.d i'
                    (
                      spatial3.d k'
                        (
                          spatial3.d l'
                            (loggedVelocityComponent u t j)
                        )
                    )
                )
      )
        ≤
      ∑ j' : Axis Depth.three,
        ∑ i' : Axis Depth.three,
          ∑ k' : Axis Depth.three,
            ∑ l' : Axis Depth.three,
              spatialSquareEnergy
                (
                  spatial3.d i'
                    (
                      spatial3.d k'
                        (
                          spatial3.d l'
                            (loggedVelocityComponent u t j')
                        )
                    )
                ) := by

    simpa using
      (
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Axis Depth.three)))
          (f := fun j' =>
            ∑ i' : Axis Depth.three,
              ∑ k' : Axis Depth.three,
                ∑ l' : Axis Depth.three,
                  spatialSquareEnergy
                    (
                      spatial3.d i'
                        (
                          spatial3.d k'
                            (
                              spatial3.d l'
                                (loggedVelocityComponent u t j')
                            )
                        )
                    ))
          (fun j' _ =>
            Finset.sum_nonneg
              (fun i' _ =>
                Finset.sum_nonneg
                  (fun k' _ =>
                    Finset.sum_nonneg
                      (fun l' _ =>
                        spatialSquareEnergy_nonneg _))))
          (Finset.mem_univ j)
      )

  exact hL.trans (hK.trans (hI.trans hJ))

theorem landauL2_third_sq_le_velocityH3Energy3At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (j i k l : Axis Depth.three) :
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
    velocityH3Energy3At u t := by

  rw [landauL2_sq_eq_spatialSquareEnergy]

  exact
    spatialSquareEnergy_third_le_velocityH3Energy3At
      u t j i k l

/-! ## Analytic data with energy bookkeeping removed -/

/--
The genuinely analytic data for one interpolation tuple.

Unlike `H3InterpolationTupleLandauData`, this structure contains no energy
inequalities: those are consequences of the definition of `velocityH3Energy3At`
and are filled automatically below.
-/
structure H3InterpolationTupleLandauAnalyticData
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

/--
Fill every energy field of `H3InterpolationTupleLandauData` automatically.
-/
theorem h3InterpolationTupleLandauData_of_analyticData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {h : ℝ → ℝ}
    {t : ℝ}
    {i k l j r : Axis Depth.three}
    (
      hA :
        H3InterpolationTupleLandauAnalyticData
          u h t i k l j r
    ) :
    H3InterpolationTupleLandauData
      u h t i k l j r := by

  refine
    {
      f_memLp2 := hA.f_memLp2
      f_energy := ?_
      g1_control := hA.g1_control
      g1_energy := ?_
      q1_control := hA.q1_control
      q1_energy := ?_
      g2_control := hA.g2_control
      g2_energy := ?_
      q2_control := hA.q2_control
      q2_energy := ?_
      g3_control := hA.g3_control
      g3_energy := ?_
      q3_control := hA.q3_control
      q3_energy := ?_
    }

  · exact
      landauL2_third_sq_le_velocityH3Energy3At
        u t j i k l

  · exact
      landauL2_third_sq_le_velocityH3Energy3At
        u t r k k l

  · exact
      landauL2_third_sq_le_velocityH3Energy3At
        u t j i i r

  · exact
      landauL2_third_sq_le_velocityH3Energy3At
        u t r i i l

  · exact
      landauL2_third_sq_le_velocityH3Energy3At
        u t j k k r

  · exact
      landauL2_third_sq_le_velocityH3Energy3At
        u t r i i k

  · exact
      landauL2_third_sq_le_velocityH3Energy3At
        u t j r r l

/-! ## Global analytic data -/

def H3OrderThreeInterpolationLandauAnalyticDataAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (h : ℝ → ℝ)
    (t : ℝ) : Prop :=
  0 ≤ h t
    ∧
  VelocityGradientEnvelope u h t
    ∧
  ∀ i k l j r : Axis Depth.three,
    H3InterpolationTupleLandauAnalyticData
      u h t i k l j r

theorem h3OrderThreeInterpolationLandauDataAt_of_analyticData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hA :
        H3OrderThreeInterpolationLandauAnalyticDataAt
          u h t
    ) :
    H3OrderThreeInterpolationLandauDataAt
      u h t := by

  rcases hA with
    ⟨hh, hGrad, hTuple⟩

  refine
    ⟨
      hh,
      hGrad,
      ?_
    ⟩

  intro i k l j r

  exact
    h3InterpolationTupleLandauData_of_analyticData
      (hTuple i k l j r)

/--
Direct analytic-data-to-Hölder closure with the corrected constant `6`.
-/
theorem h3OrderThreeInterpolationHolderLandauAt_of_analyticData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hA :
        H3OrderThreeInterpolationLandauAnalyticDataAt
          u h t
    ) :
    H3OrderThreeInterpolationHolderLandauAt
      u h t 6 := by

  exact
    h3OrderThreeInterpolationHolderLandauAt_of_landauData
      (
        h3OrderThreeInterpolationLandauDataAt_of_analyticData
          hA
      )

end Euclidean
end Bridge
end PrimeTensor

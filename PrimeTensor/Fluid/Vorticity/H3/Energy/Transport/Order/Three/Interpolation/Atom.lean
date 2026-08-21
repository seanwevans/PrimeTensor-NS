import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Monomials

/-!
# Third-order H³ transport: analytic atom frontier

The hard third-order transport bookkeeping has already reduced the interpolation
block to nine scalar triple products for each `(i,k,l,j)` tuple.

This file isolates the exact analytic estimate still required for one such
triple product:

    |∫ D³u · D²u · D²u|
      ≤ K * h(t) * ∫ |D³u|².

Here `h(t)` is the gradient envelope used by the transport estimate.  The
intended analytic proof of this atom is the standard two-step route

    Hölder:
      |∫ D³u · A · B|
        ≤ ‖D³u‖₂ ‖A‖₄ ‖B‖₄,

followed by the whole-space interpolation estimate

      ‖A‖₄ ‖B‖₄
        ≤ C * h(t) * ‖D³u‖₂.

No such interpolation theorem is assumed silently here.  Instead,
`H3OrderThreeInterpolationAtomEstimateAt` names exactly the remaining analytic
frontier.

The rest of this file is finite-energy bookkeeping:

* every individual third-derivative square energy is bounded by `E₃`;
* an atom estimate therefore implies the monomial estimate;
* hence the already-proved `729*K` global interpolation bound follows.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderThreeInterpolationAtom
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
Every individual third-order square energy is bounded by the canonical
third-order energy `E₃`.
-/
theorem thirdDerivativeSquareEnergy_le_velocityH3Energy3At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three) :
    spatialSquareEnergy
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
      ≤
    velocityH3Energy3At u t := by

  classical

  have hL :
      spatialSquareEnergy
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
        ≤
      ∑ q : PrimeTensor.Axis Depth.three,
        spatialSquareEnergy
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (
                    spatial3.d
                      q
                      (loggedVelocityComponent u t j)
                  )
              )
          ) := by

    apply
      Finset.single_le_sum
        (fun q _ =>
          spatialSquareEnergy_nonneg
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        q
                        (loggedVelocityComponent u t j)
                    )
                )
            ))

    simp

  have hK :
      (
        ∑ q : PrimeTensor.Axis Depth.three,
          spatialSquareEnergy
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        q
                        (loggedVelocityComponent u t j)
                    )
                )
            )
      )
        ≤
      ∑ p : PrimeTensor.Axis Depth.three,
        ∑ q : PrimeTensor.Axis Depth.three,
          spatialSquareEnergy
            (
              spatial3.d
                i
                (
                  spatial3.d
                    p
                    (
                      spatial3.d
                        q
                        (loggedVelocityComponent u t j)
                    )
                )
            ) := by

    apply
      Finset.single_le_sum
        (fun p _ =>
          Finset.sum_nonneg
            (fun q _ =>
              spatialSquareEnergy_nonneg
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        p
                        (
                          spatial3.d
                            q
                            (loggedVelocityComponent u t j)
                        )
                    )
                )))

    simp

  have hI :
      (
        ∑ p : PrimeTensor.Axis Depth.three,
          ∑ q : PrimeTensor.Axis Depth.three,
            spatialSquareEnergy
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      p
                      (
                        spatial3.d
                          q
                          (loggedVelocityComponent u t j)
                      )
                  )
              )
      )
        ≤
      ∑ r : PrimeTensor.Axis Depth.three,
        ∑ p : PrimeTensor.Axis Depth.three,
          ∑ q : PrimeTensor.Axis Depth.three,
            spatialSquareEnergy
              (
                spatial3.d
                  r
                  (
                    spatial3.d
                      p
                      (
                        spatial3.d
                          q
                          (loggedVelocityComponent u t j)
                      )
                  )
              ) := by

    apply
      Finset.single_le_sum
        (fun r _ =>
          Finset.sum_nonneg
            (fun p _ =>
              Finset.sum_nonneg
                (fun q _ =>
                  spatialSquareEnergy_nonneg
                    (
                      spatial3.d
                        r
                        (
                          spatial3.d
                            p
                            (
                              spatial3.d
                                q
                                (loggedVelocityComponent u t j)
                            )
                        )
                    ))))

    simp

  have hJ :
      (
        ∑ r : PrimeTensor.Axis Depth.three,
          ∑ p : PrimeTensor.Axis Depth.three,
            ∑ q : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (
                  spatial3.d
                    r
                    (
                      spatial3.d
                        p
                        (
                          spatial3.d
                            q
                            (loggedVelocityComponent u t j)
                        )
                    )
                )
      )
        ≤
      velocityH3Energy3At u t := by

    unfold velocityH3Energy3At

    apply
      Finset.single_le_sum
        (fun s _ =>
          Finset.sum_nonneg
            (fun r _ =>
              Finset.sum_nonneg
                (fun p _ =>
                  Finset.sum_nonneg
                    (fun q _ =>
                      spatialSquareEnergy_nonneg
                        (
                          spatial3.d
                            r
                            (
                              spatial3.d
                                p
                                (
                                  spatial3.d
                                    q
                                    (loggedVelocityComponent u t s)
                                )
                            )
                        )))))

    simp

  exact
    le_trans
      hL
      (
        le_trans
          hK
          (
            le_trans
              hI
              hJ
          )
      )

/--
The exact remaining analytic atom for the hard third-order interpolation terms.

For each of the three `D²u · D²u` monomials, pairing against the corresponding
`D³u` is bounded by `K * h(t)` times the square energy of that same `D³u`.

The explicit nonnegativity of `h(t)` is retained because the later passage from
one square-energy term to the total `E₃` multiplies an inequality by
`K * h(t)`.
-/
def H3OrderThreeInterpolationAtomEstimateAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (h : ℝ → ℝ)
    (t K : ℝ) : Prop :=
  0 ≤ K
    ∧
  0 ≤ h t
    ∧
  ∀ i k l j r : PrimeTensor.Axis Depth.three,
    let f :=
      spatial3.d i
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t j)
            )
        )
    abs
        (
          spatialEnergyPairing
            f
            (thirdOrderInterpolationMonomial1 u t i k l j r)
        )
      ≤
    K * h t * spatialSquareEnergy f
      ∧
    abs
        (
          spatialEnergyPairing
            f
            (thirdOrderInterpolationMonomial2 u t i k l j r)
        )
      ≤
    K * h t * spatialSquareEnergy f
      ∧
    abs
        (
          spatialEnergyPairing
            f
            (thirdOrderInterpolationMonomial3 u t i k l j r)
        )
      ≤
    K * h t * spatialSquareEnergy f

/--
The local analytic atom implies the monomial estimate used by the finite
third-order interpolation bookkeeping.
-/
theorem h3OrderThreeInterpolationMonomialEstimateAt_of_atomEstimate
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t K : ℝ}
    (
      hAtom :
        H3OrderThreeInterpolationAtomEstimateAt
          u h t K
    ) :
    H3OrderThreeInterpolationMonomialEstimateAt
      u h t K := by

  rcases hAtom with
    ⟨hK, hHt, hAtom⟩

  refine
    ⟨hK, ?_⟩

  intro i k l j r

  have hTuple :=
    hAtom i k l j r

  dsimp only at hTuple ⊢

  rcases hTuple with
    ⟨h1, h2, h3⟩

  have hEnergy :
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
      velocityH3Energy3At u t :=
    thirdDerivativeSquareEnergy_le_velocityH3Energy3At
      u t i k l j

  have hCoeff :
      0 ≤ K * h t :=
    mul_nonneg hK hHt

  have hScaled :
      K * h t
          *
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
      K * h t * velocityH3Energy3At u t :=
    mul_le_mul_of_nonneg_left
      hEnergy
      hCoeff

  constructor

  · exact
      le_trans
        h1
        hScaled

  constructor

  · exact
      le_trans
        h2
        hScaled

  · exact
      le_trans
        h3
        hScaled

/--
Once the analytic atom is available, the complete interpolation frontier closes
with the same deliberately coarse global constant `729*K`.
-/
theorem h3OrderThreeInterpolationEstimateAt_of_atomEstimate
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t K : ℝ}
    (
      hInt :
        H3OrderThreeInterpolationMonomialPairingIntegrableAt
          u t
    )
    (
      hAtom :
        H3OrderThreeInterpolationAtomEstimateAt
          u h t K
    ) :
    H3OrderThreeInterpolationEstimateAt
      u h t (729 * K) := by

  exact
    h3OrderThreeInterpolationEstimateAt_of_monomials
      hInt
      (
        h3OrderThreeInterpolationMonomialEstimateAt_of_atomEstimate
          hAtom
      )

end Euclidean
end Bridge
end PrimeTensor

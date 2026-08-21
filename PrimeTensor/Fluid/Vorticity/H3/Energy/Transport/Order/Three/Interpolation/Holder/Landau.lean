import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Holder.Pairing
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Monomials

/-!
# Third-order H³ interpolation: Hölder-to-Landau frontier

The measure-theoretic 2-4-4 Hölder step is now proved.  This file isolates the
remaining genuine harmonic-analysis input in the exact form needed by the
existing monomial bookkeeping.

For one triple product

    2 ∫ f g q,

Hölder gives

    ‖2 ∫ f g q‖ₑ
      ≤ ‖2‖ₑ ‖f‖₂ ‖g‖₄ ‖q‖₄.

The remaining Landau/Gagliardo--Nirenberg input is therefore only the estimate

    ‖2‖ₑ ‖f‖₂ ‖g‖₄ ‖q‖₄
      ≤ ofReal (K * h(t) * E₃(t)).

No componentwise `D³` square-energy bound is imposed here; the target is the
total third-order energy `velocityH3Energy3At`, which is exactly what the
monomial layer consumes.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

/--
Recreate the exact axis enumeration used when `spatialEnergyPairing` was
elaborated.
-/
noncomputable local instance axisFintypeH3HolderLandau
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3EnergyDerivative d

/--
Recreate the exact product measure-space underlying `spatialEnergyPairing`.
-/
noncomputable local instance point3MeasureSpaceH3HolderLandau :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3EnergyDerivative Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
A single real triple product satisfies the measurable 2-4-4 hypotheses, and
its Hölder norm product is bounded by the finite real target `R`.
-/
def Holder244ProductBound
    (f g q : ScalarField3)
    (R : ℝ) : Prop :=
  AEMeasurable
      (fun x : Point3 => ‖f x‖ₑ)
      MeasureTheory.volume
    ∧
  AEMeasurable
      (fun x : Point3 => ‖g x‖ₑ)
      MeasureTheory.volume
    ∧
  AEMeasurable
      (fun x : Point3 => ‖q x‖ₑ)
      MeasureTheory.volume
    ∧
  ‖(2 : ℝ)‖ₑ
      *
    (
      realLpEnorm MeasureTheory.volume 2 f
        *
      (
        realLpEnorm MeasureTheory.volume 4 g
          *
        realLpEnorm MeasureTheory.volume 4 q
      )
    )
      ≤
    ENNReal.ofReal R

/--
The green 2-4-4 Hölder theorem plus a finite Hölder-product bound gives the
corresponding ordinary real absolute-value estimate.
-/
theorem abs_spatialEnergyPairing_mul_le_of_holder244ProductBound
    {f g q : ScalarField3}
    {R : ℝ}
    (hR : 0 ≤ R)
    (hBound : Holder244ProductBound f g q R) :
    abs
        (
          spatialEnergyPairing
            f
            (fun x : Point3 => g x * q x)
        )
      ≤
    R := by

  rcases hBound with
    ⟨hF, hG, hQ, hProduct⟩

  have hHolder :
      ‖
        spatialEnergyPairing
          f
          (fun x : Point3 => g x * q x)
      ‖ₑ
        ≤
      ‖(2 : ℝ)‖ₑ
        *
      (
        realLpEnorm MeasureTheory.volume 2 f
          *
        (
          realLpEnorm MeasureTheory.volume 4 g
            *
          realLpEnorm MeasureTheory.volume 4 q
        )
      ) := by

    exact
      enorm_spatialEnergyPairing_mul_le_244
        (f := f)
        (g := g)
        (q := q)
        hF hG hQ

  have hEnorm :
      ‖
        spatialEnergyPairing
          f
          (fun x : Point3 => g x * q x)
      ‖ₑ
        ≤
      ENNReal.ofReal R :=
    le_trans hHolder hProduct

  have hReal :
      (
        ‖
          spatialEnergyPairing
            f
            (fun x : Point3 => g x * q x)
        ‖ₑ
      ).toReal
        ≤
      R :=
    ENNReal.toReal_le_of_le_ofReal
      hR
      hEnorm

  simpa only [
    toReal_enorm,
    Real.norm_eq_abs
  ] using hReal

/--
The exact remaining Landau/Gagliardo--Nirenberg frontier at one time.

For every coordinate quintuple `(i,k,l,j,r)`, the three `D²u · D²u`
monomials are required only to satisfy the post-Hölder product estimate against
the total third-order energy.
-/
def H3OrderThreeInterpolationHolderLandauAt
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
    let g1 :=
      spatial3.d k
        (
          spatial3.d l
            (loggedVelocityComponent u t r)
        )
    let q1 :=
      spatial3.d i
        (
          spatial3.d r
            (loggedVelocityComponent u t j)
        )
    let g2 :=
      spatial3.d i
        (
          spatial3.d l
            (loggedVelocityComponent u t r)
        )
    let q2 :=
      spatial3.d k
        (
          spatial3.d r
            (loggedVelocityComponent u t j)
        )
    let g3 :=
      spatial3.d i
        (
          spatial3.d k
            (loggedVelocityComponent u t r)
        )
    let q3 :=
      spatial3.d r
        (
          spatial3.d l
            (loggedVelocityComponent u t j)
        )
    let R :=
      K * h t * velocityH3Energy3At u t
    Holder244ProductBound f g1 q1 R
      ∧
    Holder244ProductBound f g2 q2 R
      ∧
    Holder244ProductBound f g3 q3 R

/--
The Hölder-to-Landau frontier implies exactly the monomial estimate already
consumed by the finite interpolation bookkeeping.
-/
theorem h3OrderThreeInterpolationMonomialEstimateAt_of_holderLandau
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t K : ℝ}
    (
      hLandau :
        H3OrderThreeInterpolationHolderLandauAt
          u h t K
    ) :
    H3OrderThreeInterpolationMonomialEstimateAt
      u h t K := by

  rcases hLandau with
    ⟨hK, hHt, hLandau⟩

  refine
    ⟨hK, ?_⟩

  intro i k l j r

  have hTuple :=
    hLandau i k l j r

  dsimp only at hTuple

  rcases hTuple with
    ⟨h1, h2, h3⟩

  have hR :
      0
        ≤
      K * h t * velocityH3Energy3At u t := by

    exact
      mul_nonneg
        (mul_nonneg hK hHt)
        (velocityH3Energy3At_nonneg u t)

  have hb1 :=
    abs_spatialEnergyPairing_mul_le_of_holder244ProductBound
      hR h1

  have hb2 :=
    abs_spatialEnergyPairing_mul_le_of_holder244ProductBound
      hR h2

  have hb3 :=
    abs_spatialEnergyPairing_mul_le_of_holder244ProductBound
      hR h3

  dsimp only

  constructor

  · change
      abs
          (
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
              (
                fun x : Point3 =>
                  spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t r)
                      )
                      x
                    *
                  spatial3.d i
                      (
                        spatial3.d r
                          (loggedVelocityComponent u t j)
                      )
                      x
              )
          )
        ≤
      K * h t * velocityH3Energy3At u t
    exact hb1

  constructor

  · change
      abs
          (
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
              (
                fun x : Point3 =>
                  spatial3.d i
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t r)
                      )
                      x
                    *
                  spatial3.d k
                      (
                        spatial3.d r
                          (loggedVelocityComponent u t j)
                      )
                      x
              )
          )
        ≤
      K * h t * velocityH3Energy3At u t
    exact hb2

  · change
      abs
          (
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
              (
                fun x : Point3 =>
                  spatial3.d i
                      (
                        spatial3.d k
                          (loggedVelocityComponent u t r)
                      )
                      x
                    *
                  spatial3.d r
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                      x
              )
          )
        ≤
      K * h t * velocityH3Energy3At u t
    exact hb3

/--
Once the genuine Landau/GN product estimate is supplied, the complete hard
third-order interpolation block closes with the existing coarse constant
`729*K`.
-/
theorem h3OrderThreeInterpolationEstimateAt_of_holderLandau
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
      hLandau :
        H3OrderThreeInterpolationHolderLandauAt
          u h t K
    ) :
    H3OrderThreeInterpolationEstimateAt
      u h t (729 * K) := by

  exact
    h3OrderThreeInterpolationEstimateAt_of_monomials
      hInt
      (
        h3OrderThreeInterpolationMonomialEstimateAt_of_holderLandau
          hLandau
      )

end Euclidean
end Bridge
end PrimeTensor

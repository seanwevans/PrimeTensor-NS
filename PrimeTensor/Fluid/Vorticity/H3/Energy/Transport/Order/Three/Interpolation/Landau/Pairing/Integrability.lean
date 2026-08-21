import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Data.Real.ConjExponents
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Energy.Bookkeeping
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Monomials

/-!
# Landau analytic data implies monomial pairing integrability

For each hard third-order interpolation monomial, the pairing has the form

    f * g * q

with

    f ∈ L²,
    g ∈ L⁴,
    q ∈ L⁴.

Hence

    g q ∈ L²
    and
    f (g q) ∈ L¹.

The `L²` datum for `f` and the `L⁴` data for `g,q` are already fields of
`H3InterpolationTupleLandauAnalyticData`.  Therefore the separate
`H3OrderThreeInterpolationMonomialPairingIntegrableAt` hypothesis is redundant.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped ENNReal NNReal

noncomputable local instance axisFintypeH3LandauPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3LandauPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3LandauPairing Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

local instance holderTripleFourFourTwo :
    ENNReal.HolderTriple
      (4 : ENNReal)
      (4 : ENNReal)
      (2 : ENNReal) := by

  have hReal :
      Real.HolderTriple
        4 4 2 := by
    rw [Real.holderTriple_iff]
    norm_num

  simpa using
    hReal.ennrealOfReal

local instance holderTripleTwoTwoOne :
    ENNReal.HolderTriple
      (2 : ENNReal)
      (2 : ENNReal)
      (1 : ENNReal) := by
  infer_instance

/--
The scalar Hölder bookkeeping used by every interpolation monomial:

    L² * L⁴ * L⁴ ⊆ L¹.
-/
private theorem integrable_mul_mul_of_memLp_two_four_four
    {f g q : ScalarField3}
    (
      hf :
        MeasureTheory.MemLp
          f
          (ENNReal.ofReal 2)
          volume
    )
    (
      hg :
        MeasureTheory.MemLp
          g
          (ENNReal.ofReal 4)
          volume
    )
    (
      hq :
        MeasureTheory.MemLp
          q
          (ENNReal.ofReal 4)
          volume
    ) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          f x * (g x * q x)
      ) := by

  have hf2 :
      MeasureTheory.MemLp
        f
        (2 : ENNReal)
        volume := by
    simpa using hf

  have hg4 :
      MeasureTheory.MemLp
        g
        (4 : ENNReal)
        volume := by
    simpa using hg

  have hq4 :
      MeasureTheory.MemLp
        q
        (4 : ENNReal)
        volume := by
    simpa using hq

  have hgq2 :
      MeasureTheory.MemLp
        (
          fun x : Point3 =>
            g x * q x
        )
        (2 : ENNReal)
        volume := by
    exact
      hq4.mul'
        hg4

  have hfgq1 :
      MeasureTheory.MemLp
        (
          fun x : Point3 =>
            f x * (g x * q x)
        )
        (1 : ENNReal)
        volume := by
    exact
      hgq2.mul'
        hf2

  exact
    MeasureTheory.memLp_one_iff_integrable.mp
      hfgq1

/--
The global Landau analytic data already implies integrability of all nine hard
third-order interpolation monomial pairings.

This discharges the formerly independent
`H3OrderThreeInterpolationMonomialPairingIntegrableAt` hypothesis.
-/
theorem h3OrderThreeInterpolationMonomialPairingIntegrableAt_of_landauAnalyticData
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hA :
        H3OrderThreeInterpolationLandauAnalyticDataAt
          u h t
    ) :
    H3OrderThreeInterpolationMonomialPairingIntegrableAt
      u t := by

  intro i k l j r

  dsimp

  have hTuple :
      H3InterpolationTupleLandauAnalyticData
        u h t i k l j r :=
    hA.2.2 i k l j r

  refine
    ⟨
      ?_,
      ?_,
      ?_
    ⟩

  · simpa [
      thirdOrderInterpolationMonomial1
    ] using
      (
        integrable_mul_mul_of_memLp_two_four_four
          hTuple.f_memLp2
          hTuple.g1_control.1
          hTuple.q1_control.1
      )

  · simpa [
      thirdOrderInterpolationMonomial2
    ] using
      (
        integrable_mul_mul_of_memLp_two_four_four
          hTuple.f_memLp2
          hTuple.g2_control.1
          hTuple.q2_control.1
      )

  · simpa [
      thirdOrderInterpolationMonomial3
    ] using
      (
        integrable_mul_mul_of_memLp_two_four_four
          hTuple.f_memLp2
          hTuple.g3_control.1
          hTuple.q3_control.1
      )

end Euclidean
end Bridge
end PrimeTensor

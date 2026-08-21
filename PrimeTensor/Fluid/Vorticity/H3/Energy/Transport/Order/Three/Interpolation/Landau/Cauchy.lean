import Mathlib.MeasureTheory.Integral.MeanInequalities
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.IBP

/-!
# Third-order H³ interpolation: the Cauchy--Schwarz step

The Landau integration-by-parts reduction gives

    ∫ g⁴ ≤ 3 h ∫ |g|² |dg|.

This file applies Mathlib's real-valued Hölder inequality with conjugate
exponents `2,2` to the remaining product:

    ∫ |g|² |dg|
      ≤
    (∫ (|g|²)²)^(1/2) * (∫ |dg|²)^(1/2).

The next layer can identify `( |g|² )²` with `g⁴` and convert these roots to
the project's `realLpEnorm`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped ENNReal NNReal

noncomputable local instance axisFintypeH3LandauCauchy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3EnergyDerivative d

noncomputable local instance point3MeasureSpaceH3LandauCauchy :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3EnergyDerivative Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The exact `MemLp` data required by Mathlib's `2,2` Hölder theorem for the
Landau product.
-/
def LandauCauchyMemLp
    (g dg : ScalarField3) : Prop :=
  MeasureTheory.MemLp
      (fun x : Point3 => abs (g x) ^ 2)
      (ENNReal.ofReal 2)
      volume
    ∧
  MeasureTheory.MemLp
      (fun x : Point3 => abs (dg x))
      (ENNReal.ofReal 2)
      volume

/--
Cauchy--Schwarz/Hölder for the exact nonnegative product produced by the
quartic Landau integration-by-parts estimate.
-/
theorem landau_cauchy_integral_le
    {g dg : ScalarField3}
    (hLp : LandauCauchyMemLp g dg) :
    (
      ∫ x : Point3,
        abs (g x) ^ 2 * abs (dg x)
    )
      ≤
    (
      ∫ x : Point3,
        (abs (g x) ^ 2) ^ (2 : ℝ)
    ) ^ (1 / (2 : ℝ))
      *
    (
      ∫ x : Point3,
        abs (dg x) ^ (2 : ℝ)
    ) ^ (1 / (2 : ℝ)) := by

  rcases hLp with ⟨hg, hdg⟩

  exact
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall
        (fun x : Point3 => by positivity))
      (Filter.Eventually.of_forall
        (fun x : Point3 => by positivity))
      hg
      hdg

/--
Combining the explicit whole-space Landau IBP step with the `2,2` Hölder
bound gives the raw quartic interpolation inequality.
-/
theorem landau_quartic_integral_le_cauchy_product
    {v g dg : ScalarField3}
    {h : ℝ}
    (hIBP : LandauQuarticIntegrationByParts v g dg)
    (hEnv : LandauScalarEnvelope v h)
    (hInt : LandauQuarticEnvelopeIntegrable v g dg h)
    (hLp : LandauCauchyMemLp g dg) :
    (
      ∫ x : Point3,
        (g x) ^ 4
    )
      ≤
    3 * h *
      (
        (
          ∫ x : Point3,
            (abs (g x) ^ 2) ^ (2 : ℝ)
        ) ^ (1 / (2 : ℝ))
          *
        (
          ∫ x : Point3,
            abs (dg x) ^ (2 : ℝ)
        ) ^ (1 / (2 : ℝ))
      ) := by

  have hIBPBound :
      (
        ∫ x : Point3,
          (g x) ^ 4
      )
        ≤
      3 * h *
        (
          ∫ x : Point3,
            abs (g x) ^ 2 * abs (dg x)
        ) :=
    landau_quartic_integral_le_envelope_integral
      hIBP hEnv hInt

  have hCS :=
    landau_cauchy_integral_le
      (g := g)
      (dg := dg)
      hLp

  have hh : 0 ≤ h := hEnv.1
  have hscale : 0 ≤ 3 * h := by positivity

  exact
    le_trans
      hIBPBound
      (
        mul_le_mul_of_nonneg_left
          hCS
          hscale
      )

end Euclidean
end Bridge
end PrimeTensor

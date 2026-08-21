import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Atom
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Third-order H³ interpolation: Hölder API probe

This file is intentionally temporary.

The hard atom has the scalar form

    spatialEnergyPairing f (fun x => g x * q x)

with

    spatialEnergyPairing f m = 2 * ∫ x, f x * m x.

The intended analytic reduction is the 2-4-4 Hölder chain

    L¹(f * (g*q))
      <= L²(f) * L²(g*q)
      <= L²(f) * L⁴(g) * L⁴(q).

Before introducing the permanent theorem, this probe records the exact mathlib
declarations available in the repository's pinned toolchain.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

#check MeasureTheory.norm_integral_le_lintegral_norm
#check MeasureTheory.enorm_integral_le_lintegral_enorm

#check MeasureTheory.eLpNorm
#check MeasureTheory.eLpNorm'
#check MeasureTheory.eLpNorm_one_eq_lintegral_enorm
#check MeasureTheory.eLpNorm_nnreal_eq_lintegral
#check MeasureTheory.MemLp
#check MeasureTheory.MemLp.aestronglyMeasurable
#check MeasureTheory.MemLp.aemeasurable

#check ENNReal.lintegral_mul_le_Lp_mul_Lq
#check ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr

-- The two exponent identities needed by the planned Hölder chain.
example : (1 : ℝ) / 1 = 1 / 2 + 1 / 2 := by
  norm_num

example : (1 : ℝ) / 2 = 1 / 4 + 1 / 4 := by
  norm_num

-- Keep the project-side definitions visible in the same elaboration context.
#check spatialEnergyPairing
#check spatialSquareEnergy
#check H3OrderThreeInterpolationAtomEstimateAt
#check thirdOrderInterpolationMonomial1
#check thirdOrderInterpolationMonomial2
#check thirdOrderInterpolationMonomial3

end Euclidean
end Bridge
end PrimeTensor

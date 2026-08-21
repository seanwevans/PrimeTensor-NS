import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Energy.Bookkeeping

/-!
# Third-order H³ interpolation: direct Landau closure

All analytic and finite-energy bookkeeping layers are now in place.

This file records the direct consequence for the interpolation transport block:

    H3OrderThreeInterpolationLandauAnalyticDataAt u h t

implies the existing interpolation estimate with constant

    729 * 6 = 4374.

The factor `729` is the already-proved combinatorial factor:
81 derivative/component tuples times 9 scalar monomials per tuple.

The factor `6` is the corrected Landau/Hölder constant that remains valid when
third-derivative energy slots coincide.

No new analytic assumption is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

/--
Direct closure of the third-order interpolation block from the explicit Landau
analytic data.
-/
theorem h3OrderThreeInterpolationEstimateAt_of_landauAnalyticData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hPair :
        H3OrderThreeInterpolationMonomialPairingIntegrableAt
          u t
    )
    (
      hA :
        H3OrderThreeInterpolationLandauAnalyticDataAt
          u h t
    ) :
    H3OrderThreeInterpolationEstimateAt
      u h t 4374 := by

  have hHolder :
      H3OrderThreeInterpolationHolderLandauAt
        u h t 6 :=
    h3OrderThreeInterpolationHolderLandauAt_of_analyticData
      hA

  have hEstimate :
      H3OrderThreeInterpolationEstimateAt
        u h t (729 * 6) :=
    h3OrderThreeInterpolationEstimateAt_of_holderLandau
      hPair
      hHolder

  norm_num at hEstimate ⊢

  exact hEstimate

/--
The same closure with the combinatorial factor left visible.
-/
theorem h3OrderThreeInterpolationEstimateAt_of_landauAnalyticData_factored
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hPair :
        H3OrderThreeInterpolationMonomialPairingIntegrableAt
          u t
    )
    (
      hA :
        H3OrderThreeInterpolationLandauAnalyticDataAt
          u h t
    ) :
    H3OrderThreeInterpolationEstimateAt
      u h t (729 * 6) := by

  exact
    h3OrderThreeInterpolationEstimateAt_of_holderLandau
      hPair
      (
        h3OrderThreeInterpolationHolderLandauAt_of_analyticData
          hA
      )

end Euclidean
end Bridge
end PrimeTensor

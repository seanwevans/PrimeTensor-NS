import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Vorticity.Product.Integrable
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Fubini

/-!
# Endpoint-independent old vorticity Fubini interchange

The generic interval/spatial Fubini theorem and the restriction from the full
elapsed interval to a shortened target `q ≤ tau` are already independent of
endpoint continuity.

The only endpoint-dependent input in the older x/y/z wrapper theorems was the
source of product-space integrability.

That source is now available directly from `CanonicalH3TailDataFrom`, so this
file removes
`H3PreterminalCanonicalL2EndpointContinuousOnElapsed`
from all three compact-test vorticity temporal Fubini interchanges.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldVorticityFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongOldVorticityFubini :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Fubini interchange for the compactly tested x-vorticity temporal
derivative on every shortened elapsed target, directly from the H³ tail. -/
theorem intervalIntegral_h3PreterminalWeakVorticityXTemporalDerivative_swap_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    ∫ x : Point3,
      (∫ r in (0 : ℝ)..(q : ℝ),
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
            hNS (t + r) x))
      ∂volume := by
  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  exact
    intervalIntegral_h3WeakTest_continuousMapExtension_swap
      ψ
      (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
        hNS)
      t
      (q : ℝ)
      q.2.1
      hShort.1

/-- Fubini interchange for the compactly tested y-vorticity temporal
derivative on every shortened elapsed target, directly from the H³ tail. -/
theorem intervalIntegral_h3PreterminalWeakVorticityYTemporalDerivative_swap_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    ∫ x : Point3,
      (∫ r in (0 : ℝ)..(q : ℝ),
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
            hNS (t + r) x))
      ∂volume := by
  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  exact
    intervalIntegral_h3WeakTest_continuousMapExtension_swap
      ψ
      (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
        hNS)
      t
      (q : ℝ)
      q.2.1
      hShort.2.1

/-- Fubini interchange for the compactly tested z-vorticity temporal
derivative on every shortened elapsed target, directly from the H³ tail. -/
theorem intervalIntegral_h3PreterminalWeakVorticityZTemporalDerivative_swap_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    ∫ x : Point3,
      (∫ r in (0 : ℝ)..(q : ℝ),
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
            hNS (t + r) x))
      ∂volume := by
  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  exact
    intervalIntegral_h3WeakTest_continuousMapExtension_swap
      ψ
      (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
        hNS)
      t
      (q : ℝ)
      q.2.1
      hShort.2.2

end

end Euclidean
end Bridge
end PrimeTensor

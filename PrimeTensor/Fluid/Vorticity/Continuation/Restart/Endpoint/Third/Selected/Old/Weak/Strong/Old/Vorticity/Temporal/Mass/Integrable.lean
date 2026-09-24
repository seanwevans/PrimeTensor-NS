import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Vorticity.Spatial.Mass.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.TemporalMassIntegrable

/-!
# Endpoint-independent old vorticity temporal-mass integrability

The previous increment gives a uniform `CanonicalH3TailDataFrom` bound for each
of the three actual old-vorticity temporal spatial norm masses:

    r ↦ ∫ ‖ψ(x) · ∂ₜωᵢ(t+r,x)‖ dx.

Their elapsed-time measurability is already endpoint-independent, coming from
joint measurability of the zero-extended temporal derivatives.

Hence each path is integrable on the finite interval `Ioo 0 tau` by the same
generic measurable-and-bounded argument used in the endpoint-era proof.

This file removes
`H3PreterminalCanonicalL2EndpointContinuousOnElapsed` from the full scalar
vorticity temporal-mass finiteness frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldVorticityTemporalMassIntegrable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongOldVorticityTemporalMassIntegrable :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The x old-vorticity temporal spatial norm mass is integrable in elapsed
time directly from the canonical H³ tail. -/
theorem h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_integrable_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction) :
    Integrable
      (h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed
        hNS t ψ)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) tau)) := by
  apply
    integrable_restrict_Ioo_of_aestronglyMeasurable_of_nonneg_of_le
      tau
      (h3EndpointVorticityRHSWeakMassEnvelope E ψ)
      (h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_aestronglyMeasurable
        hNS ψ)

  · intro r
    unfold
      h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed
    exact
      integral_nonneg
        (fun x : Point3 =>
          norm_nonneg
            ((ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
                hNS (t + r) x)))

  · intro r hr
    let q : Set.Icc (0 : ℝ) tau :=
      ⟨r, le_of_lt hr.1, le_of_lt hr.2⟩

    exact
      h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_le_tailH3_weakStrong
        hNS ht hEnd hE hTail ψ q

/-- The y old-vorticity temporal spatial norm mass is integrable in elapsed
time directly from the canonical H³ tail. -/
theorem h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_integrable_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction) :
    Integrable
      (h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed
        hNS t ψ)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) tau)) := by
  apply
    integrable_restrict_Ioo_of_aestronglyMeasurable_of_nonneg_of_le
      tau
      (h3EndpointVorticityRHSWeakMassEnvelope E ψ)
      (h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_aestronglyMeasurable
        hNS ψ)

  · intro r
    unfold
      h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed
    exact
      integral_nonneg
        (fun x : Point3 =>
          norm_nonneg
            ((ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
                hNS (t + r) x)))

  · intro r hr
    let q : Set.Icc (0 : ℝ) tau :=
      ⟨r, le_of_lt hr.1, le_of_lt hr.2⟩

    exact
      h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_le_tailH3_weakStrong
        hNS ht hEnd hE hTail ψ q

/-- The z old-vorticity temporal spatial norm mass is integrable in elapsed
time directly from the canonical H³ tail. -/
theorem h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_integrable_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction) :
    Integrable
      (h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed
        hNS t ψ)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) tau)) := by
  apply
    integrable_restrict_Ioo_of_aestronglyMeasurable_of_nonneg_of_le
      tau
      (h3EndpointVorticityRHSWeakMassEnvelope E ψ)
      (h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_aestronglyMeasurable
        hNS ψ)

  · intro r
    unfold
      h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed
    exact
      integral_nonneg
        (fun x : Point3 =>
          norm_nonneg
            ((ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
                hNS (t + r) x)))

  · intro r hr
    let q : Set.Icc (0 : ℝ) tau :=
      ⟨r, le_of_lt hr.1, le_of_lt hr.2⟩

    exact
      h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_le_tailH3_weakStrong
        hNS ht hEnd hE hTail ψ q

/-- The complete scalar old-vorticity temporal spatial-norm-mass finiteness
frontier follows directly from the canonical H³ tail. -/
theorem H3PreterminalWeakVorticityTemporalSpatialNormMassIntegrableTo_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction) :
    H3PreterminalWeakVorticityTemporalSpatialNormMassIntegrableTo
      hNS t tau ψ := by
  exact
    ⟨
      h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_integrable_tailH3_weakStrong
        hNS ht hEnd hE hTail ψ,
      h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_integrable_tailH3_weakStrong
        hNS ht hEnd hE hTail ψ,
      h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_integrable_tailH3_weakStrong
        hNS ht hEnd hE hTail ψ
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

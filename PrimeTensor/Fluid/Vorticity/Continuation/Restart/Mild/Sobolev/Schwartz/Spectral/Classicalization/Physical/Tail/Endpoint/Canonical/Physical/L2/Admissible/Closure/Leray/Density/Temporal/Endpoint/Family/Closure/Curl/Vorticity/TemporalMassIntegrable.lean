import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.SpatialMassBound

/-!
# Time integrability of the endpoint vorticity temporal spatial masses

`SpatialMassBound` gives one uniform finite envelope for the x/y/z spatial
norm masses on every elapsed point in the closed endpoint interval.

The remaining scalar Fubini seam is purely measure theoretic:

* joint measurability of each zero-extended temporal derivative gives
  measurability of its spatial norm mass after integrating out space;
* on the finite interval `Ioo 0 tau`, a measurable real-valued function
  bounded by a constant is integrable.

This file packages both steps and closes
`H3PreterminalWeakVorticityTemporalSpatialNormMassIntegrableTo`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityTemporalMassIntegrable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityTemporalMassIntegrable :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Generic measurability of the time path of compact-test spatial norm
masses. -/
theorem h3WeakTest_continuousMapExtension_spatialNormMass_aestronglyMeasurable
    (ψ : H3WeakTestFunction)
    (F : ℝ → C(Point3, ℝ))
    (hJoint :
      Measurable
        (fun z : ℝ × Point3 =>
          F z.1 z.2))
    (t : ℝ) :
    AEStronglyMeasurable
      (fun r : ℝ =>
        ∫ x : Point3,
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (F (t + r) x)‖
          ∂volume)
      (volume : Measure ℝ) := by
  let g : ℝ × Point3 → ℝ :=
    fun z =>
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ z.2)
        (F (t + z.1) z.2)‖

  have hShift :
      Measurable
        (fun z : ℝ × Point3 =>
          (t + z.1, z.2)) := by
    exact
      (measurable_const.add measurable_fst).prodMk
        measurable_snd

  have hF :
      Measurable
        (fun z : ℝ × Point3 =>
          F (t + z.1) z.2) := by
    exact hJoint.comp hShift

  have hψ :
      Measurable
        (fun z : ℝ × Point3 =>
          ψ z.2) := by
    exact
      ψ.continuous.measurable.comp
        measurable_snd

  have hgMeas :
      Measurable g := by
    have hMul :
        Measurable
          (fun z : ℝ × Point3 =>
            (ψ z.2) * (F (t + z.1) z.2)) :=
      hψ.mul hF
    have hNorm :
        Measurable
          (fun z : ℝ × Point3 =>
            ‖(ψ z.2) * (F (t + z.1) z.2)‖) :=
      hMul.norm
    simpa only [
      g,
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul
    ] using hNorm

  exact
    hgMeas.aestronglyMeasurable.integral_prod_right'

/-- The x temporal spatial norm mass is measurable as a function of elapsed
time. -/
theorem h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_aestronglyMeasurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ψ : H3WeakTestFunction) :
    AEStronglyMeasurable
      (h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed
        hNS t ψ)
      (volume : Measure ℝ) := by
  change
    AEStronglyMeasurable
      (fun r : ℝ =>
        ∫ x : Point3,
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)‖
          ∂volume)
      (volume : Measure ℝ)

  exact
    h3WeakTest_continuousMapExtension_spatialNormMass_aestronglyMeasurable
      ψ
      (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
        hNS)
      (measurable_h3LoggedPreterminalVorticityX_temporalDerivative_joint
        hNS)
      t

/-- The y temporal spatial norm mass is measurable as a function of elapsed
time. -/
theorem h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_aestronglyMeasurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ψ : H3WeakTestFunction) :
    AEStronglyMeasurable
      (h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed
        hNS t ψ)
      (volume : Measure ℝ) := by
  change
    AEStronglyMeasurable
      (fun r : ℝ =>
        ∫ x : Point3,
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)‖
          ∂volume)
      (volume : Measure ℝ)

  exact
    h3WeakTest_continuousMapExtension_spatialNormMass_aestronglyMeasurable
      ψ
      (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
        hNS)
      (measurable_h3LoggedPreterminalVorticityY_temporalDerivative_joint
        hNS)
      t

/-- The z temporal spatial norm mass is measurable as a function of elapsed
time. -/
theorem h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_aestronglyMeasurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ψ : H3WeakTestFunction) :
    AEStronglyMeasurable
      (h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed
        hNS t ψ)
      (volume : Measure ℝ) := by
  change
    AEStronglyMeasurable
      (fun r : ℝ =>
        ∫ x : Point3,
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)‖
          ∂volume)
      (volume : Measure ℝ)

  exact
    h3WeakTest_continuousMapExtension_spatialNormMass_aestronglyMeasurable
      ψ
      (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
        hNS)
      (measurable_h3LoggedPreterminalVorticityZ_temporalDerivative_joint
        hNS)
      t

/-- A globally a.e.-strongly-measurable nonnegative real function uniformly
bounded on a finite open interval is integrable on that interval. -/
theorem integrable_restrict_Ioo_of_aestronglyMeasurable_of_nonneg_of_le
    {f : ℝ → ℝ}
    (q C : ℝ)
    (hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure ℝ))
    (hfNonneg :
      ∀ r : ℝ,
        0 ≤ f r)
    (hBound :
      ∀ r : ℝ,
        r ∈ Set.Ioo (0 : ℝ) q →
        f r ≤ C) :
    Integrable
      f
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)) := by
  change
    IntegrableOn
      f
      (Set.Ioo (0 : ℝ) q)
      (volume : Measure ℝ)

  refine
    IntegrableOn.of_bound
      ?_
      hfMeas.restrict
      C
      ?_

  · rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top

  · filter_upwards
      [ae_restrict_mem measurableSet_Ioo]
      with r hr

    rw [
      Real.norm_eq_abs,
      abs_of_nonneg (hfNonneg r)
    ]

    exact hBound r hr

/-- The x temporal spatial norm mass is integrable in elapsed time on the
endpoint interval. -/
theorem h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_integrable_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
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
      h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_le_endpointH3
        hNS ht hEnd hE hTail hEndpoint ψ q

/-- The y temporal spatial norm mass is integrable in elapsed time on the
endpoint interval. -/
theorem h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_integrable_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
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
      h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_le_endpointH3
        hNS ht hEnd hE hTail hEndpoint ψ q

/-- The z temporal spatial norm mass is integrable in elapsed time on the
endpoint interval. -/
theorem h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_integrable_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
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
      h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_le_endpointH3
        hNS ht hEnd hE hTail hEndpoint ψ q

/-- The complete scalar spatial-norm-mass finiteness frontier is closed by the
uniform endpoint H³ bound. -/
theorem H3PreterminalWeakVorticityTemporalSpatialNormMassIntegrableTo_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (ψ : H3WeakTestFunction) :
    H3PreterminalWeakVorticityTemporalSpatialNormMassIntegrableTo
      hNS t tau ψ := by
  exact
    ⟨
      h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_integrable_endpointH3
        hNS ht hEnd hE hTail hEndpoint ψ,
      h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_integrable_endpointH3
        hNS ht hEnd hE hTail hEndpoint ψ,
      h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_integrable_endpointH3
        hNS ht hEnd hE hTail hEndpoint ψ
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor

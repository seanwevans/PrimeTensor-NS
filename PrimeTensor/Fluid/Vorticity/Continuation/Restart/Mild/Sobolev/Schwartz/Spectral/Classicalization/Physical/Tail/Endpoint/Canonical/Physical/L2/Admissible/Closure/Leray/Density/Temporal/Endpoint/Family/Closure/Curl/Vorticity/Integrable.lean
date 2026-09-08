import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.JointMeasurable
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Product integrability reduction for compactly tested vorticity derivatives

`JointMeasurable` closed the product-space measurability issue for the actual
preterminal vorticity temporal derivatives without asserting joint continuity.

The remaining Fubini input is finiteness.  This file isolates it in the
smallest scalar form.

For any continuous spatial family `F : ℝ → C(Point3, ℝ)` and any compact weak
test `ψ`, every fixed-time spatial slice

    x ↦ ψ(x) F(t+r)(x)

is integrable, simply because `ψ` has compact support and `F(t+r)` is
continuous.

Therefore, once the spacetime integrand is measurable, Mathlib's
`integrable_prod_iff` reduces product integrability to exactly one scalar
condition:

    r ↦ ∫ x, ‖ψ(x) F(t+r)(x)‖ dx

is integrable in time.

We instantiate this reduction for the zero-extended x-, y-, and z-vorticity
temporal derivatives.  The next analytic obligation is consequently only a
time-integrable bound for these three spatial norm masses.  That is the place
where the uniform H³ tail estimate belongs.

No pointwise temporal bound and no joint spacetime continuity is assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityIntegrable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityIntegrable :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A compact weak test multiplied by any continuous spatial slice is
integrable. -/
theorem h3WeakTest_mul_continuousMap_integrable
    (ψ : H3WeakTestFunction)
    (F : C(Point3, ℝ)) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (F x))
      (volume : Measure Point3) := by
  exact
    ψ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (F.continuous.locallyIntegrable.locallyIntegrableOn Set.univ)

/-- Generic Carathéodory-to-Fubini reduction.

If `F s` is a continuous spatial function for every `s`, the scalar evaluation
`(s,x) ↦ F s x` is jointly measurable, and the time path of spatial `L¹`
norms of `ψ(x) F(t+s)(x)` is integrable, then the compactly tested field is
integrable on the product measure. -/
theorem h3WeakTest_continuousMapExtension_productIntegrable_of_spatialNormMassIntegrable
    (ψ : H3WeakTestFunction)
    (F : ℝ → C(Point3, ℝ))
    (hJoint :
      Measurable
        (fun z : ℝ × Point3 =>
          F z.1 z.2))
    (t q : ℝ)
    (hMass :
      Integrable
        (fun r : ℝ =>
          ∫ x : Point3,
            ‖(ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (F (t + r) x)‖
            ∂volume)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))) :
    Integrable
      (fun z : ℝ × Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ z.2)
          (F (t + z.1) z.2))
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
        (volume : Measure Point3)) := by
  let μ : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)

  let f : ℝ × Point3 → ℝ :=
    fun z =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ z.2)
        (F (t + z.1) z.2)

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

  have hfMeas :
      Measurable f := by
    dsimp only [f]
    change
      Measurable
        (fun z : ℝ × Point3 =>
          (ψ z.2) * (F (t + z.1) z.2))
    exact hψ.mul hF

  have hfAE :
      AEStronglyMeasurable
        f
        (μ.prod (volume : Measure Point3)) :=
    hfMeas.aestronglyMeasurable

  rw [integrable_prod_iff hfAE]

  constructor
  · exact
      Filter.Eventually.of_forall
        (fun r =>
          h3WeakTest_mul_continuousMap_integrable
            ψ (F (t + r)))
  · dsimp only [μ, f]
    exact hMass

/-- Spatial `L¹` norm mass of the compactly tested x-vorticity temporal
derivative at elapsed time `r`. -/
noncomputable def h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t : ℝ)
    (ψ : H3WeakTestFunction)
    (r : ℝ) : ℝ :=
  ∫ x : Point3,
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
        hNS (t + r) x)‖
    ∂volume

/-- Spatial `L¹` norm mass of the compactly tested y-vorticity temporal
derivative at elapsed time `r`. -/
noncomputable def h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t : ℝ)
    (ψ : H3WeakTestFunction)
    (r : ℝ) : ℝ :=
  ∫ x : Point3,
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
        hNS (t + r) x)‖
    ∂volume

/-- Spatial `L¹` norm mass of the compactly tested z-vorticity temporal
derivative at elapsed time `r`. -/
noncomputable def h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t : ℝ)
    (ψ : H3WeakTestFunction)
    (r : ℝ) : ℝ :=
  ∫ x : Point3,
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
        hNS (t + r) x)‖
    ∂volume

/-- Exact remaining scalar finiteness frontier for all three vorticity
components at one shortened elapsed target `q`. -/
def H3PreterminalWeakVorticityTemporalSpatialNormMassIntegrableTo
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t q : ℝ)
    (ψ : H3WeakTestFunction) : Prop :=
  Integrable
      (h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed
        hNS t ψ)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))
    ∧
  Integrable
      (h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed
        hNS t ψ)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))
    ∧
  Integrable
      (h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed
        hNS t ψ)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))

/-- Product-space integrability conclusion for all three compactly tested
vorticity temporal derivatives. -/
def H3PreterminalWeakVorticityTemporalProductIntegrableTo
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t q : ℝ)
    (ψ : H3WeakTestFunction) : Prop :=
  Integrable
      (fun z : ℝ × Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ z.2)
          (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
            hNS (t + z.1) z.2))
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
        (volume : Measure Point3))
    ∧
  Integrable
      (fun z : ℝ × Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ z.2)
          (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
            hNS (t + z.1) z.2))
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
        (volume : Measure Point3))
    ∧
  Integrable
      (fun z : ℝ × Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ z.2)
          (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
            hNS (t + z.1) z.2))
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
        (volume : Measure Point3))

/-- Joint measurability plus the three scalar spatial-norm mass conditions
discharge the complete product-space Fubini integrability requirement. -/
theorem H3PreterminalWeakVorticityTemporalProductIntegrableTo_of_spatialNormMassIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t q : ℝ)
    (ψ : H3WeakTestFunction)
    (hMass :
      H3PreterminalWeakVorticityTemporalSpatialNormMassIntegrableTo
        hNS t q ψ) :
    H3PreterminalWeakVorticityTemporalProductIntegrableTo
      hNS t q ψ := by
  rcases hMass with ⟨hX, hY, hZ⟩

  constructor
  · exact
      h3WeakTest_continuousMapExtension_productIntegrable_of_spatialNormMassIntegrable
        ψ
        (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
          hNS)
        (measurable_h3LoggedPreterminalVorticityX_temporalDerivative_joint
          hNS)
        t q
        (by
          change
            Integrable
              (h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed
                hNS t ψ)
              ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))
          exact hX)
  constructor
  · exact
      h3WeakTest_continuousMapExtension_productIntegrable_of_spatialNormMassIntegrable
        ψ
        (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
          hNS)
        (measurable_h3LoggedPreterminalVorticityY_temporalDerivative_joint
          hNS)
        t q
        (by
          change
            Integrable
              (h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed
                hNS t ψ)
              ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))
          exact hY)
  · exact
      h3WeakTest_continuousMapExtension_productIntegrable_of_spatialNormMassIntegrable
        ψ
        (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
          hNS)
        (measurable_h3LoggedPreterminalVorticityZ_temporalDerivative_joint
          hNS)
        t q
        (by
          change
            Integrable
              (h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed
                hNS t ψ)
              ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))
          exact hZ)

end

end Euclidean
end Bridge
end PrimeTensor

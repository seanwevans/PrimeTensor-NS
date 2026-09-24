import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Selected.Reconstruction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Initial.Decoder

/-!
# BKM endpoint: selected bound for the actual logged velocity gradient

The complete selected BKM gradient model has now been reconstructed almost
everywhere as the real spatial derivative of the canonical H³ representative.

This file performs the two representative upgrades needed by the public
continuation interface.

First, on a strict preterminal slice, the canonical real `C¹` representative
of a genuine encoded H³ component agrees pointwise with the original logged
velocity component.  The existing decoder gives equality almost everywhere,
and both sides are continuous.

Second, the selected model gives an almost-everywhere bound for the spatial
derivative of the H³ representative.  That derivative is continuous.  Since
the right-hand side of the estimate is independent of space, the bound upgrades
from almost everywhere to every spatial point by applying
`Measure.eq_of_ae_eq` to

    x ↦ max ‖∂ᵢuⱼ(x)‖ C

and the constant function `C`.

The final theorem is therefore a pointwise estimate for the actual
`loggedVelocityComponent` derivative, with the exact selected low/middle/high
right-hand side.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeBKMEndpointSelectedActualGradientBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointSelectedActualGradientBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Continuity of first coordinate derivatives -/

/-- A coordinate derivative of a spatially `C¹` scalar field is continuous. -/
private theorem spatialC1_spatial_d_continuous_selectedActualGradientBound
    {f : ScalarField3}
    (hf : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three) :
    Continuous (spatial3.d i f) := by

  have hfun :
      (fun x : Point3 => partialDeriv i f x)
        =
      (fun x : Point3 =>
        (fderiv ℝ f x) (axisDirection i)) := by
    funext x
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.partialDeriv_eq_fderiv_axisDirection
        hf x i

  change Continuous (fun x : Point3 => partialDeriv i f x)
  rw [hfun]

  have hfd : ContDiff ℝ 0 (fderiv ℝ f) := by
    unfold SpatialC1 at hf
    exact hf.fderiv_right (by norm_num)

  exact
    (hfd.clm_apply contDiff_const).continuous

/-! ## Pointwise identification with the old logged velocity -/

/--
On a strict preterminal slice, the canonical real `C¹` representative of one
encoded H³ velocity component is pointwise the original logged velocity
component.
-/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_velocityH3SpectralScalarAt_eq_loggedVelocityComponent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    h3SpectralScalarRealC1RepresentativeOnPoint3
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)
      =
    loggedVelocityComponent
      u t (h3AxisOfFin3 j) := by

  have hAE0 :=
    h3SpectralVelocityRealC1RepresentativeOnPoint3_velocityH3SpectralStateAt_ae_eq_loggedVelocityComponent
      hFourier j

  have hAE :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u t (h3AxisOfFin3 j) := by
    simpa only [
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      velocityH3SpectralStateAt
    ] using hAE0

  have hSpectralContinuous :
      Continuous
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)) :=
    (h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
      (velocityH3SpectralScalarAt
        u t hInt hMeas hFourier j)).continuous

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  have hOldContinuous :
      Continuous
        (loggedVelocityComponent
          u t (h3AxisOfFin3 j)) := by
    unfold loggedVelocityComponent
    exact
      (hPDE.regularity.velocity_spatial_three
        t ht (h3AxisOfFin3 j)).continuous

  exact
    MeasureTheory.Measure.eq_of_ae_eq
      hAE
      hSpectralContinuous
      hOldContinuous

/-! ## Everywhere selected bound for the H³ representative -/

/--
The selected low/middle/high estimate holds at every spatial point for the
intrinsic derivative of the canonical real H³ representative.
-/
theorem norm_spatialDerivative_h3SpectralScalarRealC1RepresentativeOnPoint3_le_selectedBKM
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {g : ℝ → ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (j i : Fin 3)
    (hComponent :
      ‖velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j‖
        ≤ A)
    (x : Point3) :
    ‖spatial3.d
        (h3AxisOfFin3 i)
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j))
        x‖
      ≤
    h3BKMLowGradientUnitL2Constant
        *
      ‖velocityH3L2JetAt
          u t hInt hMeas
          (h3JetSlot0 j)‖
      +
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant)
      +
    (2 * Real.pi)
      * h3BKMQuarterTailMomentConstant := by

  let G : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier j

  let C : ℝ :=
    h3BKMLowGradientUnitL2Constant
        *
      ‖velocityH3L2JetAt
          u t hInt hMeas
          (h3JetSlot0 j)‖
      +
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant)
      +
    (2 * Real.pi)
      * h3BKMQuarterTailMomentConstant

  have hRecon :=
    spatialDerivative_h3SpectralScalarRealC1RepresentativeOnPoint3_ae_eq_selectedGradientModel_re
      hNS ht hFourier hEnvelope A j i

  have hAE :
      ∀ᵐ y ∂(volume : Measure Point3),
        ‖spatial3.d
            (h3AxisOfFin3 i)
            (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
            y‖
          ≤
        C := by

    filter_upwards [hRecon] with y hy

    have hRe :
        ‖(h3BKMSelectedGradientModel
            hFourier A j i y).re‖
          ≤
        ‖h3BKMSelectedGradientModel
            hFourier A j i y‖ := by
      simpa [Real.norm_eq_abs] using
        Complex.abs_re_le_norm
          (h3BKMSelectedGradientModel
            hFourier A j i y)

    have hModel :
        ‖h3BKMSelectedGradientModel
            hFourier A j i y‖
          ≤
        C := by
      dsimp only [C]
      exact
        norm_h3BKMSelectedGradientModel_le
          hInt hMeas hFourier hEnvelope
          A j i y hComponent

    dsimp only [G]

    rw [hy]

    exact hRe.trans hModel

  have hC1 :
      SpatialC1
        (h3SpectralScalarRealC1RepresentativeOnPoint3 G) :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one G

  have hDerivativeContinuous :
      Continuous
        (spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 G)) :=
    spatialC1_spatial_d_continuous_selectedActualGradientBound
      hC1
      (h3AxisOfFin3 i)

  have hNormContinuous :
      Continuous
        (fun y : Point3 =>
          ‖spatial3.d
              (h3AxisOfFin3 i)
              (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
              y‖) :=
    hDerivativeContinuous.norm

  have hMaxAE :
      (fun y : Point3 =>
        max
          ‖spatial3.d
              (h3AxisOfFin3 i)
              (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
              y‖
          C)
        =ᵐ[(volume : Measure Point3)]
      (fun _ : Point3 => C) := by

    filter_upwards [hAE] with y hy
    exact max_eq_right hy

  have hMaxContinuous :
      Continuous
        (fun y : Point3 =>
          max
            ‖spatial3.d
                (h3AxisOfFin3 i)
                (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
                y‖
            C) :=
    hNormContinuous.max continuous_const

  have hMaxEq :
      (fun y : Point3 =>
        max
          ‖spatial3.d
              (h3AxisOfFin3 i)
              (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
              y‖
          C)
        =
      (fun _ : Point3 => C) :=
    MeasureTheory.Measure.eq_of_ae_eq
      hMaxAE
      hMaxContinuous
      continuous_const

  have hxMax :
      max
        ‖spatial3.d
            (h3AxisOfFin3 i)
            (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
            x‖
        C
        =
      C :=
    congrFun hMaxEq x

  have hx :
      ‖spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
          x‖
        ≤
      C := by
    calc
      ‖spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
          x‖
          ≤
        max
          ‖spatial3.d
              (h3AxisOfFin3 i)
              (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
              x‖
          C :=
        le_max_left _ _

      _ = C := hxMax

  simpa only [G, C] using hx

/-! ## Actual logged velocity gradient -/

/--
The selected BKM estimate holds pointwise for the actual logged velocity
gradient on every strict preterminal slice.
-/
theorem norm_loggedVelocityComponent_spatial_d_le_selectedBKM
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {g : ℝ → ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (j i : Fin 3)
    (hComponent :
      ‖velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j‖
        ≤ A)
    (x : Point3) :
    ‖spatial3.d
        (h3AxisOfFin3 i)
        (loggedVelocityComponent
          u t (h3AxisOfFin3 j))
        x‖
      ≤
    h3BKMLowGradientUnitL2Constant
        *
      ‖velocityH3L2JetAt
          u t hInt hMeas
          (h3JetSlot0 j)‖
      +
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant)
      +
    (2 * Real.pi)
      * h3BKMQuarterTailMomentConstant := by

  have hPointwise :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_velocityH3SpectralScalarAt_eq_loggedVelocityComponent
      hNS ht hFourier j

  have hBound :=
    norm_spatialDerivative_h3SpectralScalarRealC1RepresentativeOnPoint3_le_selectedBKM
      hNS ht hFourier hEnvelope
      A j i hComponent x

  have hDerivativeEq :
      spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (velocityH3SpectralScalarAt
              u t hInt hMeas hFourier j))
          x
        =
      spatial3.d
          (h3AxisOfFin3 i)
          (loggedVelocityComponent
            u t (h3AxisOfFin3 j))
          x :=
    congrArg
      (fun f : Point3 → ℝ =>
        spatial3.d
          (h3AxisOfFin3 i)
          f
          x)
      hPointwise

  rw [← hDerivativeEq]

  exact hBound

end

end Euclidean
end Bridge
end PrimeTensor

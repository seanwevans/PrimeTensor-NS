import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Vorticity.Curl.Localized.Reconstruction
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Kernel.Physical
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Young.Convolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Transport

/-!
# BKM endpoint: package physical vorticity convolutions in L²

The localized spectral side is now packaged as a genuine Fourier `L²` inverse
transform.  To meet it from the physical side, place both factors of the
dyadic convolution on the same Euclidean carrier

    H3FourierPoint3 = WithLp 2 Point3.

For each dyadic BKM coordinate kernel:

* its Schwartz inverse-Fourier representative is integrable, hence defines a
  canonical complex `L¹` class;
* each physical vorticity component is already a real physical `L²` class;
* carrier transport plus complexification gives the corresponding Euclidean
  complex `L²` class;
* that transported class is represented almost everywhere by the literal
  complexified physical vorticity evaluated through `WithLp.ofLp`.

We therefore obtain canonical endpoint Young states

    Kᵢₖ,R * ωₓ,
    Kᵢₖ,R * ωᵧ,
    Kᵢₖ,R * ω_z

in Euclidean `L²`.

These are the bundled physical convolution objects that the next checkpoint
will compare with the localized inverse-Fourier multiplier products.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointPhysicalVorticityConvolutionL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointPhysicalVorticityConvolutionL2 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- One dyadic BKM kernel, bundled as a Fourier-carrier complex `L¹` state. -/
noncomputable def h3BKMDyadicKernelL1
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL1 :=
  (
    MeasureTheory.memLp_one_iff_integrable.mpr
      (h3BKMDyadicKernel_integrable hR i k)
  ).toLp
    (h3BKMDyadicKernel R hR i k)

/-- The `L¹` package has the expected dyadic-kernel representative a.e. -/
theorem h3BKMDyadicKernelL1_ae
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (h3BKMDyadicKernelL1 R hR i k :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMDyadicKernel R hR i k := by

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (
        MeasureTheory.memLp_one_iff_integrable.mpr
          (h3BKMDyadicKernel_integrable hR i k)
      )

/--
The Euclidean complex `L²` transport of physical x-vorticity has the literal
complexified x-vorticity as representative almost everywhere.
-/
theorem h3BKMPhysicalVorticityXEuclideanComplex_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityXL2
          u t hInt hMeas) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      h3BKMPhysicalVorticityX
        u t
        ((WithLp.ofLp :
          H3FourierPoint3 → Point3) ξ) := by

  have hCarrier :=
    h3PhysicalScalarL2EuclideanComplex_coeFn_ae
      (h3BKMPhysicalVorticityXL2
        u t hInt hMeas)

  have hPhysical :=
    h3BKMPhysicalVorticityXL2_ae_eq
      hInt hMeas

  have hPull :=
    (
      PiLp.volume_preserving_ofLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      hPhysical

  filter_upwards [hCarrier, hPull] with ξ hCarrierξ hPullξ

  rw [hCarrierξ]

  simp only [Function.comp_apply] at hPullξ

  rw [hPullξ]

  rfl

/--
The Euclidean complex `L²` transport of physical y-vorticity has the literal
complexified y-vorticity as representative almost everywhere.
-/
theorem h3BKMPhysicalVorticityYEuclideanComplex_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityYL2
          u t hInt hMeas) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      h3BKMPhysicalVorticityY
        u t
        ((WithLp.ofLp :
          H3FourierPoint3 → Point3) ξ) := by

  have hCarrier :=
    h3PhysicalScalarL2EuclideanComplex_coeFn_ae
      (h3BKMPhysicalVorticityYL2
        u t hInt hMeas)

  have hPhysical :=
    h3BKMPhysicalVorticityYL2_ae_eq
      hInt hMeas

  have hPull :=
    (
      PiLp.volume_preserving_ofLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      hPhysical

  filter_upwards [hCarrier, hPull] with ξ hCarrierξ hPullξ

  rw [hCarrierξ]

  simp only [Function.comp_apply] at hPullξ

  rw [hPullξ]

  rfl

/--
The Euclidean complex `L²` transport of physical z-vorticity has the literal
complexified z-vorticity as representative almost everywhere.
-/
theorem h3BKMPhysicalVorticityZEuclideanComplex_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityZL2
          u t hInt hMeas) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      h3BKMPhysicalVorticityZ
        u t
        ((WithLp.ofLp :
          H3FourierPoint3 → Point3) ξ) := by

  have hCarrier :=
    h3PhysicalScalarL2EuclideanComplex_coeFn_ae
      (h3BKMPhysicalVorticityZL2
        u t hInt hMeas)

  have hPhysical :=
    h3BKMPhysicalVorticityZL2_ae_eq
      hInt hMeas

  have hPull :=
    (
      PiLp.volume_preserving_ofLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      hPhysical

  filter_upwards [hCarrier, hPull] with ξ hCarrierξ hPullξ

  rw [hCarrierξ]

  simp only [Function.comp_apply] at hPullξ

  rw [hPullξ]

  rfl

/-- Bundled Euclidean `L²` convolution of one dyadic kernel with x-vorticity. -/
noncomputable def h3BKMDyadicVorticityXConvolutionL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL2 :=
  h3L1L2Convolution
    (h3BKMDyadicKernelL1 R hR i k)
    (h3PhysicalScalarL2EuclideanComplex
      (h3BKMPhysicalVorticityXL2
        u t hInt hMeas))

/-- Bundled Euclidean `L²` convolution of one dyadic kernel with y-vorticity. -/
noncomputable def h3BKMDyadicVorticityYConvolutionL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL2 :=
  h3L1L2Convolution
    (h3BKMDyadicKernelL1 R hR i k)
    (h3PhysicalScalarL2EuclideanComplex
      (h3BKMPhysicalVorticityYL2
        u t hInt hMeas))

/-- Bundled Euclidean `L²` convolution of one dyadic kernel with z-vorticity. -/
noncomputable def h3BKMDyadicVorticityZConvolutionL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL2 :=
  h3L1L2Convolution
    (h3BKMDyadicKernelL1 R hR i k)
    (h3PhysicalScalarL2EuclideanComplex
      (h3BKMPhysicalVorticityZL2
        u t hInt hMeas))

/-- Endpoint Young bound for the x-vorticity dyadic convolution state. -/
theorem norm_h3BKMDyadicVorticityXConvolutionL2_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    ‖h3BKMDyadicVorticityXConvolutionL2
        hInt hMeas R hR i k‖
      ≤
    ‖h3BKMDyadicKernelL1 R hR i k‖
      *
    ‖h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityXL2
          u t hInt hMeas)‖ := by

  exact
    norm_h3L1L2Convolution_le
      (h3BKMDyadicKernelL1 R hR i k)
      (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityXL2
          u t hInt hMeas))

/-- Endpoint Young bound for the y-vorticity dyadic convolution state. -/
theorem norm_h3BKMDyadicVorticityYConvolutionL2_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    ‖h3BKMDyadicVorticityYConvolutionL2
        hInt hMeas R hR i k‖
      ≤
    ‖h3BKMDyadicKernelL1 R hR i k‖
      *
    ‖h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityYL2
          u t hInt hMeas)‖ := by

  exact
    norm_h3L1L2Convolution_le
      (h3BKMDyadicKernelL1 R hR i k)
      (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityYL2
          u t hInt hMeas))

/-- Endpoint Young bound for the z-vorticity dyadic convolution state. -/
theorem norm_h3BKMDyadicVorticityZConvolutionL2_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    ‖h3BKMDyadicVorticityZConvolutionL2
        hInt hMeas R hR i k‖
      ≤
    ‖h3BKMDyadicKernelL1 R hR i k‖
      *
    ‖h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityZL2
          u t hInt hMeas)‖ := by

  exact
    norm_h3L1L2Convolution_le
      (h3BKMDyadicKernelL1 R hR i k)
      (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityZL2
          u t hInt hMeas))

end

end Euclidean
end Bridge
end PrimeTensor

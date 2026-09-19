import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicVorticityConvolutionRepresentative

/-!
# BKM endpoint: transport dyadic vorticity convolution representatives to physical space

`DyadicVorticityConvolutionRepresentative` identifies each bundled endpoint
Young state with its literal scalar convolution on the Euclidean carrier

    H3FourierPoint3 = WithLp 2 Point3.

The physical BKM estimates, however, are already written directly on
`Point3` using

    h3BKMPhysicalConvolution
      (h3BKMDyadicPhysicalKernel ...)
      (h3BKMPhysicalVorticityX/Y/Z ...).

The map

    WithLp.toLp 2 : Point3 → H3FourierPoint3

is volume preserving.  Pulling the Euclidean scalar convolution back through
this map therefore gives exactly the physical convolution.  We record that
identity pointwise for the three raw convolutions and then transport the
a.e. representatives of the bundled `L²` states.

After this file, the physical `L∞` bounds from `DyadicKernelBound` can be
applied directly to representatives of the exact localized inverse-Fourier
states obtained in `DyadicVorticityConvolutionReconstruction`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicVorticityConvolutionPhysical
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointDyadicVorticityConvolutionPhysical :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Exact carrier transport of the raw convolutions -/

/--
Pulling the raw Euclidean x-vorticity convolution back along `WithLp.toLp`
gives exactly the physical dyadic convolution.
-/
theorem h3BKMDyadicVorticityXConvolutionRaw_toLp_eq_physical
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (x : Point3) :
    h3BKMDyadicVorticityXConvolutionRaw
        u t R hR i k
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)
      =
    h3BKMPhysicalConvolution
      (h3BKMDyadicPhysicalKernel R hR i k)
      (h3BKMPhysicalVorticityX u t)
      x := by

  have hIntegral :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).integral_comp
      (MeasurableEquiv.toLp
        2
        Point3).measurableEmbedding
      (fun η : H3FourierPoint3 =>
        h3BKMDyadicKernel R hR i k η
          *
        h3BKMPhysicalVorticityX
          u t
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3)
            (((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x) - η)))

  unfold
    h3BKMDyadicVorticityXConvolutionRaw
    h3BKMPhysicalConvolution
    h3BKMDyadicPhysicalKernel

  simpa only [
    Function.comp_apply,
    WithLp.ofLp_sub,
    WithLp.ofLp_toLp
  ] using hIntegral.symm

/--
Pulling the raw Euclidean y-vorticity convolution back along `WithLp.toLp`
gives exactly the physical dyadic convolution.
-/
theorem h3BKMDyadicVorticityYConvolutionRaw_toLp_eq_physical
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (x : Point3) :
    h3BKMDyadicVorticityYConvolutionRaw
        u t R hR i k
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)
      =
    h3BKMPhysicalConvolution
      (h3BKMDyadicPhysicalKernel R hR i k)
      (h3BKMPhysicalVorticityY u t)
      x := by

  have hIntegral :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).integral_comp
      (MeasurableEquiv.toLp
        2
        Point3).measurableEmbedding
      (fun η : H3FourierPoint3 =>
        h3BKMDyadicKernel R hR i k η
          *
        h3BKMPhysicalVorticityY
          u t
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3)
            (((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x) - η)))

  unfold
    h3BKMDyadicVorticityYConvolutionRaw
    h3BKMPhysicalConvolution
    h3BKMDyadicPhysicalKernel

  simpa only [
    Function.comp_apply,
    WithLp.ofLp_sub,
    WithLp.ofLp_toLp
  ] using hIntegral.symm

/--
Pulling the raw Euclidean z-vorticity convolution back along `WithLp.toLp`
gives exactly the physical dyadic convolution.
-/
theorem h3BKMDyadicVorticityZConvolutionRaw_toLp_eq_physical
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (x : Point3) :
    h3BKMDyadicVorticityZConvolutionRaw
        u t R hR i k
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)
      =
    h3BKMPhysicalConvolution
      (h3BKMDyadicPhysicalKernel R hR i k)
      (h3BKMPhysicalVorticityZ u t)
      x := by

  have hIntegral :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).integral_comp
      (MeasurableEquiv.toLp
        2
        Point3).measurableEmbedding
      (fun η : H3FourierPoint3 =>
        h3BKMDyadicKernel R hR i k η
          *
        h3BKMPhysicalVorticityZ
          u t
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3)
            (((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x) - η)))

  unfold
    h3BKMDyadicVorticityZConvolutionRaw
    h3BKMPhysicalConvolution
    h3BKMDyadicPhysicalKernel

  simpa only [
    Function.comp_apply,
    WithLp.ofLp_sub,
    WithLp.ofLp_toLp
  ] using hIntegral.symm

/-! ## Physical a.e. representatives of the bundled convolution states -/

/--
The bundled x-vorticity dyadic convolution, pulled back to `Point3`, is
represented a.e. by the literal physical convolution.
-/
theorem h3BKMDyadicVorticityXConvolutionL2_toLp_ae_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (fun x : Point3 =>
      (h3BKMDyadicVorticityXConvolutionL2
          hInt hMeas R hR i k :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        (h3BKMPhysicalVorticityX u t)
        x) := by

  have hPull :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (h3BKMDyadicVorticityXConvolutionL2_ae_eq_raw
        hInt hMeas hEnvelope hR i k)

  filter_upwards [hPull] with x hx

  simp only [Function.comp_apply] at hx

  rw [hx]

  exact
    h3BKMDyadicVorticityXConvolutionRaw_toLp_eq_physical
      u t hR i k x

/--
The bundled y-vorticity dyadic convolution, pulled back to `Point3`, is
represented a.e. by the literal physical convolution.
-/
theorem h3BKMDyadicVorticityYConvolutionL2_toLp_ae_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (fun x : Point3 =>
      (h3BKMDyadicVorticityYConvolutionL2
          hInt hMeas R hR i k :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        (h3BKMPhysicalVorticityY u t)
        x) := by

  have hPull :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (h3BKMDyadicVorticityYConvolutionL2_ae_eq_raw
        hInt hMeas hEnvelope hR i k)

  filter_upwards [hPull] with x hx

  simp only [Function.comp_apply] at hx

  rw [hx]

  exact
    h3BKMDyadicVorticityYConvolutionRaw_toLp_eq_physical
      u t hR i k x

/--
The bundled z-vorticity dyadic convolution, pulled back to `Point3`, is
represented a.e. by the literal physical convolution.
-/
theorem h3BKMDyadicVorticityZConvolutionL2_toLp_ae_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (fun x : Point3 =>
      (h3BKMDyadicVorticityZConvolutionL2
          hInt hMeas R hR i k :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        (h3BKMPhysicalVorticityZ u t)
        x) := by

  have hPull :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (h3BKMDyadicVorticityZConvolutionL2_ae_eq_raw
        hInt hMeas hEnvelope hR i k)

  filter_upwards [hPull] with x hx

  simp only [Function.comp_apply] at hx

  rw [hx]

  exact
    h3BKMDyadicVorticityZConvolutionRaw_toLp_eq_physical
      u t hR i k x

end

end Euclidean
end Bridge
end PrimeTensor

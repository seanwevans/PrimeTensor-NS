import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicKernel

/-!
# BKM endpoint: transport the dyadic kernel to physical space

The inverse-Fourier dyadic BKM kernel is naturally constructed on

    H3FourierPoint3 = WithLp 2 Point3.

The physical convolution estimate, however, is stated directly on `Point3`.
The canonical map

    WithLp.toLp 2 : Point3 → H3FourierPoint3

is volume preserving.  We therefore pull the Euclidean kernel back through
that map.

This checkpoint proves:

* the transported kernel is integrable on physical `Point3`;
* its physical `L¹` mass is exactly the Euclidean kernel mass already named in
  `DyadicKernel`;
* the generic physical convolution estimate can therefore be stated directly
  in terms of `h3BKMDyadicKernelL1Mass`.

No scaling estimate is used here.  The next checkpoint can prove that this mass
is independent of the dyadic radius.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicKernelPhysical
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointDyadicKernelPhysical :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The dyadic inverse-Fourier kernel pulled back to the physical product carrier.
-/
noncomputable def h3BKMDyadicPhysicalKernel
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3)
    (x : Point3) : ℂ :=
  h3BKMDyadicKernel
    R hR i k
    ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

@[simp]
theorem h3BKMDyadicPhysicalKernel_apply
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (x : Point3) :
    h3BKMDyadicPhysicalKernel R hR i k x
      =
    h3BKMDyadicKernel
      R hR i k
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x) := by
  rfl

/-- Pullback through `WithLp.toLp` preserves integrability. -/
theorem h3BKMDyadicPhysicalKernel_integrable
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    Integrable
      (h3BKMDyadicPhysicalKernel R hR i k)
      (volume : Measure Point3) := by

  change
    Integrable
      (
        h3BKMDyadicKernel R hR i k
          ∘
        (WithLp.toLp 2 :
          Point3 → H3FourierPoint3)
      )
      (volume : Measure Point3)

  exact
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).integrable_comp_of_integrable
      (h3BKMDyadicKernel_integrable hR i k)

/-- The norm of the physical kernel is integrable as well. -/
theorem integrable_norm_h3BKMDyadicPhysicalKernel
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    Integrable
      (fun x : Point3 =>
        ‖h3BKMDyadicPhysicalKernel R hR i k x‖)
      (volume : Measure Point3) := by

  exact
    (h3BKMDyadicPhysicalKernel_integrable
      hR i k).norm

/--
The physical and Euclidean `L¹` masses are exactly equal because
`WithLp.toLp` preserves volume.
-/
theorem h3BKMDyadicPhysicalKernel_L1Mass_eq
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (∫ x : Point3,
        ‖h3BKMDyadicPhysicalKernel R hR i k x‖
        ∂(volume : Measure Point3))
      =
    h3BKMDyadicKernelL1Mass R hR i k := by

  have hIntegral :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).integral_comp
      (MeasurableEquiv.toLp
        2
        Point3).measurableEmbedding
      (fun ξ : H3FourierPoint3 =>
        ‖h3BKMDyadicKernel R hR i k ξ‖)

  unfold
    h3BKMDyadicPhysicalKernel
    h3BKMDyadicKernelL1Mass

  simpa only [Function.comp_apply] using hIntegral

/--
The generic physical convolution estimate specialized to the actual dyadic BKM
kernel and expressed using its named Euclidean `L¹` mass.
-/
theorem norm_h3BKMPhysicalConvolution_dyadic_le
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (f : Point3 → ℂ)
    (M : ℝ)
    (hf : ∀ z : Point3, ‖f z‖ ≤ M)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        f
        x‖
      ≤
    M * h3BKMDyadicKernelL1Mass R hR i k := by

  have h :=
    norm_h3BKMPhysicalConvolution_le
      (h3BKMDyadicPhysicalKernel R hR i k)
      f
      M
      (h3BKMDyadicPhysicalKernel_integrable hR i k)
      hf
      x

  rw [
    h3BKMDyadicPhysicalKernel_L1Mass_eq
      hR i k
  ] at h

  exact h

end

end Euclidean
end Bridge
end PrimeTensor

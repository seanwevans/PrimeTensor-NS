import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Kernel.Scaling

/-!
# BKM endpoint: scale-uniform dyadic physical convolution bounds

The dyadic inverse-Fourier kernel has exact scale-independent `L¹` mass:

    ‖Kᵢₖ,R‖₁ = ‖Kᵢₖ,1‖₁.

This file feeds that identity into the physical convolution estimate.  Every
positive-radius dyadic BKM kernel therefore acts on a bounded scalar field with
the same unit-scale operator constant.

The result is the per-shell estimate needed before the middle-frequency
argument counts how many dyadic shells occur between the low- and high-
frequency cutoffs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicKernelBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointDyadicKernelBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
A single dyadic physical BKM convolution is controlled by the unit-scale
kernel mass, uniformly in every positive radius.
-/
theorem norm_h3BKMPhysicalConvolution_dyadic_le_unit
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
    M *
      h3BKMDyadicKernelL1Mass
        (1 : ℝ) zero_lt_one i k := by

  have h :=
    norm_h3BKMPhysicalConvolution_dyadic_le
      hR i k f M hf x

  rw [
    h3BKMDyadicKernelL1Mass_eq_unit
      hR i k
  ] at h

  exact h

/--
Two dyadic physical convolutions at the same positive radius are controlled by
the sum of their unit-scale kernel masses.
-/
theorem norm_h3BKMPhysicalConvolution_dyadic_add_le_unit
    {R : ℝ}
    (hR : 0 < R)
    (i₁ k₁ i₂ k₂ : Fin 3)
    (f₁ f₂ : Point3 → ℂ)
    (M : ℝ)
    (hf₁ : ∀ z : Point3, ‖f₁ z‖ ≤ M)
    (hf₂ : ∀ z : Point3, ‖f₂ z‖ ≤ M)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i₁ k₁)
        f₁
        x
      +
      h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i₂ k₂)
        f₂
        x‖
      ≤
    M *
      (
        h3BKMDyadicKernelL1Mass
            (1 : ℝ) zero_lt_one i₁ k₁
          +
        h3BKMDyadicKernelL1Mass
            (1 : ℝ) zero_lt_one i₂ k₂
      ) := by

  have h :=
    norm_h3BKMPhysicalConvolution_add_le
      (h3BKMDyadicPhysicalKernel R hR i₁ k₁)
      (h3BKMDyadicPhysicalKernel R hR i₂ k₂)
      f₁
      f₂
      M
      (h3BKMDyadicPhysicalKernel_integrable hR i₁ k₁)
      (h3BKMDyadicPhysicalKernel_integrable hR i₂ k₂)
      hf₁
      hf₂
      x

  rw [
    h3BKMDyadicPhysicalKernel_L1Mass_eq
      hR i₁ k₁,
    h3BKMDyadicPhysicalKernel_L1Mass_eq
      hR i₂ k₂,
    h3BKMDyadicKernelL1Mass_eq_unit
      hR i₁ k₁,
    h3BKMDyadicKernelL1Mass_eq_unit
      hR i₂ k₂
  ] at h

  exact h

/--
The x-vorticity contribution of every positive-radius dyadic BKM kernel is
bounded by the physical vorticity envelope times its unit-scale mass.
-/
theorem norm_h3BKMPhysicalConvolution_dyadic_vorticityX_le_unit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t R : ℝ}
    (hR : 0 < R)
    (hEnvelope : VorticityEnvelope u g t)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        (h3BKMPhysicalVorticityX u t)
        x‖
      ≤
    g t *
      h3BKMDyadicKernelL1Mass
        (1 : ℝ) zero_lt_one i k := by

  exact
    norm_h3BKMPhysicalConvolution_dyadic_le_unit
      hR
      i
      k
      (h3BKMPhysicalVorticityX u t)
      (g t)
      (norm_h3BKMPhysicalVorticityX_le hEnvelope)
      x

/-- Y-vorticity analogue of the scale-uniform dyadic convolution bound. -/
theorem norm_h3BKMPhysicalConvolution_dyadic_vorticityY_le_unit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t R : ℝ}
    (hR : 0 < R)
    (hEnvelope : VorticityEnvelope u g t)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        (h3BKMPhysicalVorticityY u t)
        x‖
      ≤
    g t *
      h3BKMDyadicKernelL1Mass
        (1 : ℝ) zero_lt_one i k := by

  exact
    norm_h3BKMPhysicalConvolution_dyadic_le_unit
      hR
      i
      k
      (h3BKMPhysicalVorticityY u t)
      (g t)
      (norm_h3BKMPhysicalVorticityY_le hEnvelope)
      x

/-- Z-vorticity analogue of the scale-uniform dyadic convolution bound. -/
theorem norm_h3BKMPhysicalConvolution_dyadic_vorticityZ_le_unit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t R : ℝ}
    (hR : 0 < R)
    (hEnvelope : VorticityEnvelope u g t)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        (h3BKMPhysicalVorticityZ u t)
        x‖
      ≤
    g t *
      h3BKMDyadicKernelL1Mass
        (1 : ℝ) zero_lt_one i k := by

  exact
    norm_h3BKMPhysicalConvolution_dyadic_le_unit
      hR
      i
      k
      (h3BKMPhysicalVorticityZ u t)
      (g t)
      (norm_h3BKMPhysicalVorticityZ_le hEnvelope)
      x

end

end Euclidean
end Bridge
end PrimeTensor

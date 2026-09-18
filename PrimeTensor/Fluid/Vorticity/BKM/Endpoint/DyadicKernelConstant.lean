import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicKernelBound

/-!
# BKM endpoint: one finite coordinate-kernel constant

Every dyadic coordinate kernel now has scale-independent `L¹` mass.  Since
there are only finitely many coordinate pairs `(i,k) : Fin 3 × Fin 3`, package
all unit-scale masses into one nonnegative constant

    C_BKM = ∑ᵢ ∑ₖ ‖Kᵢₖ,1‖₁.

Each individual unit-scale mass is bounded by `C_BKM`, so every positive-radius
dyadic physical convolution is controlled by the same constant, independently
of both radius and coordinate pair.

This is the finite-dimensional bookkeeping checkpoint immediately before the
middle-frequency shell count.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicKernelConstant
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointDyadicKernelConstant :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
A single finite constant dominating every unit-scale coordinate-kernel `L¹`
mass.
-/
noncomputable def h3BKMDyadicKernelUnitMassConstant : ℝ :=
  ∑ i : Fin 3,
    ∑ k : Fin 3,
      h3BKMDyadicKernelL1Mass
        (1 : ℝ) zero_lt_one i k

/-- The finite coordinate-kernel constant is nonnegative. -/
theorem h3BKMDyadicKernelUnitMassConstant_nonneg :
    0 ≤ h3BKMDyadicKernelUnitMassConstant := by

  unfold h3BKMDyadicKernelUnitMassConstant

  exact
    Finset.sum_nonneg
      (fun i _ =>
        Finset.sum_nonneg
          (fun k _ =>
            h3BKMDyadicKernelL1Mass_nonneg
              zero_lt_one i k))

/-- Every unit-scale coordinate-kernel mass is bounded by the finite constant. -/
theorem h3BKMDyadicKernelL1Mass_unit_le_constant
    (i k : Fin 3) :
    h3BKMDyadicKernelL1Mass
        (1 : ℝ) zero_lt_one i k
      ≤
    h3BKMDyadicKernelUnitMassConstant := by

  unfold h3BKMDyadicKernelUnitMassConstant

  calc
    h3BKMDyadicKernelL1Mass
        (1 : ℝ) zero_lt_one i k
        ≤
      ∑ k' : Fin 3,
        h3BKMDyadicKernelL1Mass
          (1 : ℝ) zero_lt_one i k' := by
      exact
        Finset.single_le_sum
          (fun k' _ =>
            h3BKMDyadicKernelL1Mass_nonneg
              zero_lt_one i k')
          (Finset.mem_univ k)

    _ ≤
      ∑ i' : Fin 3,
        ∑ k' : Fin 3,
          h3BKMDyadicKernelL1Mass
            (1 : ℝ) zero_lt_one i' k' := by
      exact
        Finset.single_le_sum
          (fun i' _ =>
            Finset.sum_nonneg
              (fun k' _ =>
                h3BKMDyadicKernelL1Mass_nonneg
                  zero_lt_one i' k'))
          (Finset.mem_univ i)

/--
Uniform physical convolution bound with no radius or coordinate dependence in
the kernel constant.
-/
theorem norm_h3BKMPhysicalConvolution_dyadic_le_constant
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (f : Point3 → ℂ)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hf : ∀ z : Point3, ‖f z‖ ≤ M)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        f
        x‖
      ≤
    M * h3BKMDyadicKernelUnitMassConstant := by

  calc
    ‖h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        f
        x‖
        ≤
      M *
        h3BKMDyadicKernelL1Mass
          (1 : ℝ) zero_lt_one i k :=
      norm_h3BKMPhysicalConvolution_dyadic_le_unit
        hR i k f M hf x

    _ ≤
      M * h3BKMDyadicKernelUnitMassConstant := by
      exact
        mul_le_mul_of_nonneg_left
          (h3BKMDyadicKernelL1Mass_unit_le_constant i k)
          hM

/--
The physical vorticity envelope itself is nonnegative at the selected time.
-/
theorem h3BKM_vorticityEnvelope_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t) :
    0 ≤ g t := by

  exact
    le_trans
      (norm_nonneg
        (h3BKMPhysicalVorticityX u t (0 : Point3)))
      (norm_h3BKMPhysicalVorticityX_le
        hEnvelope
        (0 : Point3))

/-- X-vorticity dyadic convolution controlled by the single BKM constant. -/
theorem norm_h3BKMPhysicalConvolution_dyadic_vorticityX_le_constant
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
    g t * h3BKMDyadicKernelUnitMassConstant := by

  exact
    norm_h3BKMPhysicalConvolution_dyadic_le_constant
      hR
      i
      k
      (h3BKMPhysicalVorticityX u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityX_le hEnvelope)
      x

/-- Y-vorticity dyadic convolution controlled by the single BKM constant. -/
theorem norm_h3BKMPhysicalConvolution_dyadic_vorticityY_le_constant
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
    g t * h3BKMDyadicKernelUnitMassConstant := by

  exact
    norm_h3BKMPhysicalConvolution_dyadic_le_constant
      hR
      i
      k
      (h3BKMPhysicalVorticityY u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityY_le hEnvelope)
      x

/-- Z-vorticity dyadic convolution controlled by the single BKM constant. -/
theorem norm_h3BKMPhysicalConvolution_dyadic_vorticityZ_le_constant
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
    g t * h3BKMDyadicKernelUnitMassConstant := by

  exact
    norm_h3BKMPhysicalConvolution_dyadic_le_constant
      hR
      i
      k
      (h3BKMPhysicalVorticityZ u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityZ_le hEnvelope)
      x

end

end Euclidean
end Bridge
end PrimeTensor

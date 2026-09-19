import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.MiddleMultiplierKernel

/-!
# BKM endpoint: logarithmic `L¹` bound for the finite middle kernel

The middle-frequency multiplier is now packaged as one Schwartz symbol and its
inverse Fourier transform as one physical kernel.  This file proves the
operator estimate needed for that packaged kernel.

The physical middle kernel is the finite sum

    Kᵢₖ,[lo,hi] = ∑ₙ Kᵢₖ,2ⁿ.

The triangle inequality gives

    ‖Kᵢₖ,[lo,hi]‖₁
      ≤ #(Icc lo hi) · C_BKM,

because every dyadic coordinate kernel has scale-independent `L¹` mass bounded
by the universal finite coordinate constant.  For `lo ≤ hi`, the previously
proved shell-count identity converts this exactly to

    ‖Kᵢₖ,[lo,hi]‖₁
      ≤ logWidth(lo,hi) · C_BKM.

Feeding this into the generic physical convolution estimate gives the packaged
middle-frequency BKM operator bound directly, including the three physical
vorticity components.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointMiddleKernelBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointMiddleKernelBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The `L¹` mass of the packaged middle physical kernel is bounded by the number
of occupied dyadic shells times the universal BKM kernel constant.
-/
theorem h3BKMMiddleDyadicPhysicalKernel_L1Mass_le_card_mul
    (lo hi : ℕ)
    (i k : Fin 3) :
    (∫ x : Point3,
        ‖h3BKMMiddleDyadicPhysicalKernel lo hi i k x‖
        ∂(volume : Measure Point3))
      ≤
    ((Finset.Icc lo hi).card : ℝ)
      * h3BKMDyadicKernelUnitMassConstant := by

  let J : Finset ℕ := Finset.Icc lo hi

  have hEachNorm :
      ∀ n ∈ J,
        Integrable
          (fun x : Point3 =>
            ‖h3BKMDyadicPhysicalKernel
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i
                k
                x‖)
          (volume : Measure Point3) := by
    intro n hn
    exact
      (h3BKMDyadicPhysicalKernel_integrable
        (h3BKMDyadicRadius_pos n)
        i
        k).norm

  have hSumNorm :
      Integrable
        (fun x : Point3 =>
          ∑ n ∈ J,
            ‖h3BKMDyadicPhysicalKernel
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i
                k
                x‖)
        (volume : Measure Point3) := by

    have hRaw :
        Integrable
          (
            ∑ n ∈ J,
              fun x : Point3 =>
                ‖h3BKMDyadicPhysicalKernel
                    (h3BKMDyadicRadius n)
                    (h3BKMDyadicRadius_pos n)
                    i
                    k
                    x‖
          )
          (volume : Measure Point3) :=
      integrable_finsetSum'
        J
        (fun n hn => hEachNorm n hn)

    have hEq :
        (
          ∑ n ∈ J,
            fun x : Point3 =>
              ‖h3BKMDyadicPhysicalKernel
                  (h3BKMDyadicRadius n)
                  (h3BKMDyadicRadius_pos n)
                  i
                  k
                  x‖
        )
          =
        (fun x : Point3 =>
          ∑ n ∈ J,
            ‖h3BKMDyadicPhysicalKernel
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i
                k
                x‖) := by
      funext x
      rw [Finset.sum_apply]

    rw [← hEq]
    exact hRaw

  have hMiddleNorm :
      Integrable
        (fun x : Point3 =>
          ‖h3BKMMiddleDyadicPhysicalKernel
              lo hi i k x‖)
        (volume : Measure Point3) :=
    (h3BKMMiddleDyadicPhysicalKernel_integrable
      lo hi i k).norm

  have hPoint :
      ∀ x : Point3,
        ‖h3BKMMiddleDyadicPhysicalKernel
            lo hi i k x‖
          ≤
        ∑ n ∈ J,
          ‖h3BKMDyadicPhysicalKernel
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i
              k
              x‖ := by
    intro x

    rw [
      h3BKMMiddleDyadicPhysicalKernel_eq_sum
        lo hi i k x
    ]

    exact
      norm_sum_le
        J
        (fun n =>
          h3BKMDyadicPhysicalKernel
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i
            k
            x)

  have hIntegralSum :
      (∫ x : Point3,
          ∑ n ∈ J,
            ‖h3BKMDyadicPhysicalKernel
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i
                k
                x‖
          ∂(volume : Measure Point3))
        =
      ∑ n ∈ J,
        ∫ x : Point3,
          ‖h3BKMDyadicPhysicalKernel
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i
              k
              x‖
          ∂(volume : Measure Point3) := by
    simpa only [Finset.sum_apply] using
      (integral_finsetSum
        (μ := (volume : Measure Point3))
        J
        (fun n hn => hEachNorm n hn))

  change
    (∫ x : Point3,
        ‖h3BKMMiddleDyadicPhysicalKernel lo hi i k x‖
        ∂(volume : Measure Point3))
      ≤
    (J.card : ℝ)
      * h3BKMDyadicKernelUnitMassConstant

  calc
    (∫ x : Point3,
        ‖h3BKMMiddleDyadicPhysicalKernel lo hi i k x‖
        ∂(volume : Measure Point3))
        ≤
      ∫ x : Point3,
        ∑ n ∈ J,
          ‖h3BKMDyadicPhysicalKernel
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i
              k
              x‖
        ∂(volume : Measure Point3) := by
      exact
        integral_mono
          hMiddleNorm
          hSumNorm
          hPoint

    _ =
      ∑ n ∈ J,
        ∫ x : Point3,
          ‖h3BKMDyadicPhysicalKernel
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i
              k
              x‖
          ∂(volume : Measure Point3) :=
      hIntegralSum

    _ =
      ∑ _n ∈ J,
        h3BKMDyadicKernelL1Mass
          (1 : ℝ) zero_lt_one i k := by
      apply Finset.sum_congr rfl
      intro n hn

      rw [
        h3BKMDyadicPhysicalKernel_L1Mass_eq
          (h3BKMDyadicRadius_pos n)
          i
          k,
        h3BKMDyadicKernelL1Mass_eq_unit
          (h3BKMDyadicRadius_pos n)
          i
          k
      ]

    _ ≤
      ∑ _n ∈ J,
        h3BKMDyadicKernelUnitMassConstant := by
      exact
        Finset.sum_le_sum
          (fun n hn =>
            h3BKMDyadicKernelL1Mass_unit_le_constant
              i k)

    _ =
      (J.card : ℝ)
        * h3BKMDyadicKernelUnitMassConstant := by
      simp

/--
For a nonempty ordered middle window, the packaged physical kernel has the
exact logarithmic shell-width upper bound.
-/
theorem h3BKMMiddleDyadicPhysicalKernel_L1Mass_le_logWidth_mul
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (i k : Fin 3) :
    (∫ x : Point3,
        ‖h3BKMMiddleDyadicPhysicalKernel lo hi i k x‖
        ∂(volume : Measure Point3))
      ≤
    h3BKMMiddleDyadicLogWidth lo hi
      * h3BKMDyadicKernelUnitMassConstant := by

  have h :=
    h3BKMMiddleDyadicPhysicalKernel_L1Mass_le_card_mul
      lo hi i k

  rw [
    h3BKMMiddleDyadicShellCount
      lo hi,
    ← h3BKMMiddleDyadicLogWidth_eq_shellCount
      hlohi
  ] at h

  exact h

/--
A bounded scalar field acted on by the single packaged middle kernel obeys the
logarithmic BKM operator bound.
-/
theorem norm_h3BKMPhysicalConvolution_middle_le_logWidth
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (i k : Fin 3)
    (f : Point3 → ℂ)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hf : ∀ z : Point3, ‖f z‖ ≤ M)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        (h3BKMMiddleDyadicPhysicalKernel lo hi i k)
        f
        x‖
      ≤
    h3BKMMiddleDyadicLogWidth lo hi
      * (M * h3BKMDyadicKernelUnitMassConstant) := by

  calc
    ‖h3BKMPhysicalConvolution
        (h3BKMMiddleDyadicPhysicalKernel lo hi i k)
        f
        x‖
        ≤
      M *
        (∫ y : Point3,
          ‖h3BKMMiddleDyadicPhysicalKernel lo hi i k y‖
          ∂(volume : Measure Point3)) :=
      norm_h3BKMPhysicalConvolution_le
        (h3BKMMiddleDyadicPhysicalKernel lo hi i k)
        f
        M
        (h3BKMMiddleDyadicPhysicalKernel_integrable
          lo hi i k)
        hf
        x

    _ ≤
      M *
        (
          h3BKMMiddleDyadicLogWidth lo hi
            * h3BKMDyadicKernelUnitMassConstant
        ) := by
      exact
        mul_le_mul_of_nonneg_left
          (h3BKMMiddleDyadicPhysicalKernel_L1Mass_le_logWidth_mul
            hlohi i k)
          hM

    _ =
      h3BKMMiddleDyadicLogWidth lo hi
        * (M * h3BKMDyadicKernelUnitMassConstant) := by
      ring

/-- X-vorticity bound for the single packaged middle-frequency kernel. -/
theorem norm_h3BKMPhysicalConvolution_middle_vorticityX_le_logWidth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (hEnvelope : VorticityEnvelope u g t)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        (h3BKMMiddleDyadicPhysicalKernel lo hi i k)
        (h3BKMPhysicalVorticityX u t)
        x‖
      ≤
    h3BKMMiddleDyadicLogWidth lo hi
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMPhysicalConvolution_middle_le_logWidth
      hlohi
      i
      k
      (h3BKMPhysicalVorticityX u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityX_le hEnvelope)
      x

/-- Y-vorticity bound for the single packaged middle-frequency kernel. -/
theorem norm_h3BKMPhysicalConvolution_middle_vorticityY_le_logWidth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (hEnvelope : VorticityEnvelope u g t)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        (h3BKMMiddleDyadicPhysicalKernel lo hi i k)
        (h3BKMPhysicalVorticityY u t)
        x‖
      ≤
    h3BKMMiddleDyadicLogWidth lo hi
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMPhysicalConvolution_middle_le_logWidth
      hlohi
      i
      k
      (h3BKMPhysicalVorticityY u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityY_le hEnvelope)
      x

/-- Z-vorticity bound for the single packaged middle-frequency kernel. -/
theorem norm_h3BKMPhysicalConvolution_middle_vorticityZ_le_logWidth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (hEnvelope : VorticityEnvelope u g t)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        (h3BKMMiddleDyadicPhysicalKernel lo hi i k)
        (h3BKMPhysicalVorticityZ u t)
        x‖
      ≤
    h3BKMMiddleDyadicLogWidth lo hi
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMPhysicalConvolution_middle_le_logWidth
      hlohi
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

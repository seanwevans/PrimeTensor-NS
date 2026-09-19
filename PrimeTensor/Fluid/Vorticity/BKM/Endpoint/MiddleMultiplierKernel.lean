import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.LocalizedGradientShellSum

/-!
# BKM endpoint: one finite middle multiplier and one finite middle kernel

The middle-frequency Fourier identity is now a finite sum of localized
coordinate multipliers.  Package that finite sum as a single Schwartz symbol,

    Mᵢₖ,[lo,hi] = ∑ₙ Mᵢₖ,2ⁿ,

and take its inverse Fourier transform once.

Because inverse Fourier transform is additive on Schwartz space, the resulting
middle kernel is exactly the finite sum of the already-constructed dyadic
kernels.  Pulling it back through `WithLp.toLp` gives the corresponding physical
kernel, again pointwise equal to the finite dyadic kernel sum.

This is the operator-level bridge needed before identifying multiplication by
the middle Fourier symbol with physical convolution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform SchwartzMap

noncomputable section

noncomputable local instance axisFintypeBKMEndpointMiddleMultiplierKernel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointMiddleMultiplierKernel :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
Finite middle-frequency localized coordinate multiplier as one Schwartz map.
-/
noncomputable def h3BKMMiddleLocalizedCoordinateMultiplierSchwartz
    (lo hi : ℕ)
    (i k : Fin 3) :
    𝓢(H3FourierPoint3, ℂ) :=
  ∑ n ∈ Finset.Icc lo hi,
    h3BKMLocalizedCoordinateMultiplierSchwartz
      (h3BKMDyadicRadius n)
      (h3BKMDyadicRadius_pos n)
      i
      k

@[simp]
theorem h3BKMMiddleLocalizedCoordinateMultiplierSchwartz_apply
    (lo hi : ℕ)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) :
    h3BKMMiddleLocalizedCoordinateMultiplierSchwartz
        lo hi i k ξ
      =
    ∑ n ∈ Finset.Icc lo hi,
      h3BKMLocalizedCoordinateMultiplier
        (h3BKMDyadicRadius n)
        (h3BKMDyadicRadius_pos n)
        i
        k
        ξ := by

  unfold h3BKMMiddleLocalizedCoordinateMultiplierSchwartz

  simp only [
    _root_.sum_apply,
    h3BKMLocalizedCoordinateMultiplierSchwartz_apply
  ]

/--
Inverse Fourier transform of the complete finite middle-frequency multiplier.
-/
noncomputable def h3BKMMiddleDyadicKernelSchwartz
    (lo hi : ℕ)
    (i k : Fin 3) :
    𝓢(H3FourierPoint3, ℂ) :=
  𝓕⁻
    (h3BKMMiddleLocalizedCoordinateMultiplierSchwartz
      lo hi i k)

/--
Inverse Fourier transform commutes with the finite middle shell sum.
-/
theorem h3BKMMiddleDyadicKernelSchwartz_eq_sum
    (lo hi : ℕ)
    (i k : Fin 3) :
    h3BKMMiddleDyadicKernelSchwartz lo hi i k
      =
    ∑ n ∈ Finset.Icc lo hi,
      h3BKMDyadicKernelSchwartz
        (h3BKMDyadicRadius n)
        (h3BKMDyadicRadius_pos n)
        i
        k := by

  unfold
    h3BKMMiddleDyadicKernelSchwartz
    h3BKMMiddleLocalizedCoordinateMultiplierSchwartz
    h3BKMDyadicKernelSchwartz

  exact
    FourierTransform.fourierInv_sum
      (fun n =>
        h3BKMLocalizedCoordinateMultiplierSchwartz
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i
          k)
      (Finset.Icc lo hi)

/-- Pointwise function underlying the finite middle inverse-Fourier kernel. -/
noncomputable def h3BKMMiddleDyadicKernel
    (lo hi : ℕ)
    (i k : Fin 3)
    (x : H3FourierPoint3) : ℂ :=
  h3BKMMiddleDyadicKernelSchwartz lo hi i k x

/--
The pointwise middle kernel is the finite sum of the dyadic kernels.
-/
theorem h3BKMMiddleDyadicKernel_eq_sum
    (lo hi : ℕ)
    (i k : Fin 3)
    (x : H3FourierPoint3) :
    h3BKMMiddleDyadicKernel lo hi i k x
      =
    ∑ n ∈ Finset.Icc lo hi,
      h3BKMDyadicKernel
        (h3BKMDyadicRadius n)
        (h3BKMDyadicRadius_pos n)
        i
        k
        x := by

  unfold h3BKMMiddleDyadicKernel

  rw [
    h3BKMMiddleDyadicKernelSchwartz_eq_sum
      lo hi i k
  ]

  simp only [
    _root_.sum_apply,
    h3BKMDyadicKernel_apply
  ]

/-- The complete finite middle kernel is integrable. -/
theorem h3BKMMiddleDyadicKernel_integrable
    (lo hi : ℕ)
    (i k : Fin 3) :
    Integrable
      (h3BKMMiddleDyadicKernel lo hi i k)
      (volume : Measure H3FourierPoint3) := by

  change
    Integrable
      (h3BKMMiddleDyadicKernelSchwartz lo hi i k :
        H3FourierPoint3 → ℂ)
      (volume : Measure H3FourierPoint3)

  exact
    (h3BKMMiddleDyadicKernelSchwartz
      lo hi i k).integrable

/--
Physical pullback of the complete finite middle inverse-Fourier kernel.
-/
noncomputable def h3BKMMiddleDyadicPhysicalKernel
    (lo hi : ℕ)
    (i k : Fin 3)
    (x : Point3) : ℂ :=
  h3BKMMiddleDyadicKernel
    lo hi i k
    ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

/--
The physical middle kernel is pointwise the finite sum of the physical dyadic
kernels.
-/
theorem h3BKMMiddleDyadicPhysicalKernel_eq_sum
    (lo hi : ℕ)
    (i k : Fin 3)
    (x : Point3) :
    h3BKMMiddleDyadicPhysicalKernel lo hi i k x
      =
    ∑ n ∈ Finset.Icc lo hi,
      h3BKMDyadicPhysicalKernel
        (h3BKMDyadicRadius n)
        (h3BKMDyadicRadius_pos n)
        i
        k
        x := by

  unfold h3BKMMiddleDyadicPhysicalKernel

  rw [
    h3BKMMiddleDyadicKernel_eq_sum
      lo hi i k
  ]

  rfl

/-- The physical finite middle kernel is integrable. -/
theorem h3BKMMiddleDyadicPhysicalKernel_integrable
    (lo hi : ℕ)
    (i k : Fin 3) :
    Integrable
      (h3BKMMiddleDyadicPhysicalKernel lo hi i k)
      (volume : Measure Point3) := by

  change
    Integrable
      (
        h3BKMMiddleDyadicKernel lo hi i k
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
      (h3BKMMiddleDyadicKernel_integrable
        lo hi i k)

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedForcingFourierGradientDifferenceBound

/-!
# Classicalization: inverse-Fourier gradient difference bound

The ordinary Fourier-side first-gradient difference estimate is now available.
The physical forcing representative, however, is reconstructed with the inverse
Fourier transform.

On a real inner-product space Mathlib identifies

    𝓕⁻ f(x) = 𝓕 f(-x).

The Fréchet derivative of precomposition by `x ↦ -x` is multiplication by
`-1`, hence preserves operator norm.  Therefore the same first weighted `L¹`
bound transfers verbatim to inverse Fourier reconstruction.

This file isolates that transport so the next selected-path increment can work
directly with the physical forcing representative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingInverseFourierGradientDifferenceBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The inverse Fourier Fréchet derivative obeys the same first weighted `L¹`
difference estimate as the ordinary Fourier transform. -/
theorem norm_fderiv_fourierInv_sub_le_firstMass
    (f g : H3FourierPoint3 → ℂ)
    (hf0 :
      Integrable f
        (volume : Measure H3FourierPoint3))
    (hg0 :
      Integrable g
        (volume : Measure H3FourierPoint3))
    (hf1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3))
    (hg1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖g ξ‖)
        (volume : Measure H3FourierPoint3))
    (hfg1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖f ξ - g ξ‖)
        (volume : Measure H3FourierPoint3))
    (x : H3FourierPoint3) :
    ‖fderiv ℝ (FourierTransformInv.fourierInv f) x -
        fderiv ℝ (FourierTransformInv.fourierInv g) x‖
      ≤
    h3FourierFirstDerivativeL1Coefficient *
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ * ‖f ξ - g ξ‖ := by
  have hfInv :
      FourierTransformInv.fourierInv f
        =
      (fun y : H3FourierPoint3 =>
        FourierTransform.fourier f ((-1 : ℝ) • y)) := by
    funext y
    rw [Real.fourierInv_eq_fourier_neg]
    congr 1
    simp

  have hgInv :
      FourierTransformInv.fourierInv g
        =
      (fun y : H3FourierPoint3 =>
        FourierTransform.fourier g ((-1 : ℝ) • y)) := by
    funext y
    rw [Real.fourierInv_eq_fourier_neg]
    congr 1
    simp

  rw [hfInv, hgInv]

  rw [
    fderiv_comp_smul,
    fderiv_comp_smul
  ]

  have hBase :=
    norm_fderiv_fourier_sub_le_firstMass
      f g hf0 hg0 hf1 hg1 hfg1
      ((-1 : ℝ) • x)

  have hNeg :
      (-1 : ℝ) •
          fderiv ℝ (FourierTransform.fourier f)
            ((-1 : ℝ) • x)
        -
      (-1 : ℝ) •
          fderiv ℝ (FourierTransform.fourier g)
            ((-1 : ℝ) • x)
        =
      (-1 : ℝ) •
        (fderiv ℝ (FourierTransform.fourier f)
            ((-1 : ℝ) • x)
          -
        fderiv ℝ (FourierTransform.fourier g)
            ((-1 : ℝ) • x)) := by
    rw [smul_sub]

  rw [hNeg]

  have hNegOneNorm :
      ‖(-1 : ℝ)‖ = 1 := by
    norm_num

  rw [norm_smul, hNegOneNorm, one_mul]

  exact hBase

end

end Euclidean
end Bridge
end PrimeTensor

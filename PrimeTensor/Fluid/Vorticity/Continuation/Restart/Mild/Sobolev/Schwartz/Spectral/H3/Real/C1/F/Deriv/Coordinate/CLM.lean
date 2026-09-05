import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.F.Deriv.Coordinate.Bound

/-!
# Bounded coordinate-derivative evaluation on spectral H³

The preceding quantitative estimate shows that, for fixed spatial coordinate
`i` and point `x`,

    G ↦ D_i (C¹(G))(x)

is bounded by a fixed multiple of the H³ norm.

This file packages that operation as a genuine complex continuous linear map

    H3SpectralScalarState →L[ℂ] ℂ.

The only subtlety is that an `Lp` state is represented pointwise only up to
almost-everywhere equality.  We therefore prove additivity and scalar
linearity on the raw Fourier derivative multiplier almost everywhere, then
use inverse-Fourier integral linearity.  This is exactly the same pattern as
Mathlib's `Lp.fourierTransformCLM`.

The resulting map is the object needed to commute one spatial derivative
evaluation through the H³-valued Bochner Duhamel integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3RealC1FDerivCoordinateCLM
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw coordinate Fourier differentiation respects addition almost
everywhere on weighted H³ states. -/
theorem h3SpectralScalarRawFourierCoordinateDerivative_add_ae
    (G H : H3SpectralScalarState)
    (i : Fin 3) :
    h3SpectralScalarRawFourierCoordinateDerivative (G + H) i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SpectralScalarRawFourierCoordinateDerivative G i +
      h3SpectralScalarRawFourierCoordinateDerivative H i := by
  filter_upwards [MeasureTheory.Lp.coeFn_add G H] with ξ hξ
  unfold
    h3SpectralScalarRawFourierCoordinateDerivative
    h3SpectralScalarRawFourier
  rw [hξ]
  simp only [Pi.add_apply]
  ring

/-- Raw coordinate Fourier differentiation respects complex scalar
multiplication almost everywhere on weighted H³ states. -/
theorem h3SpectralScalarRawFourierCoordinateDerivative_smul_ae
    (c : ℂ)
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    h3SpectralScalarRawFourierCoordinateDerivative (c • G) i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    c • h3SpectralScalarRawFourierCoordinateDerivative G i := by
  filter_upwards [MeasureTheory.Lp.coeFn_smul c G] with ξ hξ
  unfold
    h3SpectralScalarRawFourierCoordinateDerivative
    h3SpectralScalarRawFourier
  rw [hξ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Algebraic coordinate derivative evaluation of the canonical H³ `C¹`
representative.  It is separated from the continuity packaging so later norm
proofs do not need to unfold the a.e. linearity witnesses. -/
noncomputable def h3SpectralScalarC1CoordinateDerivativeEvaluationLM
    (i : Fin 3)
    (x : H3FourierPoint3) :
    H3SpectralScalarState →ₗ[ℂ] ℂ :=
  {
    toFun := fun G =>
      FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative G i)
        x
    map_add' := by
      intro G H

      let DG : H3FourierPoint3 → ℂ :=
        h3SpectralScalarRawFourierCoordinateDerivative G i
      let DH : H3FourierPoint3 → ℂ :=
        h3SpectralScalarRawFourierCoordinateDerivative H i
      let DGH : H3FourierPoint3 → ℂ :=
        h3SpectralScalarRawFourierCoordinateDerivative (G + H) i

      have hDG :
          Integrable DG
            (volume : Measure H3FourierPoint3) := by
        dsimp only [DG]
        exact
          h3SpectralScalarRawFourierCoordinateDerivative_integrable
            G i

      have hDH :
          Integrable DH
            (volume : Measure H3FourierPoint3) := by
        dsimp only [DH]
        exact
          h3SpectralScalarRawFourierCoordinateDerivative_integrable
            H i

      have hAdd :
          DGH
            =ᵐ[(volume : Measure H3FourierPoint3)]
          DG + DH := by
        dsimp only [DGH, DG, DH]
        exact
          h3SpectralScalarRawFourierCoordinateDerivative_add_ae
            G H i

      change
        FourierTransformInv.fourierInv DGH x
          =
        FourierTransformInv.fourierInv DG x +
          FourierTransformInv.fourierInv DH x

      rw [
        Real.fourierInv_eq,
        Real.fourierInv_eq,
        Real.fourierInv_eq,
        ← integral_add
      ]
      · apply integral_congr_ae
        filter_upwards [hAdd] with ξ hξ
        rw [hξ]
        simp only [Pi.add_apply, smul_add]
      · have h :=
          (Real.fourierIntegral_convergent_iff
            (f := DG) (-x)).2 hDG
        simpa using h
      · have h :=
          (Real.fourierIntegral_convergent_iff
            (f := DH) (-x)).2 hDH
        simpa using h

    map_smul' := by
      intro c G

      let DG : H3FourierPoint3 → ℂ :=
        h3SpectralScalarRawFourierCoordinateDerivative G i
      let DcG : H3FourierPoint3 → ℂ :=
        h3SpectralScalarRawFourierCoordinateDerivative (c • G) i

      have hSmul :
          DcG
            =ᵐ[(volume : Measure H3FourierPoint3)]
          c • DG := by
        dsimp only [DcG, DG]
        exact
          h3SpectralScalarRawFourierCoordinateDerivative_smul_ae
            c G i

      change
        FourierTransformInv.fourierInv DcG x
          =
        c • FourierTransformInv.fourierInv DG x

      rw [
        Real.fourierInv_eq,
        Real.fourierInv_eq,
        ← integral_smul
      ]
      apply integral_congr_ae
      filter_upwards [hSmul] with ξ hξ
      rw [hξ, smul_comm]
      simp
  }

/-- The algebraic evaluation map has the expected raw inverse-Fourier value. -/
@[simp]
theorem h3SpectralScalarC1CoordinateDerivativeEvaluationLM_apply
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3SpectralScalarC1CoordinateDerivativeEvaluationLM i x G
      =
    FourierTransformInv.fourierInv
      (h3SpectralScalarRawFourierCoordinateDerivative G i)
      x := by
  rfl

/-- Coordinate derivative evaluation of the canonical H³ `C¹`
representative, packaged as a bounded complex-linear functional of the
spectral H³ state. -/
noncomputable def h3SpectralScalarC1CoordinateDerivativeEvaluationCLM
    (i : Fin 3)
    (x : H3FourierPoint3) :
    H3SpectralScalarState →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    (h3SpectralScalarC1CoordinateDerivativeEvaluationLM i x)
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
    (fun G => by
      rw [
        h3SpectralScalarC1CoordinateDerivativeEvaluationLM_apply,
        ← h3SpectralScalarC1Representative_fderiv_apply_fin
          G i x
      ]
      exact
        norm_h3SpectralScalarC1Representative_fderiv_apply_fin_le
          G i x)

/-- The bounded functional is exactly the coordinate value of the canonical
Fréchet derivative of the H³ `C¹` representative. -/
@[simp]
theorem h3SpectralScalarC1CoordinateDerivativeEvaluationCLM_apply
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3SpectralScalarC1CoordinateDerivativeEvaluationCLM i x G
      =
    (fderiv ℝ
        (h3SpectralScalarC1Representative G)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 i)) := by
  change
    FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative G i)
        x
      =
    (fderiv ℝ
        (h3SpectralScalarC1Representative G)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 i))
  exact
    (h3SpectralScalarC1Representative_fderiv_apply_fin
      G i x).symm

end

end Euclidean
end Bridge
end PrimeTensor

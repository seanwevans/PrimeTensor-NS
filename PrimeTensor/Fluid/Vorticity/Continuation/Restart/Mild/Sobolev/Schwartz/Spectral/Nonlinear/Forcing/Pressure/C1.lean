import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Bounded
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# C¹ inverse-Fourier reconstruction of the H³ pressure

`Pressure.Bounded` rewrites the pressure Fourier multiplier as a finite double
sum of bounded rank-one Leray coefficients times raw H³ product convolutions.

The raw product convolution already has one integrable Fourier moment.  Because
every rank-one coefficient has norm at most one, the same first-moment bound
passes to the pressure multiplier:

    ‖ξ‖ |p̂(ξ)| ∈ L¹.

Together with the zeroth-moment `L¹` theorem from `Pressure.Bounded`, Mathlib's
Fourier differentiability theorem gives a canonical classical `C¹`
inverse-Fourier pressure representative.

This file packages both the complex representative and its real part, including
transport to the project's `Point3` carrier.  The next rung identifies its
coordinate derivatives with the real Leray-complement forcing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal FourierTransform Topology

noncomputable section

noncomputable local instance axisFintypeH3PressureC1
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The first Fourier moment of the pressure multiplier is integrable. -/
theorem h3RawFinPressureFourier_firstMoment_integrable
    (U V : H3SpectralFinVectorState) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ * ‖h3RawFinPressureFourier U V ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hMajorantExpanded :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ k : Fin 3,
            ∑ j : Fin 3,
              ‖ξ‖ *
                ‖h3RawProductConvolution (U k) (V j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      integrable_finset_sum
        (Finset.univ : Finset (Fin 3))
        (fun k _ =>
          integrable_finset_sum
            (Finset.univ : Finset (Fin 3))
            (fun j _ =>
              h3RawProductConvolution_firstMoment_integrable
                (U k) (V j)))

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            (∑ k : Fin 3,
              ∑ j : Fin 3,
                ‖h3RawProductConvolution (U k) (V j) ξ‖))
        (volume : Measure H3FourierPoint3) := by
    simpa only [Finset.mul_sum] using hMajorantExpanded

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h3RawFinPressureFourier U V ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      continuous_norm.aestronglyMeasurable.mul
        (h3RawFinPressureFourier_integrable U V).norm.aestronglyMeasurable

  refine Integrable.mono' hMajorant hTargetMeas ?_
  filter_upwards with ξ

  rw [
    h3RawFinPressureFourier_eq_neg_sum_rankOne_rawProductConvolution
  ]
  rw [norm_neg]

  have hNorm :
      ‖∑ k : Fin 3,
          ∑ j : Fin 3,
            h3LerayRankOneCoefficient ξ j k *
              h3RawProductConvolution (U k) (V j) ξ‖
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          ‖h3RawProductConvolution (U k) (V j) ξ‖ := by
    calc
      ‖∑ k : Fin 3,
          ∑ j : Fin 3,
            h3LerayRankOneCoefficient ξ j k *
              h3RawProductConvolution (U k) (V j) ξ‖
          ≤
        ∑ k : Fin 3,
          ‖∑ j : Fin 3,
            h3LerayRankOneCoefficient ξ j k *
              h3RawProductConvolution (U k) (V j) ξ‖ := by
            exact norm_sum_le _ _
      _ ≤
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            ‖h3LerayRankOneCoefficient ξ j k *
              h3RawProductConvolution (U k) (V j) ξ‖ := by
            exact
              Finset.sum_le_sum
                (fun k _ => norm_sum_le _ _)
      _ ≤
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            ‖h3RawProductConvolution (U k) (V j) ξ‖ := by
            exact
              Finset.sum_le_sum
                (fun k _ =>
                  Finset.sum_le_sum
                    (fun j _ => by
                      rw [norm_mul]
                      exact
                        mul_le_of_le_one_left
                          (norm_nonneg
                            (h3RawProductConvolution
                              (U k) (V j) ξ))
                          (norm_h3LerayRankOneCoefficient_le_one
                            ξ j k)))

  have hMul :
      ‖ξ‖ *
          ‖∑ k : Fin 3,
              ∑ j : Fin 3,
                h3LerayRankOneCoefficient ξ j k *
                  h3RawProductConvolution (U k) (V j) ξ‖
        ≤
      ‖ξ‖ *
        (∑ k : Fin 3,
          ∑ j : Fin 3,
            ‖h3RawProductConvolution (U k) (V j) ξ‖) :=
    mul_le_mul_of_nonneg_left
      hNorm
      (norm_nonneg ξ)

  have hLeftNonneg :
      0 ≤
        ‖ξ‖ *
          ‖∑ k : Fin 3,
              ∑ j : Fin 3,
                h3LerayRankOneCoefficient ξ j k *
                  h3RawProductConvolution (U k) (V j) ξ‖ := by
    positivity

  simpa [
    Real.norm_eq_abs,
    abs_of_nonneg hLeftNonneg
  ] using hMul

/-- Pressure Fourier moments through order one are integrable. -/
theorem h3RawFinPressureFourier_moment_integrable_one
    (U V : H3SpectralFinVectorState)
    (n : ℕ)
    (hn : n ≤ 1) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ n * ‖h3RawFinPressureFourier U V ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hnCases : n = 0 ∨ n = 1 := by omega
  rcases hnCases with rfl | rfl
  · simpa using (h3RawFinPressureFourier_integrable U V).norm
  · simpa using h3RawFinPressureFourier_firstMoment_integrable U V

/-- Ordinary inverse-Fourier reconstruction of the pressure multiplier. -/
noncomputable def h3RawFinPressureC1Representative
    (U V : H3SpectralFinVectorState) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3RawFinPressureFourier U V)

/-- The pressure multiplier has a classical complex `C¹` inverse-Fourier
representative. -/
theorem h3RawFinPressureC1Representative_contDiff_one
    (U V : H3SpectralFinVectorState) :
    ContDiff ℝ 1
      (h3RawFinPressureC1Representative U V) := by
  have hFourier :
      ContDiff ℝ 1
        (FourierTransform.fourier
          (h3RawFinPressureFourier U V)) := by
    apply Real.contDiff_fourier
    intro n hn
    have hn' : n ≤ 1 := by simpa using hn
    exact h3RawFinPressureFourier_moment_integrable_one U V n hn'

  have hEq :
      h3RawFinPressureC1Representative U V
        =
      fun x : H3FourierPoint3 =>
        FourierTransform.fourier
          (h3RawFinPressureFourier U V)
          (-x) := by
    funext x
    unfold h3RawFinPressureC1Representative
    exact
      Real.fourierInv_eq_fourier_neg
        (h3RawFinPressureFourier U V) x

  rw [hEq]
  exact hFourier.comp (by fun_prop)

/-- Real part of the canonical complex pressure representative. -/
noncomputable def h3RawFinPressureRealC1Representative
    (U V : H3SpectralFinVectorState) :
    H3FourierPoint3 → ℝ :=
  fun x =>
    (h3RawFinPressureC1Representative U V x).re

/-- The real pressure representative is spatially `C¹`. -/
theorem h3RawFinPressureRealC1Representative_contDiff_one
    (U V : H3SpectralFinVectorState) :
    ContDiff ℝ 1
      (h3RawFinPressureRealC1Representative U V) := by
  unfold h3RawFinPressureRealC1Representative
  simpa [Function.comp_def] using
    (h3RawFinPressureC1Representative_contDiff_one U V).continuousLinearMap_comp
      Complex.reCLM

/-- Real pressure representative transported to `Point3`. -/
noncomputable def h3RawFinPressureRealC1RepresentativeOnPoint3
    (U V : H3SpectralFinVectorState) :
    Point3 → ℝ :=
  fun x =>
    h3RawFinPressureRealC1Representative U V
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

/-- Transport to `Point3` preserves pressure `C¹` regularity. -/
theorem h3RawFinPressureRealC1RepresentativeOnPoint3_contDiff_one
    (U V : H3SpectralFinVectorState) :
    ContDiff ℝ 1
      (h3RawFinPressureRealC1RepresentativeOnPoint3 U V) := by
  have hToLp :
      ContDiff ℝ 1
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) := by
    exact PiLp.contDiff_toLp

  unfold h3RawFinPressureRealC1RepresentativeOnPoint3
  exact
    (h3RawFinPressureRealC1Representative_contDiff_one U V).comp
      hToLp

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.PDE.Algebra
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Encoder

/-!
# Fourier symbol of the physical velocity Laplacian

This file closes the diffusion algebra needed for the projected spectral
Navier--Stokes equation.

For the project's Fourier convention

    dᵢ(ξ) = 2π i ξᵢ,

we first prove the exact finite identity

    Σᵢ dᵢ(ξ)^2 = -q(ξ),

where `q(ξ) = (2π)^2 ‖ξ‖^2` is `h3FourierGradientSquare`.

The already-established order-two Fourier compatibility of a genuine H³
velocity snapshot then gives, almost everywhere,

    Σᵢ 𝓕(∂ᵢ∂ᵢ uⱼ)(ξ)
      = -q(ξ) 𝓕(uⱼ)(ξ).

No time evolution, pressure elimination, or variation of constants is used
here.  This is precisely the diffusion multiplier identity needed by the next
PDE-to-spectral rung.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3FinHeatLerayDiffusionFourier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Diagonal second-derivative symbol -/

/-- The sum of the three diagonal second-derivative Fourier symbols is exactly
    minus the heat frequency `q(ξ)`. -/
theorem sum_h3FourierDerivativeSymbol2_diag_eq_neg_gradientSquare
    (ξ : H3FourierPoint3) :
    (∑ i : Fin 3, h3FourierDerivativeSymbol2 i i ξ)
      = -(h3FourierGradientSquare ξ : ℂ) := by
  calc
    (∑ i : Fin 3, h3FourierDerivativeSymbol2 i i ξ)
        =
      ∑ i : Fin 3,
        h3FourierDerivativeSymbol i ξ *
          h3FourierDerivativeSymbol i ξ := by
            rfl
    _ =
      ∑ i : Fin 3,
        -(star (h3FourierDerivativeSymbol i ξ) *
          h3FourierDerivativeSymbol i ξ) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hstar :
                star (h3FourierDerivativeSymbol i ξ)
                  = -h3FourierDerivativeSymbol i ξ := by
              exact conj_h3FourierDerivativeSymbol_eq_neg i ξ
            rw [hstar]
            ring
    _ =
      -(∑ i : Fin 3,
        star (h3FourierDerivativeSymbol i ξ) *
          h3FourierDerivativeSymbol i ξ) := by
            rw [Finset.sum_neg_distrib]
    _ = -(h3FourierGradientSquare ξ : ℂ) := by
          rw [sum_star_h3FourierDerivativeSymbol_mul_eq_gradientSquare]

/-! ## Genuine H³ snapshots -/

/-- For one velocity component of a Fourier-compatible H³ snapshot, the sum
    of the three concrete diagonal second-derivative Fourier slots is the
    expected Laplacian multiplier of the base Fourier field. -/
theorem velocityH3FourierCompatibleAt_laplacian_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    ∀ᵐ ξ ∂volume,
      (∑ i : Fin 3,
        velocityH3FourierJetAt u t hInt hMeas
          (h3JetSlot2 j i i) ξ)
        =
      -(h3FourierGradientSquare ξ : ℂ) *
        velocityH3BaseFourierAt u t hInt hMeas j ξ := by
  filter_upwards [
    velocityH3FourierCompatibleAt_orderTwo_all_ae hFourier j
  ] with ξ hξ
  calc
    (∑ i : Fin 3,
        velocityH3FourierJetAt u t hInt hMeas
          (h3JetSlot2 j i i) ξ)
        =
      ∑ i : Fin 3,
        h3FourierDerivativeSymbol2 i i ξ *
          velocityH3BaseFourierAt u t hInt hMeas j ξ := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hξ i i
    _ =
      (∑ i : Fin 3,
        h3FourierDerivativeSymbol2 i i ξ) *
          velocityH3BaseFourierAt u t hInt hMeas j ξ := by
            rw [Finset.sum_mul]
    _ =
      -(h3FourierGradientSquare ξ : ℂ) *
        velocityH3BaseFourierAt u t hInt hMeas j ξ := by
          rw [sum_h3FourierDerivativeSymbol2_diag_eq_neg_gradientSquare]

/-- The same diffusion multiplier identity after inserting the common H³
    Sobolev weight used by the spectral encoder. -/
theorem velocityH3WeightedFourierCompatibleAt_laplacian_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    ∀ᵐ ξ ∂volume,
      (h3SobolevFrequencyWeight ξ : ℂ) *
          (∑ i : Fin 3,
            velocityH3FourierJetAt u t hInt hMeas
              (h3JetSlot2 j i i) ξ)
        =
      -(h3FourierGradientSquare ξ : ℂ) *
        velocityH3WeightedBaseFourierRaw u t hInt hMeas j ξ := by
  filter_upwards [
    velocityH3FourierCompatibleAt_laplacian_ae hFourier j
  ] with ξ hξ
  rw [hξ]
  unfold velocityH3WeightedBaseFourierRaw
  ring

end

end Euclidean
end Bridge
end PrimeTensor

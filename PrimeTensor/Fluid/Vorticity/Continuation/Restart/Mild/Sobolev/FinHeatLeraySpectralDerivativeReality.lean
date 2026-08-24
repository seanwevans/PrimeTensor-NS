import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralConvolutionReality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.HeatDivergence

/-!
# Hermitian reality of the heat--derivative multiplier

The weighted product convolution has now been shown to preserve the exact
Fourier reality condition after Sobolev deweighting.  The next operation in
the finite heat--Leray kernel is one coordinate derivative followed by heat
flow.

Under Mathlib's Fourier convention the derivative symbol is

    d_j(ξ) = 2π i ξ_j.

It has precisely the Hermitian parity needed for real fields:

    d_j(-ξ) = conj (d_j(ξ)).

The heat symbol is real and even, so the combined heat--derivative symbol has
the same property.  This file lifts that scalar identity to Fourier `L²`, then
proves that exact H³ deweighting commutes with the heat--derivative operator.
Consequently one coordinate of the heat-smoothed divergence preserves the
packaged raw-Hermitian spectral condition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SpectralDerivativeReality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Scalar symbol parity -/

/-- The coordinate Fourier derivative symbol has Hermitian parity. -/
@[simp]
theorem h3FourierDerivativeSymbol_neg_eq_conj
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    h3FourierDerivativeSymbol j (-ξ)
      =
    conj (h3FourierDerivativeSymbol j ξ) := by
  unfold h3FourierDerivativeSymbol
  simp [RCLike.conj_ofNat]

/-- The heat--derivative symbol has the same Hermitian parity. -/
@[simp]
theorem h3HeatDerivativeSymbol_neg_eq_conj
    (ν t : ℝ)
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    h3HeatDerivativeSymbol ν t j (-ξ)
      =
    conj (h3HeatDerivativeSymbol ν t j ξ) := by
  unfold h3HeatDerivativeSymbol
  rw [h3FourierDerivativeSymbol_neg_eq_conj]
  rw [h3HeatFourierSymbol_neg]
  rw [map_mul, conj_h3HeatFourierSymbol]

/-- Multiplication by the heat--derivative symbol preserves one Hermitian
pointwise relation. -/
@[simp]
theorem h3HeatDerivativeSymbol_mul_conj
    (ν t : ℝ)
    (j : Fin 3)
    (ξ : H3FourierPoint3)
    (z : ℂ) :
    h3HeatDerivativeSymbol ν t j (-ξ) * conj z
      =
    conj (h3HeatDerivativeSymbol ν t j ξ * z) := by
  rw [h3HeatDerivativeSymbol_neg_eq_conj]
  rw [map_mul]

/-! ## Fourier L² preservation -/

/-- One coordinate derivative followed by heat flow preserves the ordinary
Fourier `L²` Hermitian condition. -/
theorem h3SpectralScalarHeatDerivativeApply_preserves_hermitian
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    {F : H3FourierComplexL2}
    (hF : H3FourierL2Hermitian F) :
    H3FourierL2Hermitian
      (h3SpectralScalarHeatDerivativeApply ν t hν ht j F) := by
  unfold H3FourierL2Hermitian at hF ⊢
  have hOut :=
    h3SpectralScalarHeatDerivativeApply_ae hν ht j F
  have hOutNeg := h3Fourier_ae_neg hOut
  filter_upwards [hOut, hOutNeg, hF] with ξ hAt hNeg hHerm
  rw [hNeg, hAt, hHerm]
  exact h3HeatDerivativeSymbol_mul_conj ν t j ξ (F ξ)

/-! ## Exact Sobolev deweighting intertwining -/

/-- Exact H³ deweighting commutes with one heat--derivative multiplier. -/
@[simp]
theorem h3SpectralScalarRawFourierL2_heatDerivativeApply
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (G : H3SpectralScalarState) :
    h3SpectralScalarRawFourierL2
        (h3SpectralScalarHeatDerivativeApply ν t hν ht j G)
      =
    h3SpectralScalarHeatDerivativeApply
      ν t hν ht j (h3SpectralScalarRawFourierL2 G) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawFourierL2_ae
      (h3SpectralScalarHeatDerivativeApply ν t hν ht j G),
    h3SpectralScalarHeatDerivativeApply_ae hν ht j G,
    h3SpectralScalarHeatDerivativeApply_ae
      hν ht j (h3SpectralScalarRawFourierL2 G),
    h3SpectralScalarRawFourierL2_ae G
  ] with ξ hRawOut hDerG hDerRaw hRawG
  rw [hRawOut, hDerRaw]
  unfold h3SpectralScalarRawFourier
  rw [hDerG, hRawG]
  unfold h3SpectralScalarRawFourier
  ac_rfl

/-- One weighted H³ heat--derivative coordinate preserves Hermitian reality
after exact Sobolev deweighting. -/
theorem h3SpectralScalarHeatDerivativeApply_preserves_rawHermitian
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G) :
    H3SpectralScalarRawHermitian
      (h3SpectralScalarHeatDerivativeApply ν t hν ht j G) := by
  unfold H3SpectralScalarRawHermitian at hG ⊢
  rw [h3SpectralScalarRawFourierL2_heatDerivativeApply]
  exact
    h3SpectralScalarHeatDerivativeApply_preserves_hermitian
      hν ht j hG

end

end Euclidean
end Bridge
end PrimeTensor

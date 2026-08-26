import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Derivative.Reality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Kernel

/-!
# Hermitian reality of the finite heat--Leray kernel

The analytic nonlinear step is already closed at the scalar level:

* exact weighted product convolution preserves deweighted Hermitian symmetry;
* one heat-smoothed Fourier derivative preserves it as well.

This file performs the remaining finite algebra.  First the three derivative
coordinates are summed to obtain reality preservation for the finite tensor
divergence.  Then the Fourier Leray matrix is shown to have the same Hermitian
parity entrywise.  Exact Sobolev deweighting commutes with each Leray entry, so
the finite matrix sum preserves the packaged raw-Hermitian condition.

The final theorem states that the genuine instantaneous finite heat--Leray
velocity kernel

    P e^{νtΔ} div (U ⊗ V)

preserves the exact Fourier reality invariant carried by the Picard scheme.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SpectralLerayReality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Finite sums of raw-Hermitian scalar states -/

/-- A finite sum of raw-Hermitian weighted scalar states is raw-Hermitian. -/
theorem h3SpectralScalarRawHermitian_sum
    {ι : Type*}
    (s : Finset ι)
    (F : ι → H3SpectralScalarState)
    (hF : ∀ i ∈ s, H3SpectralScalarRawHermitian (F i)) :
    H3SpectralScalarRawHermitian
      (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using h3SpectralScalarRawHermitian_zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact
        (hF a (Finset.mem_insert_self a s)).add
          (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

/-! ## Heat-divergence reality -/

/-- Finite heat-divergence of a raw-Hermitian tensor is a raw-Hermitian
velocity state. -/
theorem h3SpectralFinTensorHeatDivergenceApply_preserves_rawHermitian
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    {T : H3SpectralFinTensorState}
    (hT : H3SpectralFinTensorRawHermitian T) :
    H3SpectralVelocityRawHermitian
      (h3SpectralFinTensorHeatDivergenceApply ν t hν ht T) := by
  intro i
  unfold h3SpectralFinTensorHeatDivergenceApply
  apply h3SpectralScalarRawHermitian_sum
  intro j hj
  exact
    h3SpectralScalarHeatDerivativeApply_preserves_rawHermitian
      hν ht j (hT i j)

/-- The pre-Leray velocity kernel preserves raw-Hermitian reality. -/
theorem h3SpectralFinVelocityHeatDivergenceApply_preserves_rawHermitian
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    {U V : H3SpectralFinVectorState}
    (hU : H3SpectralVelocityRawHermitian U)
    (hV : H3SpectralVelocityRawHermitian V) :
    H3SpectralVelocityRawHermitian
      (h3SpectralFinVelocityHeatDivergenceApply ν t hν ht U V) := by
  unfold h3SpectralFinVelocityHeatDivergenceApply
  exact
    h3SpectralFinTensorHeatDivergenceApply_preserves_rawHermitian
      hν ht
      (h3SpectralFinOuterProduct_preserves_rawHermitian hU hV)

/-! ## Leray symbol parity -/

/-- The gradient-square denominator is even under frequency reflection. -/
@[simp]
theorem h3FourierGradientSquare_neg
    (ξ : H3FourierPoint3) :
    h3FourierGradientSquare (-ξ) = h3FourierGradientSquare ξ := by
  simp [h3FourierGradientSquare]

/-- The Kronecker-delta part of the Leray matrix is fixed by conjugation. -/
@[simp]
theorem conj_h3LerayDelta
    (i j : Fin 3) :
    conj (h3LerayDelta i j) = h3LerayDelta i j := by
  by_cases hij : i = j
  · simp [h3LerayDelta, hij]
  · simp [h3LerayDelta, hij]

/-- The rank-one part of the Leray symbol has Hermitian parity. -/
@[simp]
theorem h3LerayRankOneCoefficient_neg_eq_conj
    (ξ : H3FourierPoint3)
    (i j : Fin 3) :
    h3LerayRankOneCoefficient (-ξ) i j
      =
    conj (h3LerayRankOneCoefficient ξ i j) := by
  unfold h3LerayRankOneCoefficient
  rw [h3FourierGradientSquare_neg]
  by_cases hq : h3FourierGradientSquare ξ = 0
  · simp [hq]
  · simp only [dif_neg hq]
    rw [h3FourierDerivativeSymbol_neg_eq_conj,
      h3FourierDerivativeSymbol_neg_eq_conj]
    have hqstar :
        star (h3FourierGradientSquare ξ : ℂ) =
          (h3FourierGradientSquare ξ : ℂ) := by
      simpa only [starRingEnd_apply] using
        (Complex.conj_ofReal (h3FourierGradientSquare ξ))
    simp only [starRingEnd_apply]
    rw [star_div₀, star_mul', star_star, hqstar]

/-- Every finite Leray matrix entry has Hermitian parity. -/
@[simp]
theorem h3LerayCoefficient_neg_eq_conj
    (ξ : H3FourierPoint3)
    (i j : Fin 3) :
    h3LerayCoefficient (-ξ) i j
      =
    conj (h3LerayCoefficient ξ i j) := by
  unfold h3LerayCoefficient
  rw [h3LerayRankOneCoefficient_neg_eq_conj]
  rw [map_sub, conj_h3LerayDelta]

/-- Multiplication by one Leray matrix entry preserves one Hermitian pointwise
relation. -/
@[simp]
theorem h3LerayCoefficient_mul_conj
    (ξ : H3FourierPoint3)
    (i j : Fin 3)
    (z : ℂ) :
    h3LerayCoefficient (-ξ) i j * conj z
      =
    conj (h3LerayCoefficient ξ i j * z) := by
  rw [h3LerayCoefficient_neg_eq_conj]
  rw [map_mul]

/-! ## Leray multiplier on Fourier L² -/

/-- One Leray matrix entry preserves ordinary Fourier `L²` Hermitian
symmetry. -/
theorem h3SpectralScalarLerayCoefficientApply_preserves_hermitian
    (i j : Fin 3)
    {F : H3FourierComplexL2}
    (hF : H3FourierL2Hermitian F) :
    H3FourierL2Hermitian
      (h3SpectralScalarLerayCoefficientApply i j F) := by
  unfold H3FourierL2Hermitian at hF ⊢
  have hOut := h3SpectralScalarLerayCoefficientApply_ae i j F
  have hOutNeg := h3Fourier_ae_neg hOut
  filter_upwards [hOut, hOutNeg, hF] with ξ hAt hNeg hHerm
  rw [hNeg, hAt, hHerm]
  exact h3LerayCoefficient_mul_conj ξ i j (F ξ)

/-- Exact H³ deweighting commutes with one Leray matrix-entry multiplier. -/
@[simp]
theorem h3SpectralScalarRawFourierL2_lerayCoefficientApply
    (i j : Fin 3)
    (G : H3SpectralScalarState) :
    h3SpectralScalarRawFourierL2
        (h3SpectralScalarLerayCoefficientApply i j G)
      =
    h3SpectralScalarLerayCoefficientApply
      i j (h3SpectralScalarRawFourierL2 G) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawFourierL2_ae
      (h3SpectralScalarLerayCoefficientApply i j G),
    h3SpectralScalarLerayCoefficientApply_ae i j G,
    h3SpectralScalarLerayCoefficientApply_ae
      i j (h3SpectralScalarRawFourierL2 G),
    h3SpectralScalarRawFourierL2_ae G
  ] with ξ hRawOut hLerayG hLerayRaw hRawG
  rw [hRawOut, hLerayRaw]
  unfold h3SpectralScalarRawFourier
  rw [hLerayG, hRawG]
  unfold h3SpectralScalarRawFourier
  ac_rfl

/-- One weighted H³ Leray matrix entry preserves deweighted Hermitian
reality. -/
theorem h3SpectralScalarLerayCoefficientApply_preserves_rawHermitian
    (i j : Fin 3)
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G) :
    H3SpectralScalarRawHermitian
      (h3SpectralScalarLerayCoefficientApply i j G) := by
  unfold H3SpectralScalarRawHermitian at hG ⊢
  rw [h3SpectralScalarRawFourierL2_lerayCoefficientApply]
  exact
    h3SpectralScalarLerayCoefficientApply_preserves_hermitian
      i j hG

/-- The full finite Leray projection preserves deweighted Hermitian reality. -/
theorem h3SpectralFinLerayApply_preserves_rawHermitian
    {G : H3SpectralFinVectorState}
    (hG : H3SpectralVelocityRawHermitian G) :
    H3SpectralVelocityRawHermitian
      (h3SpectralFinLerayApply G) := by
  intro i
  unfold h3SpectralFinLerayApply
  apply h3SpectralScalarRawHermitian_sum
  intro j hj
  exact
    h3SpectralScalarLerayCoefficientApply_preserves_rawHermitian
      i j (hG j)

/-! ## Full instantaneous heat--Leray kernel -/

/-- The genuine finite heat--Leray bilinear kernel preserves the exact
raw-Hermitian Fourier reality invariant. -/
theorem h3SpectralFinHeatLerayVelocityApply_preserves_rawHermitian
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    {U V : H3SpectralFinVectorState}
    (hU : H3SpectralVelocityRawHermitian U)
    (hV : H3SpectralVelocityRawHermitian V) :
    H3SpectralVelocityRawHermitian
      (h3SpectralFinHeatLerayVelocityApply ν t hν ht U V) := by
  unfold h3SpectralFinHeatLerayVelocityApply
  exact
    h3SpectralFinLerayApply_preserves_rawHermitian
      (h3SpectralFinVelocityHeatDivergenceApply_preserves_rawHermitian
        hν ht hU hV)

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.Incompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel

/-!
# Finite Leray projection produces divergence-free H³ states

`Encoded.Incompressibility` proves the complementary fixed-point statement:

    divergence-free G  ->  P G = G.

For the selected Navier--Stokes restart we also need the range statement:

    P G is divergence-free

for an arbitrary spectral vector `G`.  This is what propagates
incompressibility through every nonlinear heat--Leray anchor in the Duhamel
term.

The pointwise algebra is short.  Because

    dᵢ(ξ) = 2π i ξᵢ,

the rank-one coefficient

    dᵢ star(dⱼ) / q

is symmetric in `i,j`; hence the already-proved row identity

    Σⱼ Pᵢⱼ dⱼ = 0

also gives the column identity

    Σᵢ dᵢ Pᵢⱼ = 0.

We then lift that identity through the `Lp` Leray representative theorem.
Consequently both the instantaneous heat--Leray kernel and the retarded
Duhamel integrand are Fourier divergence-free.

No PDE or time-integration theorem is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Interval ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3FinLerayProjectionIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Symmetry of the finite Leray symbol -/

@[simp]
theorem h3LerayDelta_symm
    (i j : Fin 3) :
    h3LerayDelta i j = h3LerayDelta j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp [h3LerayDelta, hij, hji]

/-- The rank-one Fourier projector coefficient is symmetric. -/
theorem h3LerayRankOneCoefficient_symm
    (ξ : H3FourierPoint3)
    (i j : Fin 3) :
    h3LerayRankOneCoefficient ξ i j
      =
    h3LerayRankOneCoefficient ξ j i := by
  unfold h3LerayRankOneCoefficient
  by_cases hq : h3FourierGradientSquare ξ = 0
  · simp [hq]
  · simp only [dif_neg hq]

    have hi :
        star (h3FourierDerivativeSymbol i ξ)
          =
        -h3FourierDerivativeSymbol i ξ := by
      simpa only [starRingEnd_apply] using
        conj_h3FourierDerivativeSymbol_eq_neg i ξ

    have hj :
        star (h3FourierDerivativeSymbol j ξ)
          =
        -h3FourierDerivativeSymbol j ξ := by
      simpa only [starRingEnd_apply] using
        conj_h3FourierDerivativeSymbol_eq_neg j ξ

    rw [hi, hj]
    ring

/-- The full finite Leray matrix is symmetric. -/
theorem h3LerayCoefficient_symm
    (ξ : H3FourierPoint3)
    (i j : Fin 3) :
    h3LerayCoefficient ξ i j
      =
    h3LerayCoefficient ξ j i := by
  unfold h3LerayCoefficient
  rw [
    h3LerayDelta_symm,
    h3LerayRankOneCoefficient_symm
  ]

/-! ## Divergence annihilation -/

/-- Column form of Leray gradient annihilation:

    Σᵢ dᵢ Pᵢⱼ = 0.

The row form was already proved in `PDE.Algebra`; symmetry turns it into the
divergence identity required for the range of the projector. -/
theorem sum_derivativeSymbol_mul_h3LerayCoefficient_eq_zero
    (ξ : H3FourierPoint3)
    (j : Fin 3) :
    (∑ i : Fin 3,
      h3FourierDerivativeSymbol i ξ *
        h3LerayCoefficient ξ i j)
      =
    0 := by
  calc
    (∑ i : Fin 3,
      h3FourierDerivativeSymbol i ξ *
        h3LerayCoefficient ξ i j)
        =
      ∑ i : Fin 3,
        h3LerayCoefficient ξ j i *
          h3FourierDerivativeSymbol i ξ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [h3LerayCoefficient_symm ξ i j]
            ring
    _ = 0 :=
      sum_h3LerayCoefficient_mul_derivativeSymbol_eq_zero
        ξ j

/-- Every finite Fourier Leray projection is divergence-free, independently of
its input state. -/
theorem h3SpectralFinLerayApply_divergenceFree
    (G : H3SpectralFinVectorState) :
    H3SpectralFinDivergenceFree
      (h3SpectralFinLerayApply G) := by
  have h0 := h3SpectralFinLerayApply_ae G 0
  have h1 := h3SpectralFinLerayApply_ae G 1
  have h2 := h3SpectralFinLerayApply_ae G 2

  filter_upwards [h0, h1, h2] with ξ h0ξ h1ξ h2ξ

  have hc0 :=
    sum_derivativeSymbol_mul_h3LerayCoefficient_eq_zero ξ 0
  have hc1 :=
    sum_derivativeSymbol_mul_h3LerayCoefficient_eq_zero ξ 1
  have hc2 :=
    sum_derivativeSymbol_mul_h3LerayCoefficient_eq_zero ξ 2

  simp only [Fin.sum_univ_three] at hc0 hc1 hc2 ⊢
  rw [h0ξ, h1ξ, h2ξ]
  simp only [Fin.sum_univ_three]

  calc
    h3FourierDerivativeSymbol 0 ξ *
          (h3LerayCoefficient ξ 0 0 * (G 0 : H3FourierPoint3 → ℂ) ξ +
            h3LerayCoefficient ξ 0 1 * (G 1 : H3FourierPoint3 → ℂ) ξ +
            h3LerayCoefficient ξ 0 2 * (G 2 : H3FourierPoint3 → ℂ) ξ)
        +
        h3FourierDerivativeSymbol 1 ξ *
          (h3LerayCoefficient ξ 1 0 * (G 0 : H3FourierPoint3 → ℂ) ξ +
            h3LerayCoefficient ξ 1 1 * (G 1 : H3FourierPoint3 → ℂ) ξ +
            h3LerayCoefficient ξ 1 2 * (G 2 : H3FourierPoint3 → ℂ) ξ)
        +
        h3FourierDerivativeSymbol 2 ξ *
          (h3LerayCoefficient ξ 2 0 * (G 0 : H3FourierPoint3 → ℂ) ξ +
            h3LerayCoefficient ξ 2 1 * (G 1 : H3FourierPoint3 → ℂ) ξ +
            h3LerayCoefficient ξ 2 2 * (G 2 : H3FourierPoint3 → ℂ) ξ)
        =
      (h3FourierDerivativeSymbol 0 ξ * h3LerayCoefficient ξ 0 0 +
          h3FourierDerivativeSymbol 1 ξ * h3LerayCoefficient ξ 1 0 +
          h3FourierDerivativeSymbol 2 ξ * h3LerayCoefficient ξ 2 0) *
          (G 0 : H3FourierPoint3 → ℂ) ξ
        +
      (h3FourierDerivativeSymbol 0 ξ * h3LerayCoefficient ξ 0 1 +
          h3FourierDerivativeSymbol 1 ξ * h3LerayCoefficient ξ 1 1 +
          h3FourierDerivativeSymbol 2 ξ * h3LerayCoefficient ξ 2 1) *
          (G 1 : H3FourierPoint3 → ℂ) ξ
        +
      (h3FourierDerivativeSymbol 0 ξ * h3LerayCoefficient ξ 0 2 +
          h3FourierDerivativeSymbol 1 ξ * h3LerayCoefficient ξ 1 2 +
          h3FourierDerivativeSymbol 2 ξ * h3LerayCoefficient ξ 2 2) *
          (G 2 : H3FourierPoint3 → ℂ) ξ := by
            ring
    _ = 0 := by
      rw [hc0, hc1, hc2]
      simp

/-- The zero spectral vector is divergence-free. -/
theorem h3SpectralFinDivergenceFree_zero :
    H3SpectralFinDivergenceFree
      (0 : H3SpectralFinVectorState) := by
  filter_upwards with ξ
  simp [H3SpectralFinDivergenceFree]

/-- Every instantaneous nonlinear heat--Leray velocity kernel lies in the
Fourier divergence-free subspace. -/
theorem h3SpectralFinHeatLerayVelocityApply_divergenceFree
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState) :
    H3SpectralFinDivergenceFree
      (h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U V) := by
  unfold h3SpectralFinHeatLerayVelocityApply
  exact
    h3SpectralFinLerayApply_divergenceFree
      (h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U V)

/-- Therefore every retarded Duhamel integrand value is Fourier
divergence-free, including the zero endpoint convention. -/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_divergenceFree
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (s : ℝ) :
    H3SpectralFinDivergenceFree
      (h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U V s) := by
  by_cases hs : 0 < t - s
  · rw [
      h3SpectralFinHeatLerayDuhamelIntegrand,
      dif_pos hs
    ]
    exact
      h3SpectralFinHeatLerayVelocityApply_divergenceFree
        hν hs (U s) (V s)
  · rw [
      h3SpectralFinHeatLerayDuhamelIntegrand,
      dif_neg hs
    ]
    exact h3SpectralFinDivergenceFree_zero

end
end Euclidean
end Bridge
end PrimeTensor

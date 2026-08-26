import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.PDE.Algebra
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fourier.Compatibility

/-!
# Fourier incompressibility for the weighted H³ encoder

The finite Leray algebra proves pointwise that the Fourier Leray matrix fixes
any vector satisfying

    Σⱼ dⱼ(ξ) Uⱼ(ξ) = 0.

The actual H³ restart state is weighted: each velocity component stores

    Gⱼ(ξ) = W₃(ξ) * ûⱼ(ξ).

Because the same scalar weight multiplies every component, Fourier
divergence-freeness passes unchanged from the raw base transform to the
weighted encoder.  This file packages that fact at the `Lp` level and proves
that the lifted finite Leray multiplier is exactly the identity on every such
state.

The remaining PDE-facing obligation is now isolated cleanly: derive the raw
a.e. relation

    Σⱼ dⱼ(ξ) ûⱼ(ξ) = 0

from the classical preterminal incompressibility equation.  Once that is done,
no additional Leray/projection argument is required for encoded snapshots.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3FinLerayEncodedIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Abstract spectral divergence-free predicate -/

/-- A weighted three-component spectral state is Fourier divergence-free. -/
def H3SpectralFinDivergenceFree
    (G : H3SpectralFinVectorState) : Prop :=
  ∀ᵐ ξ ∂volume,
    (∑ j : Fin 3,
      h3FourierDerivativeSymbol j ξ *
        (G j : H3FourierPoint3 → ℂ) ξ) = 0

/-- The bundled finite Leray multiplier has the expected pointwise matrix
    representative almost everywhere. -/
theorem h3SpectralFinLerayApply_ae
    (G : H3SpectralFinVectorState)
    (i : Fin 3) :
    (h3SpectralFinLerayApply G i : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      ∑ j : Fin 3,
        h3LerayCoefficient ξ i j *
          (G j : H3FourierPoint3 → ℂ) ξ) := by
  let A0 : H3SpectralScalarState :=
    h3SpectralScalarLerayCoefficientApply i 0 (G 0)
  let A1 : H3SpectralScalarState :=
    h3SpectralScalarLerayCoefficientApply i 1 (G 1)
  let A2 : H3SpectralScalarState :=
    h3SpectralScalarLerayCoefficientApply i 2 (G 2)
  have h0 :=
    h3SpectralScalarLerayCoefficientApply_ae i 0 (G 0)
  have h1 :=
    h3SpectralScalarLerayCoefficientApply_ae i 1 (G 1)
  have h2 :=
    h3SpectralScalarLerayCoefficientApply_ae i 2 (G 2)
  have h01 := MeasureTheory.Lp.coeFn_add A0 A1
  have h012 := MeasureTheory.Lp.coeFn_add (A0 + A1) A2
  filter_upwards [h0, h1, h2, h01, h012] with ξ h0ξ h1ξ h2ξ h01ξ h012ξ
  unfold h3SpectralFinLerayApply
  simp only [Fin.sum_univ_three]
  change ((A0 + A1 + A2 : H3SpectralScalarState) : H3FourierPoint3 → ℂ) ξ = _
  rw [h012ξ]
  simp only [Pi.add_apply]
  rw [h01ξ]
  simp only [Pi.add_apply]
  change
    (A0 : H3FourierPoint3 → ℂ) ξ +
        (A1 : H3FourierPoint3 → ℂ) ξ +
        (A2 : H3FourierPoint3 → ℂ) ξ = _
  rw [h0ξ, h1ξ, h2ξ]

/-- The lifted Fourier Leray operator is exactly the identity on a bundled
    divergence-free spectral state. -/
theorem h3SpectralFinLerayApply_eq_of_divergenceFree
    {G : H3SpectralFinVectorState}
    (hG : H3SpectralFinDivergenceFree G) :
    h3SpectralFinLerayApply G = G := by
  funext i
  apply MeasureTheory.Lp.ext
  filter_upwards [h3SpectralFinLerayApply_ae G i, hG] with ξ hRep hDiv
  rw [hRep]
  exact
    sum_h3LerayCoefficient_mul_eq_of_divergenceFree
      ξ i
      (fun j => (G j : H3FourierPoint3 → ℂ) ξ)
      hDiv

/-! ## Raw incompressibility and the concrete H³ encoder -/

/-- The exact raw base-Fourier divergence-free relation at one H³ snapshot. -/
def VelocityH3BaseFourierDivergenceFreeAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) : Prop :=
  ∀ᵐ ξ ∂volume,
    (∑ j : Fin 3,
      h3FourierDerivativeSymbol j ξ *
        velocityH3BaseFourierAt u t hInt hMeas j ξ) = 0

/-- Multiplying every raw Fourier velocity component by the common positive
    H³ weight preserves the divergence-free relation. -/
theorem velocityH3SpectralStateAt_divergenceFree_of_base
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hDiv : VelocityH3BaseFourierDivergenceFreeAt u t hInt hMeas) :
    H3SpectralFinDivergenceFree
      (velocityH3SpectralStateAt u t hInt hMeas hFourier) := by
  have hRepAll :
      ∀ᵐ ξ ∂volume,
        ∀ j : Fin 3,
          (velocityH3SpectralStateAt u t hInt hMeas hFourier j :
              H3FourierPoint3 → ℂ) ξ
            =
          velocityH3WeightedBaseFourierRaw
            u t hInt hMeas j ξ := by
    change
      {ξ : H3FourierPoint3 |
        ∀ j : Fin 3,
          (velocityH3SpectralStateAt u t hInt hMeas hFourier j :
              H3FourierPoint3 → ℂ) ξ
            =
          velocityH3WeightedBaseFourierRaw
            u t hInt hMeas j ξ} ∈ ae volume
    rw [show
      {ξ : H3FourierPoint3 |
        ∀ j : Fin 3,
          (velocityH3SpectralStateAt u t hInt hMeas hFourier j :
              H3FourierPoint3 → ℂ) ξ
            =
          velocityH3WeightedBaseFourierRaw
            u t hInt hMeas j ξ}
        =
      ⋂ j : Fin 3,
        {ξ : H3FourierPoint3 |
          (velocityH3SpectralStateAt u t hInt hMeas hFourier j :
              H3FourierPoint3 → ℂ) ξ
            =
          velocityH3WeightedBaseFourierRaw
            u t hInt hMeas j ξ} by
        ext ξ
        simp]
    exact
      Filter.iInter_mem.mpr
        (fun j => velocityH3SpectralScalarAt_ae hFourier j)

  filter_upwards [hDiv, hRepAll] with ξ hDivξ hRepξ
  calc
    (∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ *
          (velocityH3SpectralStateAt
            u t hInt hMeas hFourier j :
              H3FourierPoint3 → ℂ) ξ)
        =
      ∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ *
          ((h3SobolevFrequencyWeight ξ : ℂ) *
            velocityH3BaseFourierAt u t hInt hMeas j ξ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hRepξ j]
          rfl
    _ =
      (h3SobolevFrequencyWeight ξ : ℂ) *
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ *
            velocityH3BaseFourierAt u t hInt hMeas j ξ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = 0 := by
          rw [hDivξ, mul_zero]

/-- Therefore the finite Leray multiplier fixes every genuinely encoded H³
    snapshot as soon as its raw base Fourier transform is divergence-free. -/
theorem h3SpectralFinLerayApply_velocityH3SpectralStateAt_eq_of_base
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hDiv : VelocityH3BaseFourierDivergenceFreeAt u t hInt hMeas) :
    h3SpectralFinLerayApply
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
      =
    velocityH3SpectralStateAt u t hInt hMeas hFourier := by
  exact
    h3SpectralFinLerayApply_eq_of_divergenceFree
      (velocityH3SpectralStateAt_divergenceFree_of_base
        hFourier hDiv)

end

end Euclidean
end Bridge
end PrimeTensor

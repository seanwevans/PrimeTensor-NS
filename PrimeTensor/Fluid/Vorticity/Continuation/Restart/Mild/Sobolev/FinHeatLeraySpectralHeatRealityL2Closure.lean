import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralHeatRealityL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Closed algebra of the H³ Fourier reality condition

The previous file lifts pointwise Hermitian symmetry to the actual complex
Fourier `L²` carrier and proves that spectral heat evolution preserves it.
For Picard iteration we also need two structural facts:

* the Hermitian states are closed under the additive operations used by the
  mild equation;
* the Hermitian states form a norm-closed subset of Fourier `L²`, so a Banach
  limit of Hermitian iterates is still Hermitian.

The second point is packaged by writing Hermitian symmetry as the fixed-point
condition between two continuous real-linear maps on `L²`: frequency
reflection and complex conjugation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SpectralHeatRealityL2Closure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Reflection and conjugation on Fourier L² -/

/-- Negation of the Euclidean Fourier variable preserves volume exactly. -/
theorem h3FourierNegMeasurePreserving :
    MeasurePreserving
      (fun ξ : H3FourierPoint3 => -ξ)
      volume
      volume := by
  simpa using
    (LinearIsometryEquiv.neg ℝ :
      H3FourierPoint3 ≃ₗᵢ[ℝ] H3FourierPoint3).measurePreserving

/-- Frequency reflection `F(ξ) ↦ F(-ξ)` as a continuous real-linear map on
complex Fourier `L²`. -/
noncomputable def h3FourierReflectL2L :
    H3FourierComplexL2 →L[ℝ] H3FourierComplexL2 :=
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ
      ℝ
      (fun ξ : H3FourierPoint3 => -ξ)
      h3FourierNegMeasurePreserving).toContinuousLinearMap

/-- Complex conjugation as a continuous real-linear map on complex Fourier
`L²`. -/
noncomputable def h3FourierConjL2L :
    H3FourierComplexL2 →L[ℝ] H3FourierComplexL2 :=
  ContinuousLinearMap.compLpL
    2 volume Complex.conjCLE.toContinuousLinearMap

/-- Canonical representative of frequency reflection. -/
theorem h3FourierReflectL2L_ae
    (F : H3FourierComplexL2) :
    (h3FourierReflectL2L F : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 => F (-ξ)) := by
  unfold h3FourierReflectL2L
  change
    (((MeasureTheory.Lp.compMeasurePreservingₗᵢ
        ℝ
        (fun ξ : H3FourierPoint3 => -ξ)
        h3FourierNegMeasurePreserving) F : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 => F (-ξ))
  simpa only [
    MeasureTheory.Lp.compMeasurePreservingₗᵢ_apply_coe,
    Function.comp_def
  ] using
    (MeasureTheory.AEEqFun.coeFn_compMeasurePreserving
      (↑F : H3FourierPoint3 →ₘ[volume] ℂ)
      h3FourierNegMeasurePreserving)

/-- Canonical representative of complex conjugation. -/
theorem h3FourierConjL2L_ae
    (F : H3FourierComplexL2) :
    (h3FourierConjL2L F : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 => conj (F ξ)) := by
  unfold h3FourierConjL2L
  change
    (((Complex.conjCLE.toContinuousLinearMap).compLp F : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 => conj (F ξ))
  exact Complex.conjCLE.toContinuousLinearMap.coeFn_compLp F

/-- The a.e. Hermitian condition is exactly equality of the reflected and
conjugated `L²` states. -/
theorem h3FourierL2Hermitian_iff_reflect_eq_conj
    (F : H3FourierComplexL2) :
    H3FourierL2Hermitian F
      ↔
    h3FourierReflectL2L F = h3FourierConjL2L F := by
  constructor
  · intro hF
    apply MeasureTheory.Lp.ext
    filter_upwards [
      h3FourierReflectL2L_ae F,
      h3FourierConjL2L_ae F,
      hF
    ] with ξ hReflect hConj hHerm
    rw [hReflect, hConj]
    exact hHerm
  · intro hEq
    unfold H3FourierL2Hermitian
    have hEqAe :
        (h3FourierReflectL2L F : H3FourierPoint3 → ℂ)
          =ᵐ[volume]
        (h3FourierConjL2L F : H3FourierPoint3 → ℂ) := by
      rw [hEq]
    filter_upwards [
      h3FourierReflectL2L_ae F,
      h3FourierConjL2L_ae F,
      hEqAe
    ] with ξ hReflect hConj hPointEq
    calc
      F (-ξ) = h3FourierReflectL2L F ξ := hReflect.symm
      _ = h3FourierConjL2L F ξ := hPointEq
      _ = conj (F ξ) := hConj

/-! ## Additive closure -/

@[simp]
theorem h3FourierL2Hermitian_zero :
    H3FourierL2Hermitian (0 : H3FourierComplexL2) := by
  rw [h3FourierL2Hermitian_iff_reflect_eq_conj]
  simp

 theorem H3FourierL2Hermitian.add
    {F G : H3FourierComplexL2}
    (hF : H3FourierL2Hermitian F)
    (hG : H3FourierL2Hermitian G) :
    H3FourierL2Hermitian (F + G) := by
  rw [h3FourierL2Hermitian_iff_reflect_eq_conj] at hF hG ⊢
  simp only [map_add]
  rw [hF, hG]

 theorem H3FourierL2Hermitian.neg
    {F : H3FourierComplexL2}
    (hF : H3FourierL2Hermitian F) :
    H3FourierL2Hermitian (-F) := by
  rw [h3FourierL2Hermitian_iff_reflect_eq_conj] at hF ⊢
  simp only [map_neg]
  rw [hF]

 theorem H3FourierL2Hermitian.sub
    {F G : H3FourierComplexL2}
    (hF : H3FourierL2Hermitian F)
    (hG : H3FourierL2Hermitian G) :
    H3FourierL2Hermitian (F - G) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

/-! ## Norm closedness -/

/-- Hermitian Fourier `L²` states form a norm-closed subset. -/
theorem isClosed_h3FourierL2Hermitian :
    IsClosed
      {F : H3FourierComplexL2 | H3FourierL2Hermitian F} := by
  have hClosed :
      IsClosed
        {F : H3FourierComplexL2 |
          h3FourierReflectL2L F = h3FourierConjL2L F} :=
    isClosed_eq
      h3FourierReflectL2L.continuous
      h3FourierConjL2L.continuous
  convert hClosed using 1
  ext F
  simp only [Set.mem_ofPred_eq]
  exact h3FourierL2Hermitian_iff_reflect_eq_conj F

/-- Any norm limit of eventually Hermitian Fourier `L²` states remains
Hermitian. -/
theorem h3FourierL2Hermitian_of_tendsto
    {ι : Type*}
    {l : Filter ι}
    [l.NeBot]
    {F : ι → H3FourierComplexL2}
    {G : H3FourierComplexL2}
    (hFG : Tendsto F l (nhds G))
    (hF : ∀ᶠ i in l, H3FourierL2Hermitian (F i)) :
    H3FourierL2Hermitian G := by
  exact isClosed_h3FourierL2Hermitian.mem_of_tendsto hFG hF

/-! ## Weighted spectral closure -/

@[simp]
theorem h3SpectralScalarRawHermitian_zero :
    H3SpectralScalarRawHermitian (0 : H3SpectralScalarState) := by
  unfold H3SpectralScalarRawHermitian
  rw [h3SpectralScalarRawFourierL2_zero]
  exact h3FourierL2Hermitian_zero

 theorem H3SpectralScalarRawHermitian.add
    {G H : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G)
    (hH : H3SpectralScalarRawHermitian H) :
    H3SpectralScalarRawHermitian (G + H) := by
  unfold H3SpectralScalarRawHermitian at hG hH ⊢
  rw [h3SpectralScalarRawFourierL2_add]
  exact hG.add hH

 theorem H3SpectralScalarRawHermitian.neg
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G) :
    H3SpectralScalarRawHermitian (-G) := by
  unfold H3SpectralScalarRawHermitian at hG ⊢
  rw [h3SpectralScalarRawFourierL2_neg]
  exact hG.neg

 theorem H3SpectralScalarRawHermitian.sub
    {G H : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G)
    (hH : H3SpectralScalarRawHermitian H) :
    H3SpectralScalarRawHermitian (G - H) := by
  simpa only [sub_eq_add_neg] using hG.add hH.neg

@[simp]
theorem h3SpectralVelocityRawHermitian_zero :
    H3SpectralVelocityRawHermitian (0 : H3SpectralVelocityState) := by
  intro j
  change H3SpectralScalarRawHermitian (0 : H3SpectralScalarState)
  exact h3SpectralScalarRawHermitian_zero

 theorem H3SpectralVelocityRawHermitian.add
    {U V : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRawHermitian U)
    (hV : H3SpectralVelocityRawHermitian V) :
    H3SpectralVelocityRawHermitian (U + V) := by
  intro j
  change H3SpectralScalarRawHermitian (U j + V j)
  exact (hU j).add (hV j)

 theorem H3SpectralVelocityRawHermitian.neg
    {U : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRawHermitian U) :
    H3SpectralVelocityRawHermitian (-U) := by
  intro j
  change H3SpectralScalarRawHermitian (-U j)
  exact (hU j).neg

 theorem H3SpectralVelocityRawHermitian.sub
    {U V : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRawHermitian U)
    (hV : H3SpectralVelocityRawHermitian V) :
    H3SpectralVelocityRawHermitian (U - V) := by
  simpa only [sub_eq_add_neg] using hU.add hV.neg

end

end Euclidean
end Bridge
end PrimeTensor

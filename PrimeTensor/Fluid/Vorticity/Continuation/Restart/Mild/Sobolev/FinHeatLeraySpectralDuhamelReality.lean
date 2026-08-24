import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralLerayReality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayDuhamelPath

/-!
# Hermitian reality of the finite heat--Leray Duhamel operator

The instantaneous finite heat--Leray kernel now preserves the exact
raw-Hermitian Fourier invariant.  This file lifts that statement through the
retarded Bochner interval integral.

A useful simplification occurs at the temporal boundary.  The H³ Sobolev
weight is positive, real, and even, so Hermitian symmetry of the exact
deweighted Fourier state is equivalent to Hermitian symmetry of the weighted
spectral `L²` state itself.  The latter is expressed by equality of the two
continuous real-linear maps already constructed in
`FinHeatLeraySpectralHeatRealityL2Closure`: frequency reflection and complex
conjugation.  Those maps commute directly with interval integration.

Thus no new interchange theorem for the deweighting operator is required.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SpectralDuhamelReality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Evenness and reality of the Sobolev weight -/

@[simp]
theorem h3SobolevFrequencyWeightSq_neg
    (ξ : H3FourierPoint3) :
    h3SobolevFrequencyWeightSq (-ξ) =
      h3SobolevFrequencyWeightSq ξ := by
  unfold h3SobolevFrequencyWeightSq
  rw [h3FourierGradientSquare_neg]

@[simp]
theorem h3SobolevFrequencyWeight_neg
    (ξ : H3FourierPoint3) :
    h3SobolevFrequencyWeight (-ξ) =
      h3SobolevFrequencyWeight ξ := by
  unfold h3SobolevFrequencyWeight
  rw [h3SobolevFrequencyWeightSq_neg]

@[simp]
theorem h3SobolevFrequencyWeightInv_neg
    (ξ : H3FourierPoint3) :
    h3SobolevFrequencyWeightInv (-ξ) =
      h3SobolevFrequencyWeightInv ξ := by
  unfold h3SobolevFrequencyWeightInv
  rw [h3SobolevFrequencyWeight_neg]

@[simp]
theorem conj_h3SobolevFrequencyWeight
    (ξ : H3FourierPoint3) :
    conj (h3SobolevFrequencyWeight ξ : ℂ) =
      (h3SobolevFrequencyWeight ξ : ℂ) := by
  exact Complex.conj_ofReal _

@[simp]
theorem conj_h3SobolevFrequencyWeightInv
    (ξ : H3FourierPoint3) :
    conj (h3SobolevFrequencyWeightInv ξ : ℂ) =
      (h3SobolevFrequencyWeightInv ξ : ℂ) := by
  exact Complex.conj_ofReal _

/-! ## Weighted and deweighted Hermitian symmetry agree -/

/-- Hermitian symmetry of the weighted spectral `L²` state itself. -/
def H3SpectralVelocityHermitian
    (U : H3SpectralVelocityState) : Prop :=
  ∀ j : Fin 3, H3FourierL2Hermitian (U j)

/-- Exact deweighted Hermitian symmetry implies Hermitian symmetry of the
weighted scalar spectral state. -/
theorem h3SpectralScalarRawHermitian_to_hermitian
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G) :
    H3FourierL2Hermitian G := by
  unfold H3SpectralScalarRawHermitian at hG
  unfold H3FourierL2Hermitian at hG ⊢
  have hRaw := h3SpectralScalarRawFourierL2_ae G
  have hRawNeg := h3Fourier_ae_neg hRaw
  filter_upwards [hG, hRaw, hRawNeg] with ξ hHerm hAt hNeg
  have hRawHerm :
      h3SpectralScalarRawFourier G (-ξ) =
        conj (h3SpectralScalarRawFourier G ξ) := by
    calc
      h3SpectralScalarRawFourier G (-ξ)
          = h3SpectralScalarRawFourierL2 G (-ξ) := hNeg.symm
      _ = conj (h3SpectralScalarRawFourierL2 G ξ) := hHerm
      _ = conj (h3SpectralScalarRawFourier G ξ) := by rw [hAt]
  calc
    G (-ξ)
        = (h3SobolevFrequencyWeight (-ξ) : ℂ) *
            h3SpectralScalarRawFourier G (-ξ) :=
      (h3SpectralScalarRawFourier_reweight_pointwise G (-ξ)).symm
    _ = (h3SobolevFrequencyWeight ξ : ℂ) *
            h3SpectralScalarRawFourier G (-ξ) := by
      rw [h3SobolevFrequencyWeight_neg]
    _ = (h3SobolevFrequencyWeight ξ : ℂ) *
            conj (h3SpectralScalarRawFourier G ξ) := by
      rw [hRawHerm]
    _ = conj
          ((h3SobolevFrequencyWeight ξ : ℂ) *
            h3SpectralScalarRawFourier G ξ) := by
      rw [map_mul, conj_h3SobolevFrequencyWeight]
    _ = conj (G ξ) := by
      rw [h3SpectralScalarRawFourier_reweight_pointwise]

/-- Hermitian symmetry of the weighted scalar spectral state implies exact
deweighted Hermitian symmetry. -/
theorem h3SpectralScalarHermitian_to_rawHermitian
    {G : H3SpectralScalarState}
    (hG : H3FourierL2Hermitian G) :
    H3SpectralScalarRawHermitian G := by
  unfold H3SpectralScalarRawHermitian
  unfold H3FourierL2Hermitian at hG ⊢
  have hRaw := h3SpectralScalarRawFourierL2_ae G
  have hRawNeg := h3Fourier_ae_neg hRaw
  filter_upwards [hG, hRaw, hRawNeg] with ξ hHerm hAt hNeg
  rw [hNeg, hAt]
  unfold
    h3SpectralScalarRawFourier
    h3SobolevFrequencyWeightInvComplex
  rw [h3SobolevFrequencyWeightInv_neg, hHerm]
  rw [map_mul, conj_h3SobolevFrequencyWeightInv]

/-- Coordinatewise conversion from the exact deweighted invariant to the
weighted Hermitian invariant. -/
theorem h3SpectralVelocityRawHermitian_to_hermitian
    {U : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRawHermitian U) :
    H3SpectralVelocityHermitian U := by
  intro j
  exact h3SpectralScalarRawHermitian_to_hermitian (hU j)

/-- Coordinatewise conversion back to the exact deweighted invariant. -/
theorem h3SpectralVelocityHermitian_to_rawHermitian
    {U : H3SpectralVelocityState}
    (hU : H3SpectralVelocityHermitian U) :
    H3SpectralVelocityRawHermitian U := by
  intro j
  exact h3SpectralScalarHermitian_to_rawHermitian (hU j)

/-! ## Interval integration preserves Hermitian symmetry -/

/-- A Bochner interval integral of weighted Hermitian velocity states remains
weighted Hermitian. -/
theorem h3SpectralVelocityHermitian_intervalIntegral
    {a b : ℝ}
    {F : ℝ → H3SpectralVelocityState}
    (hInt : IntervalIntegrable F volume a b)
    (hF :
      ∀ s ∈ Set.uIcc a b,
        H3SpectralVelocityHermitian (F s)) :
    H3SpectralVelocityHermitian
      (∫ s in a..b, F s) := by
  intro j
  rw [h3FourierL2Hermitian_iff_reflect_eq_conj]
  let Pj :
      H3SpectralVelocityState →L[ℝ] H3FourierComplexL2 :=
    ContinuousLinearMap.proj j
  let Rj :
      H3SpectralVelocityState →L[ℝ] H3FourierComplexL2 :=
    h3FourierReflectL2L.comp Pj
  let Cj :
      H3SpectralVelocityState →L[ℝ] H3FourierComplexL2 :=
    h3FourierConjL2L.comp Pj
  have hR := Rj.intervalIntegral_comp_comm hInt
  have hC := Cj.intervalIntegral_comp_comm hInt
  calc
    h3FourierReflectL2L ((∫ s in a..b, F s) j)
        = Rj (∫ s in a..b, F s) := by
          simp [Rj, Pj]
    _ = ∫ s in a..b, Rj (F s) := hR.symm
    _ = ∫ s in a..b, Cj (F s) := by
          apply intervalIntegral.integral_congr
          intro s hs
          simp only [Rj, Cj, Pj, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.proj_apply]
          exact
            (h3FourierL2Hermitian_iff_reflect_eq_conj (F s j)).1
              (hF s hs j)
    _ = Cj (∫ s in a..b, F s) := hC
    _ = h3FourierConjL2L ((∫ s in a..b, F s) j) := by
          simp [Cj, Pj]

/-- A Bochner interval integral of exact raw-Hermitian weighted states remains
raw-Hermitian. -/
theorem h3SpectralVelocityRawHermitian_intervalIntegral
    {a b : ℝ}
    {F : ℝ → H3SpectralVelocityState}
    (hInt : IntervalIntegrable F volume a b)
    (hF :
      ∀ s ∈ Set.uIcc a b,
        H3SpectralVelocityRawHermitian (F s)) :
    H3SpectralVelocityRawHermitian
      (∫ s in a..b, F s) := by
  apply h3SpectralVelocityHermitian_to_rawHermitian
  apply h3SpectralVelocityHermitian_intervalIntegral hInt
  intro s hs
  exact h3SpectralVelocityRawHermitian_to_hermitian (hF s hs)

/-! ## Retarded Duhamel reality -/

/-- Every retarded heat--Leray integrand slice preserves the exact reality
invariant when both input paths do. -/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_preserves_rawHermitian
    {ν t : ℝ}
    (hν : 0 < ν)
    {U V : ℝ → H3SpectralFinVectorState}
    (hU : ∀ s : ℝ, H3SpectralVelocityRawHermitian (U s))
    (hV : ∀ s : ℝ, H3SpectralVelocityRawHermitian (V s))
    (s : ℝ) :
    H3SpectralVelocityRawHermitian
      (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V s) := by
  unfold h3SpectralFinHeatLerayDuhamelIntegrand
  split_ifs with hs
  · exact
      h3SpectralFinHeatLerayVelocityApply_preserves_rawHermitian
        hν hs (hU s) (hV s)
  · exact h3SpectralVelocityRawHermitian_zero

/-- The genuine finite heat--Leray Duhamel interval integral preserves exact
raw-Hermitian reality. -/
theorem h3SpectralFinHeatLerayDuhamel_preserves_rawHermitian
    {ν t : ℝ}
    (hν : 0 < ν)
    {U V : ℝ → H3SpectralFinVectorState}
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume 0 t)
    (hU : ∀ s : ℝ, H3SpectralVelocityRawHermitian (U s))
    (hV : ∀ s : ℝ, H3SpectralVelocityRawHermitian (V s)) :
    H3SpectralVelocityRawHermitian
      (h3SpectralFinHeatLerayDuhamel ν t hν U V) := by
  unfold h3SpectralFinHeatLerayDuhamel
  apply h3SpectralVelocityRawHermitian_intervalIntegral hInt
  intro s _hs
  exact
    h3SpectralFinHeatLerayDuhamelIntegrand_preserves_rawHermitian
      hν hU hV s

/-- For the continuous bounded paths used by the normalized mild operator, the
Duhamel reality theorem needs no separate integrability argument. -/
theorem h3SpectralFinHeatLerayDuhamel_preserves_rawHermitian_of_continuous
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hUbound : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hVbound : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (hUreal : ∀ s : ℝ, H3SpectralVelocityRawHermitian (U s))
    (hVreal : ∀ s : ℝ, H3SpectralVelocityRawHermitian (V s)) :
    H3SpectralVelocityRawHermitian
      (h3SpectralFinHeatLerayDuhamel ν t hν U V) := by
  have hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume 0 t :=
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν ht hMU hMV U V
      hUcont hVcont
      (fun s _hs => hUbound s)
      (fun s _hs => hVbound s)
  exact
    h3SpectralFinHeatLerayDuhamel_preserves_rawHermitian
      hν hInt hUreal hVreal

/-- The normalized physical-time Duhamel path is raw-Hermitian at every time
whenever its two real-time input paths are. -/
theorem h3SpectralFinHeatLerayDuhamelPath_preserves_rawHermitian
    {ν τ MU MV : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hUbound : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hVbound : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (hUreal : ∀ s : ℝ, H3SpectralVelocityRawHermitian (U s))
    (hVreal : ∀ s : ℝ, H3SpectralVelocityRawHermitian (V s))
    (q : H3UnitTime) :
    H3SpectralVelocityRawHermitian
      (h3SpectralFinHeatLerayDuhamelPath
        hν hτ hMU hMV U V
        hUcont hVcont hUbound hVbound q) := by
  rw [h3SpectralFinHeatLerayDuhamelPath_apply]
  exact
    h3SpectralFinHeatLerayDuhamel_preserves_rawHermitian_of_continuous
      hν
      (h3PhysicalTimeNN τ hτ q).property
      hMU hMV U V
      hUcont hVcont hUbound hVbound hUreal hVreal

end

end Euclidean
end Bridge
end PrimeTensor

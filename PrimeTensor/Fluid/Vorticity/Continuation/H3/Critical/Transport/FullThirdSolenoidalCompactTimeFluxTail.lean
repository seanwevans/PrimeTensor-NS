import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalCompactTimeRadialTightness
import Mathlib.Tactic

/-!
# Compact strict-time uniformity of the complete H³ high-max Fourier flux

On a fixed compact time slab, strong H³ continuity yields two quantitative
facts about the actual weighted spectral path: (1) a common norm ceiling K,
(2) a common high-frequency radius with arbitrarily small Fourier tail.

For any time-indexed solenoidal Schwartz realization of that path with the
*same exact weighted Fourier representatives*, the previously proved global
high-max trilinear estimate gives a common radius for which the complete
complex sixth-power high-maximum flux is less than ε at EVERY time in the
slab. The trilinear field family is an explicit hypothesis: a jointly
chosen physical Schwartz realization across time is not silently assumed.

The radius depends on the compact slab. The terminal endpoint T is excluded.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology FourierTransform
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev PairV := V3 × V3

noncomputable local instance axisFintypeCompactTimeFluxTail244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- ABSTRACT STRICT-SLAB TRILINEAR TAIL: strong continuous spectral H³
paths and matching solenoidal Schwartz representatives have uniformly
vanishing complete high-maximum complex flux on compact time intervals.
The norm ceiling is derived from compactness rather than postulated. -/
theorem thirdFullSchwartzStrictSlab_highMaxFluxUniform244
    (U : ℝ → H3SpectralVelocityState)
    (v : ℝ → A3 → SchwartzMap V3 ℂ)
    (a b : ℝ)
    (hCont : ContinuousOn U (Set.Icc a b))
    (hDiv : ∀ t ∈ Set.Icc a b, ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v t j) x (h3FourierAxisDirection j) = 0)
    (hRep : ∀ t ∈ Set.Icc a b, ∀ j : A3,
      (U t (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          (𝓕 (v t j)) ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ t ∈ Set.Icc a b,
      ‖∫ z in thirdFullHighMaxSet244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 (v t) z
          ∂volume.prod volume‖ < ε := by
  obtain ⟨E₀, hE₀⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).exists_bound_of_continuousOn
      hCont
  let K : ℝ := max E₀ 0
  have hK : 0 ≤ K := le_max_right E₀ 0
  have hBound : ∀ t ∈ Set.Icc a b, ‖U t‖ ≤ K := by
    intro t ht
    exact (hE₀ t ht).trans (le_max_left E₀ 0)
  let B : ℝ := 1944 * h3SobolevFirstMomentDeweightingConstant * K
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity [h3SobolevFirstMomentDeweightingConstant_nonneg]
  let δ : ℝ := min 1 (ε / (1 + B))
  have hOneB : 0 < 1 + B := by linarith
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min_iff.mpr ⟨by norm_num, div_pos hε hOneB⟩
  have hδone : δ ≤ 1 := by
    dsimp only [δ]
    exact min_le_left 1 (ε / (1 + B))
  have hδepsilon : B * δ < ε := by
    have hδle : δ ≤ ε / (1 + B) := by
      dsimp only [δ]
      exact min_le_right 1 (ε / (1 + B))
    calc
      B * δ ≤ B * (ε / (1 + B)) :=
        mul_le_mul_of_nonneg_left hδle hB
      _ < (1 + B) * (ε / (1 + B)) :=
        mul_lt_mul_of_pos_right (by linarith) (div_pos hε hOneB)
      _ = ε := by
        rw [mul_comm (1 + B)]
        exact div_mul_cancel₀ ε hOneB.ne'
  have hCompact : IsCompact (U '' Set.Icc a b) :=
    isCompact_Icc.image_of_continuousOn hCont
  obtain ⟨R, hR⟩ :=
    thirdFullSpectralVelocityHighRadialApply_uniformOnCompact244
      _ hCompact δ hδ
  refine ⟨R, ?_⟩
  intro t ht
  have hTail :
      ‖thirdFullSpectralVelocityHighRadialApply244 R (U t)‖ < δ :=
    hR (U t) ⟨t, ht, rfl⟩
  have hNormNonneg : 0 ≤
      ‖thirdFullSpectralVelocityHighRadialApply244 R (U t)‖ :=
    norm_nonneg _
  have hNormOne :
      ‖thirdFullSpectralVelocityHighRadialApply244 R (U t)‖ ≤ 1 :=
    (le_of_lt hTail).trans hδone
  have hSquare :
      ‖thirdFullSpectralVelocityHighRadialApply244 R (U t)‖ ^ 2 ≤ δ := by
    have hAux :
        ‖thirdFullSpectralVelocityHighRadialApply244 R (U t)‖ ^ 2 ≤
          ‖thirdFullSpectralVelocityHighRadialApply244 R (U t)‖ := by
      have hMul := mul_le_mul_of_nonneg_left hNormOne hNormNonneg
      nlinarith only [hMul]
    exact hAux.trans (le_of_lt hTail)
  have hFlux := thirdFullWeightedSchwartz_highMaxIntegral_le244
    (v t) (hDiv t ht) (U t) (hRep t ht) K hK (hBound t ht) R
  calc
    ‖∫ z in thirdFullHighMaxSet244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 (v t) z
        ∂volume.prod volume‖ ≤
      B * ‖thirdFullSpectralVelocityHighRadialApply244 R (U t)‖ ^ 2 :=
        hFlux
    _ ≤ B * δ := mul_le_mul_of_nonneg_left hSquare hB
    _ < ε := hδepsilon

/-- Apply compact-time high-max flux control to the ACTUAL continuous
preterminal spectral H³ path. The matching family of solenoidal Schwartz
realizations is kept explicit, rather than manufactured from a fixed-time
density theorem with no joint-time selection guarantee. -/
theorem thirdFullPhysicalStrictSlab_highMaxFluxUniform244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < T)
    (v : ℝ → A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ t ∈ Set.Icc a b, ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v t j) x (h3FourierAxisDirection j) = 0)
    (hRep : ∀ t ∈ Set.Icc a b, ∀ j : A3,
      (h3AuditActualSpectralVelocityTotal hH3 t
          (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          (𝓕 (v t j)) ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ t ∈ Set.Icc a b,
      ‖∫ z in thirdFullHighMaxSet244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 (v t) z
          ∂volume.prod volume‖ < ε := by
  have hSubset : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hCont : ContinuousOn (h3AuditActualSpectralVelocityTotal hH3)
      (Set.Icc a b) :=
    (h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hSubset
  exact thirdFullSchwartzStrictSlab_highMaxFluxUniform244
    (h3AuditActualSpectralVelocityTotal hH3) v a b hCont hDiv hRep ε hε

end
end PrimeTensor.FirstMonomialTriad

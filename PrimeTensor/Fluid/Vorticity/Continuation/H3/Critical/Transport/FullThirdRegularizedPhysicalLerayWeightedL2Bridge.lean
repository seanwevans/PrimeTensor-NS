import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdFiniteAxisRegularizedLerayNumerator
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.Incompressibility
import Mathlib.Tactic

/-!
# Weighted L² representative of the actual regularized real Schwartz recovery

The previous file proved the *pointwise* identity between PrimeTensor's
Fin-three Leray matrix and its intrinsic-axis transverse numerator.  The
real solenoidal Schwartz construction, meanwhile, supplies the exact Fourier
transform of the regularized numerator for every smooth compact Hermitian
*pre-Leray* input.

This file joins them at the genuine H³ spectral `Lp` level. Its input spectral
representative is smooth and compact, but **its Leray projection is not assumed
smooth**.  All pointwise substitutions of `Lp` elements are made only on a
common full-measure set, using the established representative theorems.

The main identity is

  R_n(P G)_i(ξ) = W₃(ξ) * Fourier(realSchwartzRecovery(n, U)_i)(ξ)

almost everywhere, where G_i(ξ) = W₃(ξ) U_i(ξ). The regularization, finite
Leray projection and Fourier reconstruction share exactly the same multiplier.
A final theorem chooses support-flat even cutoffs for a moving sequence of
smooth Hermitian pre-Leray inputs and transfers convergence to the actual
physically divergence-free Schwartz fields.

The remaining unconditional construction is the deweighting and carrier
transport of the compact Hermitian weighted Schwartz inputs from the existing
density theorem into the smooth axis profiles `U` required below.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology PrimeTensor.Bridge.Euclidean
open scoped ENNReal BigOperators ContDiff SchwartzMap FourierTransform ComplexConjugate

noncomputable section
set_option maxHeartbeats 1800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev Freq244 := A3 → ℝ
private abbrev CPol244 := A3 → ℂ

noncomputable local instance axisFintypePhysicalLerayWeightedBridge244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Three scalar a.e. representative identities become one simultaneous
finite-index representative equality. No pointwise `Lp` equality is used. -/
theorem thirdFullHermitianWeightedInput_all_ae244
    (G : H3SpectralVelocityState) (U : Freq244 → CPol244)
    (hG : ∀ i : Fin 3,
      (G i : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          U (WithLp.ofLp ξ) (h3AxisOfFin3 i))) :
    ∀ᵐ ξ : V3 ∂volume,
      ∀ i : Fin 3, (G i : V3 → ℂ) ξ =
        (h3SobolevFrequencyWeight ξ : ℂ) *
          U (WithLp.ofLp ξ) (h3AxisOfFin3 i) := by
  filter_upwards [hG 0, hG 1, hG 2] with ξ h0 h1 h2
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- EXACT `Lp` bridge for one Fourier coordinate. The input `G` is the
smooth Hermitian *pre-Leray* weighted Fourier state. The projected state
`P G` need only be an `Lp` element; no Schwartz regularity of it is assumed.

The identity retains the true H³ Fourier weight and the exact finite-to-axis
component map. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_leray_weighted_L2_ae244
    (n : ℕ) (G : H3SpectralVelocityState)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hχone : ∀ ξ j, U ξ j ≠ 0 → χ ξ = 1)
    (hG : ∀ j : Fin 3,
      (G j : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          U (WithLp.ofLp ξ) (h3AxisOfFin3 j)))
    (i : Fin 3) :
    (h3FullThirdRadialRecoveryVelocity244 n (h3SpectralFinLerayApply G) i :
        V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
        𝓕 (h3SchwartzComplexify
          (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
            hχsmooth hχcompact hUsmooth (h3AxisOfFin3 i))) ξ) := by
  have hRad := MeasureTheory.MemLp.coeFn_toLp
    (h3FullThirdRadialRecoveryRaw_memLp244 n (h3SpectralFinLerayApply G i))
  have hLeray := h3SpectralFinLerayApply_ae G i
  have hGAll := thirdFullHermitianWeightedInput_all_ae244 G U hG
  filter_upwards [hRad, hLeray, hGAll] with ξ hRadAt hLerayAt hInput
  have hRadAt' :
      (h3FullThirdRadialRecoveryVelocity244 n
          (h3SpectralFinLerayApply G) i : V3 → ℂ) ξ =
        h3FullThirdRadialRecoveryRaw244 n
          (h3SpectralFinLerayApply G i) ξ := hRadAt
  rw [hRadAt']
  change (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) *
    (h3SpectralFinLerayApply G i : V3 → ℂ) ξ = _
  rw [hLerayAt]
  have hSum :
      (∑ j : Fin 3, h3LerayCoefficient ξ i j * (G j : V3 → ℂ) ξ) =
      ∑ j : Fin 3, h3LerayCoefficient ξ i j *
        ((h3SobolevFrequencyWeight ξ : ℂ) *
          U (WithLp.ofLp ξ) (h3AxisOfFin3 j)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hInput j]
  rw [hSum]
  have hFraction := h3FullThirdRegularizedFiniteLeray_axisFraction244 n ξ i
    (fun j : Fin 3 => (h3SobolevFrequencyWeight ξ : ℂ) *
      U (WithLp.ofLp ξ) (h3AxisOfFin3 j))
  simp only [h3AxisOfFin3_h3ClassicalizationFinOfAxis] at hFraction
  have hPhysical := thirdFullRegularizedPhysicalSchwartzAt_weighted_no_div244
    n χ U hχsmooth hχcompact hUsmooth
    hχeven hUherm hχone ξ (h3AxisOfFin3 i)
  exact hFraction.trans hPhysical.symm

/-- The *same physical Schwartz velocity* supplies all three components of
the regularized Leray-projected weighted-H³ state. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_leray_velocity_L2_ae244
    (n : ℕ) (G : H3SpectralVelocityState)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hχone : ∀ ξ j, U ξ j ≠ 0 → χ ξ = 1)
    (hG : ∀ j : Fin 3,
      (G j : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          U (WithLp.ofLp ξ) (h3AxisOfFin3 j))) :
    ∀ i : Fin 3,
    (h3FullThirdRadialRecoveryVelocity244 n (h3SpectralFinLerayApply G) i :
        V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
        𝓕 (h3SchwartzComplexify
          (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
            hχsmooth hχcompact hUsmooth (h3AxisOfFin3 i))) ξ) := by
  intro i
  exact thirdFullRegularizedPhysicalSchwartzAt_leray_weighted_L2_ae244
    n G χ U hχsmooth hχcompact hUsmooth hχeven hUherm hχone hG i

/-- Existence of a physical solenoidal Schwartz realization for an arbitrary
smooth *compact Hermitian pre-Leray representative*. Only the original
unprojected weighted spectral state has a smooth pointwise representative.
The cutoff is selected internally, with no external support-flatness premise. -/
theorem exists_thirdFullRegularizedPhysicalSchwartz_leray_L2_ae244
    (n : ℕ) (G : H3SpectralVelocityState)
    (U : Freq244 → CPol244)
    (hUcompact : HasCompactSupport U)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hG : ∀ j : Fin 3,
      (G j : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          U (WithLp.ofLp ξ) (h3AxisOfFin3 j))) :
    ∃ χ : Freq244 → ℝ,
      ∃ (hχsmooth : ContDiff ℝ ∞ χ),
      ∃ (hχcompact : HasCompactSupport χ),
        (∀ i : Fin 3,
          (h3FullThirdRadialRecoveryVelocity244 n
             (h3SpectralFinLerayApply G) i : V3 → ℂ) =ᵐ[volume]
           (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
             𝓕 (h3SchwartzComplexify
               (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
                 hχsmooth hχcompact hUsmooth (h3AxisOfFin3 i))) ξ)) ∧
        (∀ x : V3, ∑ j : A3,
          fderiv ℝ (h3SchwartzComplexify
            (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
              hχsmooth hχcompact hUsmooth j))
            x (h3FourierAxisDirection j) = 0) := by
  obtain ⟨χ, hχsmooth, hχcompact, hEven, hFlat⟩ :=
    exists_thirdFullAxisSupportFlatEvenCutoff244 U hUcompact
  exact ⟨χ, hχsmooth, hχcompact,
    thirdFullRegularizedPhysicalSchwartzAt_leray_velocity_L2_ae244
      n G χ U hχsmooth hχcompact hUsmooth hEven hUherm hFlat hG,
    thirdFullRegularizedPhysicalSchwartzAt_divergence244
      n χ U hχsmooth hχcompact hUsmooth⟩

/-- Physical Schwartz completion of a moving compact-Hermitian **pre-Leray**
sequence. Unlike the earlier assembly, there is no hypothesis that the
weighted state *after* Leray projection has a smooth Fourier representative.

Since Leray fixes the Fourier-divergence-free target, continuity of the bounded
Leray operator gives convergence of projected inputs, and uniform radial
contraction gives the diagonal limit in genuine weighted H³. -/
theorem exists_thirdFullPhysicalSchwartzMoving_lerayWeighted_completion244
    (target : H3SpectralVelocityState)
    (hTargetDiv : H3SpectralFinDivergenceFree target)
    (G : ℕ → H3SpectralVelocityState)
    (hGconverges : Tendsto G atTop (𝓝 target))
    (U : ℕ → Freq244 → CPol244)
    (hUcompact : ∀ n, HasCompactSupport (U n))
    (hUsmooth : ∀ n, ContDiff ℝ ∞ (U n))
    (hUherm : ∀ n, H3ComplexHermitianPolarizationProfile244 (U n))
    (hGweighted : ∀ n j,
      (G n j : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          U n (WithLp.ofLp ξ) (h3AxisOfFin3 j))) :
    ∃ χ : ℕ → Freq244 → ℝ,
      ∃ (hχsmooth : ∀ n, ContDiff ℝ ∞ (χ n)),
      ∃ (hχcompact : ∀ n, HasCompactSupport (χ n)),
        Tendsto (fun n =>
          h3FullThirdRadialRecoveryVelocity244 n
            (h3SpectralFinLerayApply (G n))) atTop (𝓝 target) ∧
        (∀ (n : ℕ) (i : Fin 3),
          (h3FullThirdRadialRecoveryVelocity244 n
            (h3SpectralFinLerayApply (G n)) i : V3 → ℂ) =ᵐ[volume]
            (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
              𝓕 (h3SchwartzComplexify
                (thirdFullRegularizedPhysicalSchwartzAt244 n (χ n) (U n)
                  (hχsmooth n) (hχcompact n) (hUsmooth n)
                  (h3AxisOfFin3 i))) ξ)) ∧
        (∀ (n : ℕ) (x : V3), ∑ j : A3,
          fderiv ℝ (h3SchwartzComplexify
            (thirdFullRegularizedPhysicalSchwartzAt244 n (χ n) (U n)
              (hχsmooth n) (hχcompact n) (hUsmooth n) j))
            x (h3FourierAxisDirection j) = 0) ∧
        Tendsto (fun n => h3SpectralVelocityDecodeRealL2
          (h3FullThirdRadialRecoveryVelocity244 n
            (h3SpectralFinLerayApply (G n)))) atTop
          (𝓝 (h3SpectralVelocityDecodeRealL2 target)) ∧
        CauchySeq (fun n =>
          h3FullThirdRadialRecoveryVelocity244 n
            (h3SpectralFinLerayApply (G n))) := by
  classical
  have hChoose (n : ℕ) :
      ∃ χ : Freq244 → ℝ,
        ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ ξ : Freq244, χ (fun j => -ξ j) = χ ξ) ∧
        (∀ ξ j, U n ξ j ≠ 0 → χ ξ = 1) :=
    exists_thirdFullAxisSupportFlatEvenCutoff244 (U n) (hUcompact n)
  choose χ hχsmooth hχcompact hχeven hχone using hChoose
  have hPconverges :
      Tendsto (fun n => h3SpectralFinLerayApply (G n))
        atTop (𝓝 target) := by
    have h := (continuous_h3SpectralFinLerayApply.tendsto target).comp
      hGconverges
    rw [h3SpectralFinLerayApply_eq_of_divergenceFree hTargetDiv] at h
    exact h
  have hLimit := h3FullThirdRadialRecoveryVelocity_moving_tendsto244
    target (fun n => h3SpectralFinLerayApply (G n)) hPconverges
  have hPhysical (n : ℕ) (i : Fin 3) :=
    thirdFullRegularizedPhysicalSchwartzAt_leray_weighted_L2_ae244
      n (G n) (χ n) (U n)
      (hχsmooth n) (hχcompact n) (hUsmooth n)
      (hχeven n) (hUherm n) (hχone n) (hGweighted n) i
  have hDiv (n : ℕ) :=
    thirdFullRegularizedPhysicalSchwartzAt_divergence244
      n (χ n) (U n) (hχsmooth n) (hχcompact n) (hUsmooth n)
  exact ⟨χ, hχsmooth, hχcompact, hLimit, hPhysical, hDiv,
    h3SpectralVelocityDecodeRealL2_tendsto_of_weighted244 hLimit,
    hLimit.cauchySeq⟩

end
end PrimeTensor.FirstMonomialTriad

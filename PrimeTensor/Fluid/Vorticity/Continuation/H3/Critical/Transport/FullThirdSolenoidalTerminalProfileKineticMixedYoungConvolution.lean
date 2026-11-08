import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticLowMaxMixedRadialBudget
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadIntegralBound
import Mathlib.Tactic

/-!
# Asymmetric mixed Fourier Young bound for the exact low-maximum sixth flux

The prior radius-six coefficient estimate leaves three genuine mixed complex
contraction budgets.  Their three polarization inputs need not coincide.
A measure-preserving triad rearrangement gives an asymmetric L2-L2-L1 bound
with *independent* outer Fourier amplitudes. This is not the diagonal
F(p) F(r) estimate; it is a genuine two-profile inequality.  A free positive
scaling makes the estimate useful as an L2 continuity mechanism.

The native mixed six-transfer contraction is then bounded on the literal
LowMax(R) carrier by 3*2*(R+1) times the product of the three complex
polarization amplitudes. Combining these statements yields a mixed Young
budget that can be inserted into the preceding signed three-term telescope.
No unjustified L2-L2-L2 bound on the full unbounded momentum plane is used.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev YM3 := H3FourierPoint3
private abbrev YPair := YM3 × YM3
private abbrev YA3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeKineticMixedYoung244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A genuinely MIXED L2-L2-L1 triad estimate. The two outer functions are
unrelated; the transform (p,r) -> (p,-p-r) is measure preserving. The
arithmetic mean of their squared L2 masses pays for their product.
This is the underlying asymmetric version of the existing diagonal
h3Triad_integral_norm_le_L2_L1 estimate. -/
theorem thirdFullKinetic_mixedYoung_quadratic244
    (S : Set YPair) (hS : MeasurableSet S)
    (K : YPair → ℝ) (F W H : YM3 → ℝ)
    (hK : Integrable K (volume.prod volume))
    (hF : Integrable (fun ξ => F ξ ^ 2) volume)
    (hW : Integrable (fun ξ => W ξ ^ 2) volume)
    (hH : Integrable H volume)
    (hH0 : ∀ ξ, 0 ≤ H ξ)
    (hBound : ∀ z ∈ S,
      K z ≤ F z.1 * W z.2 * H (-(z.1 + z.2))) :
    (∫ z in S, K z ∂volume.prod volume) ≤
      ((∫ ξ : YM3, F ξ ^ 2 ∂volume) +
        (∫ ξ : YM3, W ξ ^ 2 ∂volume)) / 2 *
        (∫ ξ : YM3, H ξ ∂volume) := by
  let μ : Measure YPair := volume.prod volume
  let f : YPair → ℝ := fun z => F z.1 ^ 2 * H (-(z.1 + z.2))
  let w : YPair → ℝ := fun z => W z.2 ^ 2 * H (-(z.1 + z.2))
  have hf : Integrable f μ :=
    h3Triad_square_middle_integrable F H hF hH
  have hw : Integrable w μ := by
    have hs := (h3Triad_square_middle_integrable W H hW hH).swap
    change Integrable
      (fun z : YPair => W z.2 ^ 2 * H (-(z.2 + z.1))) μ at hs
    simpa only [add_comm] using hs
  have hmajor : Integrable (fun z => (f z + w z) / 2) μ := by
    have h := (hf.add hw).const_mul (1 / (2 : ℝ))
    convert h using 1
    ext z
    dsimp only [f, w]
    simp only [Pi.add_apply]
    ring
  have hIndicator : Integrable (S.indicator K) μ := hK.indicator hS
  have hPoint (z : YPair) :
      S.indicator K z ≤ (f z + w z) / 2 := by
    have hHnonneg : 0 ≤ H (-(z.1 + z.2)) := hH0 _
    have hsquares : 2 * F z.1 * W z.2 ≤ F z.1 ^ 2 + W z.2 ^ 2 := by
      nlinarith only [sq_nonneg (F z.1 - W z.2)]
    have hside : F z.1 * W z.2 * H (-(z.1 + z.2)) ≤
        (f z + w z) / 2 := by
      have hprod := mul_le_mul_of_nonneg_right hsquares hHnonneg
      dsimp only [f, w]
      nlinarith only [hprod]
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
      exact (hBound z hz).trans hside
    · rw [Set.indicator_of_notMem hz]
      dsimp only [f, w]
      have hp : 0 ≤ F z.1 ^ 2 := sq_nonneg _
      have hw' : 0 ≤ W z.2 ^ 2 := sq_nonneg _
      positivity
  have hMono :
      (∫ z : YPair, S.indicator K z ∂μ) ≤
        ∫ z : YPair, (f z + w z) / 2 ∂μ :=
    integral_mono hIndicator hmajor hPoint
  have hSwap :
      (∫ z : YPair, w z ∂μ) =
        (∫ z : YPair, W z.1 ^ 2 * H (-(z.1 + z.2)) ∂μ) := by
    have hs := integral_prod_swap (μ := (volume : Measure YM3))
      (ν := (volume : Measure YM3))
      (fun z : YPair => W z.1 ^ 2 * H (-(z.1 + z.2)))
    change (∫ z : YPair, W z.2 ^ 2 * H (-(z.2 + z.1)) ∂μ) =
      (∫ z : YPair, W z.1 ^ 2 * H (-(z.1 + z.2)) ∂μ) at hs
    simpa only [w, add_comm] using hs
  have hfIntegral : (∫ z : YPair, f z ∂μ) =
      (∫ ξ : YM3, F ξ ^ 2 ∂volume) *
        (∫ ξ : YM3, H ξ ∂volume) :=
    h3Triad_square_middle_integral F H
  have hwIntegral : (∫ z : YPair, w z ∂μ) =
      (∫ ξ : YM3, W ξ ^ 2 ∂volume) *
        (∫ ξ : YM3, H ξ ∂volume) := by
    rw [hSwap]
    exact h3Triad_square_middle_integral W H
  calc
    (∫ z in S, K z ∂μ) =
        ∫ z : YPair, S.indicator K z ∂μ :=
      (integral_indicator hS).symm
    _ ≤ ∫ z : YPair, (f z + w z) / 2 ∂μ := hMono
    _ = (1 / 2 : ℝ) * ((∫ z : YPair, f z ∂μ) +
            (∫ z : YPair, w z ∂μ)) := by
      have hPointEq : (fun z : YPair => (f z + w z) / 2) =
          (fun z : YPair => (1 / 2 : ℝ) * (f z + w z)) := by
        funext z
        ring
      rw [hPointEq, integral_const_mul, integral_add hf hw]
    _ = _ := by rw [hfIntegral, hwIntegral]; ring

/-- Free reciprocal scaling of the TWO outer Fourier amplitudes. Unlike the
unscaled arithmetic-mean bound, this can detect a small outer L2 difference:
one may choose the scaling only after its size is known. No L2-L2-L2
inequality on an infinite-measure convolution plane is asserted. -/
theorem thirdFullKinetic_mixedYoung_scaled244
    (S : Set YPair) (hS : MeasurableSet S)
    (K : YPair → ℝ) (F W H : YM3 → ℝ)
    (hK : Integrable K (volume.prod volume))
    (hF : Integrable (fun ξ => F ξ ^ 2) volume)
    (hW : Integrable (fun ξ => W ξ ^ 2) volume)
    (hH : Integrable H volume)
    (hH0 : ∀ ξ, 0 ≤ H ξ)
    (hBound : ∀ z ∈ S,
      K z ≤ F z.1 * W z.2 * H (-(z.1 + z.2)))
    (scale : ℝ) (hscale : 0 < scale) :
    (∫ z in S, K z ∂volume.prod volume) ≤
      ((scale ^ 2 * (∫ ξ : YM3, F ξ ^ 2 ∂volume) +
        scale⁻¹ ^ 2 * (∫ ξ : YM3, W ξ ^ 2 ∂volume)) / 2) *
        (∫ ξ : YM3, H ξ ∂volume) := by
  let F' : YM3 → ℝ := fun ξ => scale * F ξ
  let W' : YM3 → ℝ := fun ξ => scale⁻¹ * W ξ
  have hF' : Integrable (fun ξ : YM3 => F' ξ ^ 2) volume := by
    have h := hF.const_mul (scale ^ 2)
    convert h using 1
    ext ξ
    dsimp only [F']
    ring
  have hW' : Integrable (fun ξ : YM3 => W' ξ ^ 2) volume := by
    have h := hW.const_mul (scale⁻¹ ^ 2)
    convert h using 1
    ext ξ
    dsimp only [W']
    ring
  have hBound' : ∀ z ∈ S,
      K z ≤ F' z.1 * W' z.2 * H (-(z.1 + z.2)) := by
    intro z hz
    have heq : F z.1 * W z.2 * H (-(z.1 + z.2)) =
        F' z.1 * W' z.2 * H (-(z.1 + z.2)) := by
      dsimp only [F', W']
      have hInv : scale * scale⁻¹ = 1 := mul_inv_cancel₀ hscale.ne'
      calc
        _ = (scale * scale⁻¹) *
              (F z.1 * W z.2 * H (-(z.1 + z.2))) := by
            rw [hInv]
            ring
        _ = _ := by ring
    exact (hBound z hz).trans_eq heq
  have hYoung := thirdFullKinetic_mixedYoung_quadratic244
    S hS K F' W' H hK hF' hW' hH hH0 hBound'
  have hFI : (∫ ξ : YM3, F' ξ ^ 2 ∂volume) =
      scale ^ 2 * (∫ ξ : YM3, F ξ ^ 2 ∂volume) := by
    have hEq : (fun ξ : YM3 => F' ξ ^ 2) =
        (fun ξ : YM3 => scale ^ 2 * F ξ ^ 2) := by
      funext ξ
      dsimp only [F']
      ring
    rw [hEq, integral_const_mul]
  have hWI : (∫ ξ : YM3, W' ξ ^ 2 ∂volume) =
      scale⁻¹ ^ 2 * (∫ ξ : YM3, W ξ ^ 2 ∂volume) := by
    have hEq : (fun ξ : YM3 => W' ξ ^ 2) =
        (fun ξ : YM3 => scale⁻¹ ^ 2 * W ξ ^ 2) := by
      funext ξ
      dsimp only [W']
      ring
    rw [hEq, integral_const_mul]
  rw [hFI, hWI] at hYoung
  exact hYoung

/-- The real amplitudes in the three independent polarization slots. -/
noncomputable def thirdFullKineticPolarAmplitude244
    (P : YM3 → YA3 → ℂ) (ξ : YM3) : ℝ :=
  h3TriadPolarizationNorm (P ξ)

theorem thirdFullKineticPolarAmplitude_nonneg244
    (P : YM3 → YA3 → ℂ) (ξ : YM3) :
    0 ≤ thirdFullKineticPolarAmplitude244 P ξ :=
  h3TriadPolarizationNorm_nonneg _

/-- All three native contractions have exactly one Fourier frequency in
the multiplier. On the literal LowMax(R) plane they cost at most 3*2(R+1)
times three potentially unrelated polarization amplitudes. -/
theorem thirdFullKinetic_lowMax_mixedBudget_le_amplitudes244
    (R : ℕ) (P Q W : YM3 → YA3 → ℂ)
    (z : YPair) (hz : z ∈ (thirdFullHighMaxSet244 R)ᶜ) :
    thirdFullKineticMixedPolarSixthBudget244 P Q W z ≤
      (3 * (2 * ((R : ℝ) + 1))) *
        (thirdFullKineticPolarAmplitude244 P z.1 *
          thirdFullKineticPolarAmplitude244 Q (-(z.1 + z.2)) *
          thirdFullKineticPolarAmplitude244 W z.2) := by
  let p : YA3 → ℝ := WithLp.ofLp z.1
  let q : YA3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
  let r : YA3 → ℝ := WithLp.ofLp z.2
  let A : YA3 → ℂ := P z.1
  let B : YA3 → ℂ := Q (-(z.1 + z.2))
  let C : YA3 → ℂ := W z.2
  let a : ℝ := h3TriadPolarizationNorm A
  let b : ℝ := h3TriadPolarizationNorm B
  let c : ℝ := h3TriadPolarizationNorm C
  let ρ : ℝ := 2 * ((R : ℝ) + 1)
  have ha : 0 ≤ a := h3TriadPolarizationNorm_nonneg _
  have hb : 0 ≤ b := h3TriadPolarizationNorm_nonneg _
  have hc : 0 ≤ c := h3TriadPolarizationNorm_nonneg _
  have hπ : (1 : ℝ) ≤ 2 * Real.pi := by
    have h := Real.pi_gt_three
    linarith only [h]
  have hFreq (ξ : YM3)
      (hξ : h3FourierGradientMagnitude ξ < ρ) : ‖ξ‖ ≤ ρ := by
    calc
      ‖ξ‖ = (1 : ℝ) * ‖ξ‖ := by ring
      _ ≤ (2 * Real.pi) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right hπ (norm_nonneg ξ)
      _ ≤ ρ := hξ.le
  obtain ⟨_hp, hq, hr⟩ :=
    thirdFullKinetic_lowMax_allFrequenciesBelow244 R z hz
  have hqBound : frequencyNorm q ≤ ρ := by
    simpa only [frequencyNorm, q, WithLp.toLp_ofLp] using
      hFreq (-(z.1 + z.2)) hq
  have hrBound : frequencyNorm r ≤ ρ := by
    simpa only [frequencyNorm, r, WithLp.toLp_ofLp] using
      hFreq z.2 hr
  have hAC : ‖thirdFullComplexPolarizationDot244 A C‖ ≤ a * c := by
    simpa only [thirdFullComplexPolarizationDot244, amplitudeDot,
      a, c, h3TriadPolarizationNorm] using
      h3Triad_amplitudeDot_norm_le A C
  have hAB : ‖thirdFullComplexPolarizationDot244 A B‖ ≤ a * b := by
    simpa only [thirdFullComplexPolarizationDot244, amplitudeDot,
      a, b, h3TriadPolarizationNorm] using
      h3Triad_amplitudeDot_norm_le A B
  have hBC : ‖thirdFullComplexPolarizationDot244 B C‖ ≤ b * c := by
    simpa only [thirdFullComplexPolarizationDot244, amplitudeDot,
      b, c, h3TriadPolarizationNorm] using
      h3Triad_amplitudeDot_norm_le B C
  have hrB : ‖mixedDot r B‖ ≤ ρ * b := by
    have h := (mixedDot_norm_le_euclidean r B)
    have h0 : ‖mixedDot r B‖ ≤ frequencyNorm r * b := by
      simpa only [b, h3TriadPolarizationNorm, polarizationNorm] using h
    exact h0.trans (mul_le_mul_of_nonneg_right hrBound hb)
  have hqC : ‖mixedDot q C‖ ≤ ρ * c := by
    have h0 : ‖mixedDot q C‖ ≤ frequencyNorm q * c := by
      simpa only [c, h3TriadPolarizationNorm, polarizationNorm] using
        (mixedDot_norm_le_euclidean q C)
    exact h0.trans (mul_le_mul_of_nonneg_right hqBound hc)
  have hrA : ‖mixedDot r A‖ ≤ ρ * a := by
    have h0 : ‖mixedDot r A‖ ≤ frequencyNorm r * a := by
      simpa only [a, h3TriadPolarizationNorm, polarizationNorm] using
        (mixedDot_norm_le_euclidean r A)
    exact h0.trans (mul_le_mul_of_nonneg_right hrBound ha)
  have hX : ‖thirdFullComplexPolarizationDot244 A C * mixedDot r B‖ ≤
      (a * c) * (ρ * b) := by
    rw [norm_mul]
    exact mul_le_mul hAC hrB (norm_nonneg _)
      (mul_nonneg ha hc)
  have hY : ‖thirdFullComplexPolarizationDot244 A B * mixedDot q C‖ ≤
      (a * b) * (ρ * c) := by
    rw [norm_mul]
    exact mul_le_mul hAB hqC (norm_nonneg _)
      (mul_nonneg ha hb)
  have hZ : ‖thirdFullComplexPolarizationDot244 B C * mixedDot r A‖ ≤
      (b * c) * (ρ * a) := by
    rw [norm_mul]
    exact mul_le_mul hBC hrA (norm_nonneg _)
      (mul_nonneg hb hc)
  change ‖thirdFullComplexPolarizationDot244 A C * mixedDot r B‖ +
      ‖thirdFullComplexPolarizationDot244 A B * mixedDot q C‖ +
      ‖thirdFullComplexPolarizationDot244 B C * mixedDot r A‖ ≤
      (3 * ρ) * (a * b * c)
  calc
    _ ≤ (a * c) * (ρ * b) + (a * b) * (ρ * c) +
          (b * c) * (ρ * a) := add_le_add (add_le_add hX hY) hZ
    _ = _ := by ring

/-- TRUE mixed L2-L2-L1 estimate for the native low-maximum complex
contraction budget. The two outer amplitude squares need not coincide.
The middle amplitude is integrable; on genuine H3 Fourier states this is
supplied by deweighting, not by a false full-space L2-to-L1 implication.
The global budget integrability contract is stated explicitly. -/
theorem thirdFullKinetic_lowMax_mixedBudget_le_L2L2L1244
    (R : ℕ) (P Q W : YM3 → YA3 → ℂ)
    (hBudget : Integrable (thirdFullKineticMixedPolarSixthBudget244 P Q W)
      (volume.prod volume))
    (hP : Integrable (fun ξ : YM3 =>
      thirdFullKineticPolarAmplitude244 P ξ ^ 2) volume)
    (hW : Integrable (fun ξ : YM3 =>
      thirdFullKineticPolarAmplitude244 W ξ ^ 2) volume)
    (hQ : Integrable (thirdFullKineticPolarAmplitude244 Q) volume) :
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullKineticMixedPolarSixthBudget244 P Q W z ∂volume.prod volume) ≤
      (3 * (2 * ((R : ℝ) + 1))) *
        (((∫ ξ : YM3, thirdFullKineticPolarAmplitude244 P ξ ^ 2 ∂volume) +
          (∫ ξ : YM3, thirdFullKineticPolarAmplitude244 W ξ ^ 2 ∂volume)) /
          2 *
          (∫ ξ : YM3, thirdFullKineticPolarAmplitude244 Q ξ ∂volume)) := by
  let ρ : ℝ := 2 * ((R : ℝ) + 1)
  let F : YM3 → ℝ := thirdFullKineticPolarAmplitude244 P
  let W' : YM3 → ℝ := thirdFullKineticPolarAmplitude244 W
  let H : YM3 → ℝ := fun ξ => (3 * ρ) * thirdFullKineticPolarAmplitude244 Q ξ
  have hH : Integrable H volume := hQ.const_mul (3 * ρ)
  have hH0 (ξ : YM3) : 0 ≤ H ξ := by
    dsimp only [H, ρ]
    exact mul_nonneg (by positivity) (thirdFullKineticPolarAmplitude_nonneg244 Q ξ)
  have hBound (z : YPair) (hz : z ∈ (thirdFullHighMaxSet244 R)ᶜ) :
      thirdFullKineticMixedPolarSixthBudget244 P Q W z ≤
        F z.1 * W' z.2 * H (-(z.1 + z.2)) := by
    have hb := thirdFullKinetic_lowMax_mixedBudget_le_amplitudes244
      R P Q W z hz
    dsimp only [F, W', H, ρ]
    calc
      _ ≤ (3 * (2 * ((R : ℝ) + 1))) *
          (thirdFullKineticPolarAmplitude244 P z.1 *
            thirdFullKineticPolarAmplitude244 Q (-(z.1 + z.2)) *
            thirdFullKineticPolarAmplitude244 W z.2) := hb
      _ = _ := by ring
  have hYoung := thirdFullKinetic_mixedYoung_quadratic244
    ((thirdFullHighMaxSet244 R)ᶜ)
    (thirdFullHighMaxSet_measurable244 R).compl
    (thirdFullKineticMixedPolarSixthBudget244 P Q W)
    F W' H hBudget hP hW hH hH0 hBound
  have hHIntegral : (∫ ξ : YM3, H ξ ∂volume) =
      (3 * ρ) *
        (∫ ξ : YM3, thirdFullKineticPolarAmplitude244 Q ξ ∂volume) := by
    dsimp only [H]
    rw [integral_const_mul]
  calc
    _ ≤ ((∫ ξ : YM3, F ξ ^ 2 ∂volume) +
            (∫ ξ : YM3, W' ξ ^ 2 ∂volume)) / 2 *
            (∫ ξ : YM3, H ξ ∂volume) := hYoung
    _ = _ := by rw [hHIntegral]; dsimp only [F, W', ρ]; ring

/-- Reciprocal-scale mixed Young budget for the NATIVE three-channel complex
contraction. The scaling parameter can be chosen differently for each of
the three polarized difference terms; it is not a regularity hypothesis. -/
theorem thirdFullKinetic_lowMax_mixedBudget_scaled244
    (R : ℕ) (P Q W : YM3 → YA3 → ℂ)
    (hBudget : Integrable (thirdFullKineticMixedPolarSixthBudget244 P Q W)
      (volume.prod volume))
    (hP : Integrable (fun ξ : YM3 =>
      thirdFullKineticPolarAmplitude244 P ξ ^ 2) volume)
    (hW : Integrable (fun ξ : YM3 =>
      thirdFullKineticPolarAmplitude244 W ξ ^ 2) volume)
    (hQ : Integrable (thirdFullKineticPolarAmplitude244 Q) volume)
    (scale : ℝ) (hscale : 0 < scale) :
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullKineticMixedPolarSixthBudget244 P Q W z ∂volume.prod volume) ≤
      (3 * (2 * ((R : ℝ) + 1))) *
        (((scale ^ 2 * (∫ ξ : YM3,
              thirdFullKineticPolarAmplitude244 P ξ ^ 2 ∂volume) +
            scale⁻¹ ^ 2 * (∫ ξ : YM3,
              thirdFullKineticPolarAmplitude244 W ξ ^ 2 ∂volume)) / 2) *
          (∫ ξ : YM3, thirdFullKineticPolarAmplitude244 Q ξ ∂volume)) := by
  let ρ : ℝ := 2 * ((R : ℝ) + 1)
  let F : YM3 → ℝ := thirdFullKineticPolarAmplitude244 P
  let W' : YM3 → ℝ := thirdFullKineticPolarAmplitude244 W
  let H : YM3 → ℝ := fun ξ => (3 * ρ) * thirdFullKineticPolarAmplitude244 Q ξ
  have hH : Integrable H volume := hQ.const_mul (3 * ρ)
  have hH0 (ξ : YM3) : 0 ≤ H ξ := by
    dsimp only [H, ρ]
    exact mul_nonneg (by positivity) (thirdFullKineticPolarAmplitude_nonneg244 Q ξ)
  have hBound (z : YPair) (hz : z ∈ (thirdFullHighMaxSet244 R)ᶜ) :
      thirdFullKineticMixedPolarSixthBudget244 P Q W z ≤
        F z.1 * W' z.2 * H (-(z.1 + z.2)) := by
    have hb := thirdFullKinetic_lowMax_mixedBudget_le_amplitudes244 R P Q W z hz
    dsimp only [F, W', H, ρ]
    calc
      _ ≤ (3 * (2 * ((R : ℝ) + 1))) *
          (thirdFullKineticPolarAmplitude244 P z.1 *
            thirdFullKineticPolarAmplitude244 Q (-(z.1 + z.2)) *
            thirdFullKineticPolarAmplitude244 W z.2) := hb
      _ = _ := by ring
  have hYoung := thirdFullKinetic_mixedYoung_scaled244
    ((thirdFullHighMaxSet244 R)ᶜ)
    (thirdFullHighMaxSet_measurable244 R).compl
    (thirdFullKineticMixedPolarSixthBudget244 P Q W)
    F W' H hBudget hP hW hH hH0 hBound scale hscale
  have hHIntegral : (∫ ξ : YM3, H ξ ∂volume) =
      (3 * ρ) *
        (∫ ξ : YM3, thirdFullKineticPolarAmplitude244 Q ξ ∂volume) := by
    dsimp only [H]
    rw [integral_const_mul]
  calc
    _ ≤ ((scale ^ 2 * (∫ ξ : YM3, F ξ ^ 2 ∂volume) +
           scale⁻¹ ^ 2 * (∫ ξ : YM3, W' ξ ^ 2 ∂volume)) / 2) *
           (∫ ξ : YM3, H ξ ∂volume) := hYoung
    _ = _ := by rw [hHIntegral]; dsimp only [F, W', ρ]; ring


/-- Actual low-maximum MIXED SIXTH-POWER flux estimate. The radius-six
complex coefficient from the previous module and the radius-one mixed Young
contraction combine into an explicit seventh-order cutoff cost. The THREE
Fourier polarization profiles remain distinct; no signed phase is discarded
until the final norm bound. This is the missing per-mixed-term analytic
interface for the established signed polarization telescope. -/
theorem thirdFullKinetic_lowMax_mixedFlux_le_scaledL2L2L1244
    (R : ℕ) (P Q W : YM3 → YA3 → ℂ)
    (hFlux : IntegrableOn (thirdFullKineticMixedPolarSixthFlux244 P Q W)
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume))
    (hBudget : Integrable (thirdFullKineticMixedPolarSixthBudget244 P Q W)
      (volume.prod volume))
    (hP : Integrable (fun ξ : YM3 =>
      thirdFullKineticPolarAmplitude244 P ξ ^ 2) volume)
    (hW : Integrable (fun ξ : YM3 =>
      thirdFullKineticPolarAmplitude244 W ξ ^ 2) volume)
    (hQ : Integrable (thirdFullKineticPolarAmplitude244 Q) volume)
    (scale : ℝ) (hscale : 0 < scale) :
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      ‖thirdFullKineticMixedPolarSixthFlux244 P Q W z‖ ∂volume.prod volume) ≤
      (9 * (2 * ((R : ℝ) + 1)) ^ 7) *
        (((scale ^ 2 * (∫ ξ : YM3,
              thirdFullKineticPolarAmplitude244 P ξ ^ 2 ∂volume) +
            scale⁻¹ ^ 2 * (∫ ξ : YM3,
              thirdFullKineticPolarAmplitude244 W ξ ^ 2 ∂volume)) / 2) *
          (∫ ξ : YM3, thirdFullKineticPolarAmplitude244 Q ξ ∂volume)) := by
  let ρ : ℝ := 2 * ((R : ℝ) + 1)
  let L : ℝ :=
    ((scale ^ 2 * (∫ ξ : YM3, thirdFullKineticPolarAmplitude244 P ξ ^ 2 ∂volume) +
       scale⁻¹ ^ 2 * (∫ ξ : YM3,
         thirdFullKineticPolarAmplitude244 W ξ ^ 2 ∂volume)) / 2) *
      (∫ ξ : YM3, thirdFullKineticPolarAmplitude244 Q ξ ∂volume)
  have hCoefficient := thirdFullKinetic_lowMax_mixedIntegral_le_radiusBudget244
    R P Q W hFlux hBudget.integrableOn
  have hYoung := thirdFullKinetic_lowMax_mixedBudget_scaled244
    R P Q W hBudget hP hW hQ scale hscale
  change (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      ‖thirdFullKineticMixedPolarSixthFlux244 P Q W z‖ ∂volume.prod volume) ≤
      (9 * ρ ^ 7) * L
  calc
    _ ≤ (3 * ρ ^ 6) *
        (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
          thirdFullKineticMixedPolarSixthBudget244 P Q W z
            ∂volume.prod volume) := hCoefficient
    _ ≤ (3 * ρ ^ 6) * ((3 * ρ) * L) :=
      mul_le_mul_of_nonneg_left hYoung (by positivity)
    _ = (9 * ρ ^ 7) * L := by ring


end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdCompactHermitianSolenoidalSchwartz
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Compact.Density
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Heat.Reality.L2.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Duhamel.Reality
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Hermitian smooth compact density and real-solenoidal weighted H³ completion

A complex-weighted H³ Fourier state with the exact real-data Hermitian
involution is approximated in its actual L² norm by *Hermitian* smooth,
compact-frequency Schwartz functions. This fills the input-reality gap in
`FullThirdHermitianTransverseCutoff`.

The construction is a bounded REAL-linear symmetrization on Fourier L²:

    P F = (F + conj(F(-ξ))) / 2.

For a Hermitian target, P fixes the target. Applying P to a smooth compact
approximation preserves compact support and smoothness, and its normed
operator bound gives genuine quantitative density. Taking three components
and then applying the preexisting bounded spectral Leray projection gives
unconditional REAL-DECODEABLE, Fourier-divergence-free strong H³ density,
whenever the target is raw-Hermitian and Fourier divergence-free.

IMPORTANT: Leray projection here is still a weighted H³ L² state; even though
its pre-Leray input is Hermitian and smooth compact, the Leray output is not
claimed to possess a globally smooth Fourier Schwartz representative at
zero. A separate annular excision theorem is needed to connect this spectral
density to the exact physical solenoidal Schwartz construction.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology Set
open scoped ENNReal SchwartzMap ComplexConjugate ContDiff

noncomputable section
set_option maxHeartbeats 1200000

private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeHermitianCompactDensity244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The real-linear conjugate-reflection and Hermitian averaging operators -/

/-- Conjugate reflection is continuous and REAL-linear in Fourier L². -/
noncomputable def h3HermitianConjugateReflectCLM244 :
    H3SpectralScalarState →L[ℝ] H3SpectralScalarState :=
  h3FourierConjL2L.comp h3FourierReflectL2L

/-- The actual a.e. representative of conjugate reflection. -/
theorem h3HermitianConjugateReflectCLM_ae244
    (F : H3SpectralScalarState) :
    (h3HermitianConjugateReflectCLM244 F : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => conj (F (-ξ))) := by
  have hC := h3FourierConjL2L_ae (h3FourierReflectL2L F)
  have hR := h3FourierReflectL2L_ae F
  filter_upwards [hC, hR] with ξ hc hr
  change (h3FourierConjL2L (h3FourierReflectL2L F) : V3 → ℂ) ξ =
    conj ((F : V3 → ℂ) (-ξ))
  rw [hc, hr]

/-- Twice conjugating the genuine Fourier L² element gives itself. -/
theorem h3FourierConjL2L_involutive244
    (F : H3SpectralScalarState) :
    h3FourierConjL2L (h3FourierConjL2L F) = F := by
  apply MeasureTheory.Lp.ext
  have hC := h3FourierConjL2L_ae F
  have hCC := h3FourierConjL2L_ae (h3FourierConjL2L F)
  filter_upwards [hCC, hC] with ξ hcc hc
  rw [hcc, hc]
  simp

/-- The Hermitian projector is a bounded real-linear operator in the actual
weighted Fourier state. No complex-linearity is incorrectly assumed. -/
noncomputable def h3FourierHermitianAverageCLM244 :
    H3SpectralScalarState →L[ℝ] H3SpectralScalarState :=
  (1 / 2 : ℝ) •
    ((ContinuousLinearMap.id ℝ H3SpectralScalarState) +
      h3HermitianConjugateReflectCLM244)

@[simp]
theorem h3FourierHermitianAverageCLM_apply244
    (F : H3SpectralScalarState) :
    h3FourierHermitianAverageCLM244 F =
      (1 / 2 : ℝ) • (F + h3HermitianConjugateReflectCLM244 F) := by
  simp only [h3FourierHermitianAverageCLM244,
    smul_apply, add_apply, ContinuousLinearMap.id_apply]

/-- A Hermitian spectral target is fixed exactly by the averaging operator. -/
theorem h3FourierHermitianAverageCLM_fixed244
    (F : H3SpectralScalarState)
    (hF : H3FourierL2Hermitian F) :
    h3FourierHermitianAverageCLM244 F = F := by
  have hR : h3FourierReflectL2L F = h3FourierConjL2L F :=
    (h3FourierL2Hermitian_iff_reflect_eq_conj F).1 hF
  have hJ : h3HermitianConjugateReflectCLM244 F = F := by
    change h3FourierConjL2L (h3FourierReflectL2L F) = F
    rw [hR]
    exact h3FourierConjL2L_involutive244 F
  rw [h3FourierHermitianAverageCLM_apply244, hJ]
  calc
    (1 / 2 : ℝ) • (F + F) = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • F := by
      rw [smul_add, add_smul]
    _ = F := by norm_num

/-! ## Smooth compact averaging on genuine frequency functions -/

/-- Pointwise smooth compact Hermitian average of a complex Fourier profile. -/
noncomputable def h3HermitianSmoothCompactAverage244
    (g : V3 → ℂ) (ξ : V3) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) * (g ξ + conj (g (-ξ)))

/-- Conjugation and reflection preserve smoothness on the real Hilbert carrier. -/
theorem h3HermitianSmoothCompactAverage_contDiff244
    (g : V3 → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (h3HermitianSmoothCompactAverage244 g) := by
  have hNeg : ContDiff ℝ ∞ (fun ξ : V3 => g (-ξ)) :=
    hg.comp contDiff_id.neg
  have hConj : ContDiff ℝ ∞ (fun ξ : V3 => conj (g (-ξ))) := by
    have h := Complex.conjCLE.contDiff.comp hNeg
    simpa only [Function.comp_def, Complex.conjCLE_apply] using h
  change ContDiff ℝ ∞ (fun ξ : V3 =>
    ((1 / 2 : ℝ) : ℂ) * (g ξ + conj (g (-ξ))))
  exact contDiff_const.mul (hg.add hConj)

/-- The averaged profile is compactly supported whenever the original is. -/
theorem h3HermitianSmoothCompactAverage_hasCompactSupport244
    (g : V3 → ℂ) (hg : HasCompactSupport g) :
    HasCompactSupport (h3HermitianSmoothCompactAverage244 g) := by
  have hNeg : HasCompactSupport (fun ξ : V3 => g (-ξ)) := by
    simpa only [Function.comp_def, Homeomorph.coe_neg] using
      hg.comp_homeomorph (Homeomorph.neg V3)
  have hConj : HasCompactSupport (fun ξ : V3 => conj (g (-ξ))) := by
    have h := hNeg.comp_left
      (g := fun z : ℂ => conj z) (by simp)
    simpa only [Function.comp_def] using h
  have hSum := hg.add hConj
  have hScaled := hSum.comp_left
    (g := fun z : ℂ => ((1 / 2 : ℝ) : ℂ) * z) (by simp)
  change HasCompactSupport (fun ξ : V3 =>
    ((1 / 2 : ℝ) : ℂ) * (g ξ + conj (g (-ξ))))
  simpa only [Function.comp_def, Pi.add_apply] using hScaled

/-- Hermitian reality holds at EVERY frequency, including the origin. -/
theorem h3HermitianSmoothCompactAverage_reality244
    (g : V3 → ℂ) (ξ : V3) :
    h3HermitianSmoothCompactAverage244 g (-ξ) =
      conj (h3HermitianSmoothCompactAverage244 g ξ) := by
  unfold h3HermitianSmoothCompactAverage244
  simp only [neg_neg, map_mul, map_add, Complex.conj_ofReal,
    Complex.conj_conj]
  ring

/-- Smooth compact averaging represents the EXACT real-linear L² projector,
not merely a pointwise formal symmetrization. -/
theorem h3HermitianSmoothCompactAverage_toLp244
    (F : H3SpectralScalarState) (g : V3 → ℂ)
    (hFg : (F : V3 → ℂ) =ᵐ[volume] g)
    (hcompact : HasCompactSupport g) (hsmooth : ContDiff ℝ ∞ g) :
    h3FourierHermitianAverageCLM244 F =
      ((h3HermitianSmoothCompactAverage_hasCompactSupport244 g hcompact).toSchwartzMap
        (h3HermitianSmoothCompactAverage_contDiff244 g hsmooth)).toLp
        2 (volume : Measure V3) := by
  let S : SchwartzMap V3 ℂ :=
    (h3HermitianSmoothCompactAverage_hasCompactSupport244 g hcompact).toSchwartzMap
      (h3HermitianSmoothCompactAverage_contDiff244 g hsmooth)
  change h3FourierHermitianAverageCLM244 F = S.toLp 2 (volume : Measure V3)
  rw [h3FourierHermitianAverageCLM_apply244]
  apply MeasureTheory.Lp.ext
  have hSmul := MeasureTheory.Lp.coeFn_smul (1 / 2 : ℝ)
    (F + h3HermitianConjugateReflectCLM244 F)
  have hAdd := MeasureTheory.Lp.coeFn_add F
    (h3HermitianConjugateReflectCLM244 F)
  have hJ := h3HermitianConjugateReflectCLM_ae244 F
  have hFgNeg := h3Fourier_ae_neg hFg
  filter_upwards [hSmul, hAdd, hJ, hFg, hFgNeg,
    S.coeFn_toLp 2 (volume : Measure V3)]
    with ξ hs ha hj hf hfneg hS
  rw [hs]
  simp only [Pi.smul_apply]
  rw [ha]
  simp only [Pi.add_apply]
  rw [hj, hf, hfneg, hS]
  simp only [Complex.real_smul]
  rfl

/-! ## Quantitative Hermitian compact-smooth density -/

/-- A Hermitian weighted Fourier state has arbitrarily accurate genuinely
Hermitian and compact-frequency Schwartz representatives. The error is
controlled by the operator norm of the SAME bounded real-linear averaging. -/
theorem exists_h3HermitianSmoothCompactSpectralApprox244
    (F : H3SpectralScalarState)
    (hF : H3FourierL2Hermitian F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : SchwartzMap V3 ℂ,
      HasCompactSupport (S : V3 → ℂ) ∧
      (∀ ξ : V3, S (-ξ) = conj (S ξ)) ∧
      ‖F - S.toLp 2 (volume : Measure V3)‖ < ε := by
  let P := h3FourierHermitianAverageCLM244
  have hK : 0 < ‖P‖ + 1 := by positivity
  have hδ : 0 < ε / (‖P‖ + 1) := div_pos hε hK
  obtain ⟨G, ⟨g, hGg, hcompact, hsmooth⟩, hClose⟩ :=
    exists_h3SmoothCompact_spectralApprox_norm F hδ
  let S : SchwartzMap V3 ℂ :=
    (h3HermitianSmoothCompactAverage_hasCompactSupport244 g hcompact).toSchwartzMap
      (h3HermitianSmoothCompactAverage_contDiff244 g hsmooth)
  have hProjected : P G = S.toLp 2 (volume : Measure V3) := by
    exact h3HermitianSmoothCompactAverage_toLp244 G g hGg hcompact hsmooth
  have hFixed : P F = F := h3FourierHermitianAverageCLM_fixed244 F hF
  have hDiff : F - S.toLp 2 (volume : Measure V3) = P (F - G) := by
    rw [← hProjected, map_sub, hFixed]
  have hError : ‖F - S.toLp 2 (volume : Measure V3)‖ < ε := by
    calc
      ‖F - S.toLp 2 (volume : Measure V3)‖ = ‖P (F - G)‖ := by rw [hDiff]
      _ ≤ ‖P‖ * ‖F - G‖ := P.le_opNorm _
      _ ≤ (‖P‖ + 1) * ‖F - G‖ := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
          (norm_nonneg _)
      _ < (‖P‖ + 1) * (ε / (‖P‖ + 1)) :=
        mul_lt_mul_of_pos_left hClose hK
      _ = ε := by
        calc
          (‖P‖ + 1) * (ε / (‖P‖ + 1)) =
              (ε / (‖P‖ + 1)) * (‖P‖ + 1) := mul_comm _ _
          _ = ε := div_mul_cancel₀ ε (ne_of_gt hK)
  refine ⟨S, ?_, ?_, hError⟩
  · change HasCompactSupport (h3HermitianSmoothCompactAverage244 g)
    exact h3HermitianSmoothCompactAverage_hasCompactSupport244 g hcompact
  · intro ξ
    change h3HermitianSmoothCompactAverage244 g (-ξ) =
      conj (h3HermitianSmoothCompactAverage244 g ξ)
    exact h3HermitianSmoothCompactAverage_reality244 g ξ

/-- Componentwise compact-Hermitian Schwartz density for a real weighted
H³ velocity. No divergence hypothesis is needed until the Leray step. -/
theorem exists_h3HermitianSmoothCompactSpectralVelocityApprox244
    (U : H3SpectralVelocityState)
    (hU : H3SpectralVelocityRawHermitian U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : Fin 3 → SchwartzMap V3 ℂ,
      (∀ j, HasCompactSupport (Φ j : V3 → ℂ)) ∧
      H3SpectralVelocityRawHermitian
        (h3SchwartzSpectralVelocityRealization244 Φ) ∧
      ‖U - h3SchwartzSpectralVelocityRealization244 Φ‖ < ε := by
  have hHerm : H3SpectralVelocityHermitian U :=
    h3SpectralVelocityRawHermitian_to_hermitian hU
  have hSmall : 0 < ε / 2 := by positivity
  have hEach (j : Fin 3) :
      ∃ S : SchwartzMap V3 ℂ,
        HasCompactSupport (S : V3 → ℂ) ∧
        (∀ ξ, S (-ξ) = conj (S ξ)) ∧
        ‖U j - S.toLp 2 (volume : Measure V3)‖ < ε / 2 :=
    exists_h3HermitianSmoothCompactSpectralApprox244 (U j) (hHerm j) hSmall
  choose Φ hΦcompact hΦHerm hΦsmall using hEach
  have hInputHerm : H3SpectralVelocityHermitian
      (h3SchwartzSpectralVelocityRealization244 Φ) := by
    intro j
    change H3FourierL2Hermitian ((Φ j).toLp 2 (volume : Measure V3))
    unfold H3FourierL2Hermitian
    have hAt := (Φ j).coeFn_toLp 2 (volume : Measure V3)
    have hAtNeg := h3Fourier_ae_neg hAt
    filter_upwards [hAt, hAtNeg] with ξ ha han
    rw [han, ha]
    exact hΦHerm j ξ
  have hNorm : ‖U - h3SchwartzSpectralVelocityRealization244 Φ‖ ≤ ε / 2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    have hj := hΦsmall j
    simpa only [Pi.sub_apply, h3SchwartzSpectralVelocityRealization_apply244]
      using le_of_lt hj
  refine ⟨Φ, hΦcompact, h3SpectralVelocityHermitian_to_rawHermitian hInputHerm, ?_⟩
  exact lt_of_le_of_lt hNorm (by linarith)

/-- UNCONDITIONAL genuine weighted-H³ strong approximation of a real,
Fourier-divergence-free velocity by projected compact Hermitian Schwartz
inputs. Every image is solenoidal and exactly real-decodable in L².

This is NOT yet density by physical Schwartz fields: the frequency-dependent
Leray multiplier must first be regularized at the Fourier origin. -/
theorem exists_h3RealSolenoidalProjectedCompactSpectralApprox244
    (U : H3SpectralVelocityState)
    (hUdiv : H3SpectralFinDivergenceFree U)
    (hUreal : H3SpectralVelocityRawHermitian U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : Fin 3 → SchwartzMap V3 ℂ,
      (∀ j, HasCompactSupport (Φ j : V3 → ℂ)) ∧
      H3SpectralFinDivergenceFree (h3SchwartzSpectralLerayState244 Φ) ∧
      H3SpectralVelocityRawHermitian (h3SchwartzSpectralLerayState244 Φ) ∧
      H3SpectralVelocityRealizable (h3SchwartzSpectralLerayState244 Φ) ∧
      ‖U - h3SchwartzSpectralLerayState244 Φ‖ < ε := by
  have hSmall : 0 < ε / 12 := by positivity
  obtain ⟨Φ, hCompact, hInputReal, hInputClose⟩ :=
    exists_h3HermitianSmoothCompactSpectralVelocityApprox244 U hUreal hSmall
  obtain ⟨hDiv, hReal, hRealize⟩ :=
    h3SchwartzSpectralLerayState_realSolenoidal244 Φ hInputReal
  have hErr := h3SchwartzSpectralLerayState_error_le244 U hUdiv Φ
  have hStrict : 6 * ‖U - h3SchwartzSpectralVelocityRealization244 Φ‖ < ε := by
    have h := mul_lt_mul_of_pos_left hInputClose (by norm_num : (0 : ℝ) < 6)
    have hHalf : 6 * (ε / 12) < ε := by linarith
    exact lt_trans h hHalf
  exact ⟨Φ, hCompact, hDiv, hReal, hRealize, lt_of_le_of_lt hErr hStrict⟩


/-- A single chosen sequence of compact-Hermitian input Schwartz vectors
produces genuine real-decodable divergence-free projected spectral states
converging strongly and Cauchy in the weighted H³ carrier. No extra
Hermitian density hypothesis occurs in the theorem statement. -/
theorem exists_h3RealSolenoidalProjectedCompactSpectralSequence244
    (U : H3SpectralVelocityState)
    (hUdiv : H3SpectralFinDivergenceFree U)
    (hUreal : H3SpectralVelocityRawHermitian U) :
    ∃ Φ : ℕ → Fin 3 → SchwartzMap V3 ℂ,
      (∀ n j, HasCompactSupport (Φ n j : V3 → ℂ)) ∧
      (∀ n, H3SpectralFinDivergenceFree
        (h3SchwartzSpectralLerayState244 (Φ n))) ∧
      (∀ n, H3SpectralVelocityRawHermitian
        (h3SchwartzSpectralLerayState244 (Φ n))) ∧
      (∀ n, H3SpectralVelocityRealizable
        (h3SchwartzSpectralLerayState244 (Φ n))) ∧
      Tendsto (fun n => h3SchwartzSpectralLerayState244 (Φ n))
        atTop (𝓝 U) ∧
      CauchySeq (fun n => h3SchwartzSpectralLerayState244 (Φ n)) := by
  classical
  have hRadiusPos (n : ℕ) :
      0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  have hApprox (n : ℕ) :
      ∃ φ : Fin 3 → SchwartzMap V3 ℂ,
        (∀ j, HasCompactSupport (φ j : V3 → ℂ)) ∧
        H3SpectralFinDivergenceFree (h3SchwartzSpectralLerayState244 φ) ∧
        H3SpectralVelocityRawHermitian (h3SchwartzSpectralLerayState244 φ) ∧
        H3SpectralVelocityRealizable (h3SchwartzSpectralLerayState244 φ) ∧
        ‖U - h3SchwartzSpectralLerayState244 φ‖ <
          (1 : ℝ) / ((n : ℝ) + 1) :=
    exists_h3RealSolenoidalProjectedCompactSpectralApprox244
      U hUdiv hUreal (hRadiusPos n)
  choose Φ hCompact hDiv hRaw hReal hClose using hApprox
  have hRadiusTendsto :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hConverges :
      Tendsto (fun n => h3SchwartzSpectralLerayState244 (Φ n))
        atTop (𝓝 U) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hRadiusTendsto) ε hε
    refine ⟨N, ?_⟩
    intro n hn
    have hRadiusSmall :
        (1 : ℝ) / ((n : ℝ) + 1) < ε := by
      have h := hN n hn
      simpa only [Real.dist_eq, sub_zero, abs_of_pos (hRadiusPos n)] using h
    calc
      dist (h3SchwartzSpectralLerayState244 (Φ n)) U =
          ‖U - h3SchwartzSpectralLerayState244 (Φ n)‖ := by
        rw [dist_eq_norm, norm_sub_rev]
      _ < (1 : ℝ) / ((n : ℝ) + 1) := hClose n
      _ < ε := hRadiusSmall
  exact ⟨Φ, hCompact, hDiv, hRaw, hReal,
    hConverges, hConverges.cauchySeq⟩

end
end PrimeTensor.FirstMonomialTriad

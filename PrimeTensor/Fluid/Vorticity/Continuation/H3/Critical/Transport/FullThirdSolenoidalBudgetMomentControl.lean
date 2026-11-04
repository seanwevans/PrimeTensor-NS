import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalAnnularBudgetIntegrability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadSchwartzMoments
import Mathlib.Tactic

/-!
# A quantitative L²--L²--L¹ bound for the exact unsigned H³ Fourier flux budget

The three complex sixth-power flux contractions carry only ONE frequency
coordinate each. Their absolute-value budget is not an abstract Schwartz
seminorm: it is bounded by a real triad majorant of the form

  (F(p)² + F(q)²) H(r) + (F(p)² + F(r)²) H(q) / 2,

where q = -(p+r), F(ξ) is the Euclidean modulus of the genuine complex
Fourier velocity, and H(ξ) = |ξ| F(ξ).

The four separated square terms integrate to the SAME product because the
previously proved physical-frequency triad equivalences preserve product
Lebesgue measure. Thus

    totalUnsignedBudget(v) ≤ 3 (∫ F²) (∫ |ξ|F).

Both factors are genuinely finite for Schwartz data. Unlike the preceding
integrability result, this is a quantitative bound that can be made UNIFORM
along a density sequence whenever its Fourier mass and first moment have
uniform bounds. A final moving-annulus theorem proves vanishing of the
near-shell contribution under precisely those quantitative assumptions.

We do NOT assert that the physical H³ recovery sequence already satisfies
the required uniform moment bounds in this module. That bridge must use the
project's exact weighted H³ Fourier representative and deweighting theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev PairV := V3 × V3

noncomputable local instance axisFintypeBudgetMomentControl244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact scalar amplitude of the physical complex Fourier vector. -/
noncomputable def thirdFullBudgetMomentAmplitude244
    (v : A3 → SchwartzMap V3 ℂ) (ξ : V3) : ℝ :=
  h3TriadSpectralAmplitude v ξ

/-- First Fourier radial moment of the physical complex vector amplitude. -/
noncomputable def thirdFullBudgetFirstMoment244
    (v : A3 → SchwartzMap V3 ℂ) : ℝ :=
  ∫ ξ : V3, ‖ξ‖ * thirdFullBudgetMomentAmplitude244 v ξ
    ∂volume

/-- Unweighted Fourier L² mass of the same complex velocity. -/
noncomputable def thirdFullBudgetFourierMass244
    (v : A3 → SchwartzMap V3 ℂ) : ℝ :=
  ∫ ξ : V3, (thirdFullBudgetMomentAmplitude244 v ξ) ^ 2
    ∂volume

/-- Both exact moments are integrable for every Schwartz field. -/
theorem thirdFullBudgetMoments_integrable244
    (v : A3 → SchwartzMap V3 ℂ) :
    Integrable (fun ξ : V3 => (thirdFullBudgetMomentAmplitude244 v ξ) ^ 2)
      volume ∧
    Integrable (fun ξ : V3 => ‖ξ‖ * thirdFullBudgetMomentAmplitude244 v ξ)
      volume := by
  constructor
  · simpa only [thirdFullBudgetMomentAmplitude244, pow_zero, one_mul]
      using h3TriadSpectralAmplitude_integrable_pow_mul_sq v 0
  · simpa only [thirdFullBudgetMomentAmplitude244, pow_one]
      using h3TriadSpectralAmplitude_integrable_pow_mul v 1

/-- The moment factors are both nonnegative. -/
theorem thirdFullBudgetMoments_nonneg244
    (v : A3 → SchwartzMap V3 ℂ) :
    0 ≤ thirdFullBudgetFourierMass244 v ∧
      0 ≤ thirdFullBudgetFirstMoment244 v := by
  constructor
  · unfold thirdFullBudgetFourierMass244
    exact integral_nonneg (fun ξ => sq_nonneg _)
  · unfold thirdFullBudgetFirstMoment244
    exact integral_nonneg (fun ξ =>
      mul_nonneg (norm_nonneg ξ) (h3TriadSpectralAmplitude_nonneg v ξ))

/-- The full three-channel UNSIGNED contraction at a genuine complex Fourier
triad is bounded by two symmetric products carrying the first radial moment.
No incompressibility or Hermitian assumption is needed for this inequality. -/
theorem thirdFullSchwartzSixthFluxBudget_le_twoMomentProducts244
    (v : A3 → SchwartzMap V3 ℂ) (z : PairV) :
    let F := thirdFullBudgetMomentAmplitude244 v
    let H : V3 → ℝ := fun ξ => ‖ξ‖ * F ξ
    let q : V3 := -(z.1 + z.2)
    thirdFullSchwartzSixthFluxBudget244 v z ≤
      2 * (F z.1 * F q * H z.2) + F z.1 * F z.2 * H q := by
  let p : V3 := z.1
  let q : V3 := -(z.1 + z.2)
  let r : V3 := z.2
  let U := h3SchwartzTriadPolarization v
  let A : A3 → ℂ := U (WithLp.ofLp p)
  let B : A3 → ℂ := U (WithLp.ofLp q)
  let C : A3 → ℂ := U (WithLp.ofLp r)
  let F : V3 → ℝ := thirdFullBudgetMomentAmplitude244 v
  let H : V3 → ℝ := fun ξ => ‖ξ‖ * F ξ
  have hAC : ‖thirdFullComplexPolarizationDot244 A C‖ ≤ F p * F r := by
    simpa only [thirdFullComplexPolarizationDot244, amplitudeDot,
      F, thirdFullBudgetMomentAmplitude244, h3TriadSpectralAmplitude,
      A, C, U] using h3Triad_amplitudeDot_norm_le A C
  have hAB : ‖thirdFullComplexPolarizationDot244 A B‖ ≤ F p * F q := by
    simpa only [thirdFullComplexPolarizationDot244, amplitudeDot,
      F, thirdFullBudgetMomentAmplitude244, h3TriadSpectralAmplitude,
      A, B, U] using h3Triad_amplitudeDot_norm_le A B
  have hBC : ‖thirdFullComplexPolarizationDot244 B C‖ ≤ F q * F r := by
    simpa only [thirdFullComplexPolarizationDot244, amplitudeDot,
      F, thirdFullBudgetMomentAmplitude244, h3TriadSpectralAmplitude,
      B, C, U] using h3Triad_amplitudeDot_norm_le B C
  have hrB : ‖mixedDot (WithLp.ofLp r) B‖ ≤ ‖r‖ * F q := by
    simpa only [F, thirdFullBudgetMomentAmplitude244, h3TriadSpectralAmplitude,
      B, U] using h3Triad_mixedDot_norm_le r B
  have hqC : ‖mixedDot (WithLp.ofLp q) C‖ ≤ ‖q‖ * F r := by
    simpa only [F, thirdFullBudgetMomentAmplitude244, h3TriadSpectralAmplitude,
      C, U] using h3Triad_mixedDot_norm_le q C
  have hrA : ‖mixedDot (WithLp.ofLp r) A‖ ≤ ‖r‖ * F p := by
    simpa only [F, thirdFullBudgetMomentAmplitude244, h3TriadSpectralAmplitude,
      A, U] using h3Triad_mixedDot_norm_le r A
  have hX : ‖thirdFullComplexPolarizationDot244 A C * mixedDot (WithLp.ofLp r) B‖ ≤
      F p * F q * H r := by
    rw [norm_mul]
    calc
      _ ≤ (F p * F r) * (‖r‖ * F q) := by
        apply mul_le_mul hAC hrB
        · positivity
        · exact mul_nonneg (h3TriadSpectralAmplitude_nonneg v p)
            (h3TriadSpectralAmplitude_nonneg v r)
      _ = F p * F q * H r := by dsimp only [H]; ring
  have hY : ‖thirdFullComplexPolarizationDot244 A B * mixedDot (WithLp.ofLp q) C‖ ≤
      F p * F r * H q := by
    rw [norm_mul]
    calc
      _ ≤ (F p * F q) * (‖q‖ * F r) := by
        apply mul_le_mul hAB hqC
        · positivity
        · exact mul_nonneg (h3TriadSpectralAmplitude_nonneg v p)
            (h3TriadSpectralAmplitude_nonneg v q)
      _ = F p * F r * H q := by dsimp only [H]; ring
  have hZ : ‖thirdFullComplexPolarizationDot244 B C * mixedDot (WithLp.ofLp r) A‖ ≤
      F p * F q * H r := by
    rw [norm_mul]
    calc
      _ ≤ (F q * F r) * (‖r‖ * F p) := by
        apply mul_le_mul hBC hrA
        · positivity
        · exact mul_nonneg (h3TriadSpectralAmplitude_nonneg v q)
            (h3TriadSpectralAmplitude_nonneg v r)
      _ = F p * F q * H r := by dsimp only [H]; ring
  change ‖thirdFullComplexPolarizationDot244 A C *
        mixedDot (WithLp.ofLp r) B‖ +
      ‖thirdFullComplexPolarizationDot244 A B *
        mixedDot (WithLp.ofLp q) C‖ +
      ‖thirdFullComplexPolarizationDot244 B C *
        mixedDot (WithLp.ofLp r) A‖ ≤
      2 * (F p * F q * H r) + F p * F r * H q
  calc
    _ ≤ F p * F q * H r + F p * F r * H q +
          F p * F q * H r := add_le_add (add_le_add hX hY) hZ
    _ = _ := by ring

/-- A direct AM--GM majorant, suitable for separation into four product
integrals with exactly the old measure-preserving triad maps. -/
theorem thirdFullSchwartzSixthFluxBudget_le_squareMomentDensity244
    (v : A3 → SchwartzMap V3 ℂ) (z : PairV) :
    let F := thirdFullBudgetMomentAmplitude244 v
    let H : V3 → ℝ := fun ξ => ‖ξ‖ * F ξ
    let q : V3 := -(z.1 + z.2)
    thirdFullSchwartzSixthFluxBudget244 v z ≤
      (F z.1 ^ 2 + F q ^ 2) * H z.2 +
        ((F z.1 ^ 2 + F z.2 ^ 2) * H q) / 2 := by
  let F : V3 → ℝ := thirdFullBudgetMomentAmplitude244 v
  let H : V3 → ℝ := fun ξ => ‖ξ‖ * F ξ
  let q : V3 := -(z.1 + z.2)
  have hFz : 0 ≤ F z.1 := h3TriadSpectralAmplitude_nonneg v z.1
  have hFq : 0 ≤ F q := h3TriadSpectralAmplitude_nonneg v q
  have hFr : 0 ≤ F z.2 := h3TriadSpectralAmplitude_nonneg v z.2
  have hHr : 0 ≤ H z.2 := mul_nonneg (norm_nonneg _) hFr
  have hHq : 0 ≤ H q := mul_nonneg (norm_nonneg _) hFq
  have hSquareR : 2 * F z.1 * F q ≤ F z.1 ^ 2 + F q ^ 2 := by
    nlinarith [sq_nonneg (F z.1 - F q)]
  have hSquareQ : 2 * F z.1 * F z.2 ≤ F z.1 ^ 2 + F z.2 ^ 2 := by
    nlinarith [sq_nonneg (F z.1 - F z.2)]
  have hR := mul_le_mul_of_nonneg_right hSquareR hHr
  have hQ := mul_le_mul_of_nonneg_right hSquareQ hHq
  calc
    _ ≤ 2 * (F z.1 * F q * H z.2) + F z.1 * F z.2 * H q :=
      thirdFullSchwartzSixthFluxBudget_le_twoMomentProducts244 v z
    _ ≤ (F z.1 ^ 2 + F q ^ 2) * H z.2 +
        ((F z.1 ^ 2 + F z.2 ^ 2) * H q) / 2 := by
          nlinarith only [hR, hQ]

/-- In the old physical-frequency variables, the middle-frequency square
with outer-r moment is a measure-preserving reindexing of the outer-r square
with middle moment. This gives both L¹ and EXACT integral equality. -/
private theorem thirdFull_budget_middleSquare_outerMoment244
    (F H : V3 → ℝ)
    (hF : Integrable (fun ξ : V3 => F ξ ^ 2) volume)
    (hH : Integrable H volume) :
    Integrable (fun z : PairV => F (-(z.1 + z.2)) ^ 2 * H z.2)
        (volume.prod volume) ∧
      (∫ z : PairV, F (-(z.1 + z.2)) ^ 2 * H z.2
          ∂volume.prod volume) =
        (∫ ξ : V3, F ξ ^ 2 ∂volume) *
          ∫ ξ : V3, H ξ ∂volume := by
  have hBase := h3Triad_square_middle_integrable F H hF hH
  have hSwap : Integrable
      (fun z : PairV => F z.2 ^ 2 * H (-(z.1 + z.2)))
        (volume.prod volume) := by
    have hs := hBase.swap
    change Integrable
      (fun z : PairV => F z.2 ^ 2 * H (-(z.2 + z.1)))
        (volume.prod volume) at hs
    simpa only [add_comm] using hs
  let g : PairV → ℝ :=
    fun z => F z.2 ^ 2 * H (-(z.1 + z.2))
  have hTrans (z : PairV) :
      g (h3TriadMiddleEquiv z) =
        F (-(z.1 + z.2)) ^ 2 * H z.2 := by
    change F (-(z.1 + z.2)) ^ 2 *
      H (-(z.1 + -(z.1 + z.2))) = _
    rw [show -(z.1 + -(z.1 + z.2)) = z.2 by abel]
  have hComp : Integrable (g ∘ h3TriadMiddleEquiv)
      (volume.prod volume) :=
    (h3TriadMiddleEquiv_preserving.integrable_comp
      hSwap.aestronglyMeasurable).mpr hSwap
  constructor
  · exact hComp.congr (Filter.Eventually.of_forall hTrans)
  · calc
      (∫ z : PairV, F (-(z.1 + z.2)) ^ 2 * H z.2
          ∂volume.prod volume) =
        ∫ z : PairV, g (h3TriadMiddleEquiv z)
          ∂volume.prod volume := by
            apply integral_congr_ae
            filter_upwards with z
            exact (hTrans z).symm
      _ = ∫ z : PairV, g z ∂volume.prod volume :=
        h3TriadMiddleEquiv_preserving.integral_comp
          h3TriadMiddleEquiv.measurableEmbedding g
      _ = (∫ z : PairV, F z.1 ^ 2 * H (-(z.1 + z.2))
          ∂volume.prod volume) := by
            have hs := integral_prod_swap
              (μ := (volume : Measure V3)) (ν := (volume : Measure V3))
              (fun z : PairV => F z.1 ^ 2 * H (-(z.1 + z.2)))
            change (∫ z : PairV, F z.2 ^ 2 * H (-(z.2 + z.1))
              ∂volume.prod volume) =
                (∫ z : PairV, F z.1 ^ 2 * H (-(z.1 + z.2))
                  ∂volume.prod volume) at hs
            simpa only [g, add_comm] using hs
      _ = _ := h3Triad_square_middle_integral F H

/-- The exact L²--L²--L¹ estimate, without an arbitrary Schwartz seminorm.
Crucially, all FOUR separated integrals equal the same product of two
one-frequency Fourier moments. The constant is exactly 3. -/
theorem thirdFullSchwartzSixthFluxTotalBudget_le_L2FirstMoment244
    (v : A3 → SchwartzMap V3 ℂ) :
    thirdFullSchwartzSixthFluxTotalBudget244 v ≤
      3 * thirdFullBudgetFourierMass244 v * thirdFullBudgetFirstMoment244 v := by
  let F : V3 → ℝ := thirdFullBudgetMomentAmplitude244 v
  let H : V3 → ℝ := fun ξ => ‖ξ‖ * F ξ
  let μ : Measure PairV := volume.prod volume
  let G : PairV → ℝ := fun z => F z.1 ^ 2 * H z.2
  let J : PairV → ℝ := fun z => F (-(z.1 + z.2)) ^ 2 * H z.2
  let K : PairV → ℝ := fun z => F z.1 ^ 2 * H (-(z.1 + z.2))
  let N : PairV → ℝ := fun z => F z.2 ^ 2 * H (-(z.1 + z.2))
  let D : PairV → ℝ := fun z => G z + J z + (K z + N z) / 2
  have hF : Integrable (fun ξ : V3 => F ξ ^ 2) volume :=
    (thirdFullBudgetMoments_integrable244 v).1
  have hH : Integrable H volume :=
    (thirdFullBudgetMoments_integrable244 v).2
  have hG : Integrable G μ := hF.mul_prod hH
  have hK : Integrable K μ := h3Triad_square_middle_integrable F H hF hH
  have hN : Integrable N μ := by
    have hs := hK.swap
    change Integrable (fun z : PairV => F z.2 ^ 2 * H (-(z.2 + z.1))) μ at hs
    simpa only [N, add_comm] using hs
  obtain ⟨hJ, hJIntegral⟩ :=
    thirdFull_budget_middleSquare_outerMoment244 F H hF hH
  have hD : Integrable D μ := by
    have h := (hG.add hJ).add ((hK.add hN).const_mul (1 / (2 : ℝ)))
    apply h.congr
    filter_upwards with z
    change (G z + J z) + (1 / (2 : ℝ)) * (K z + N z) = D z
    dsimp only [D]
    ring
  have hPoint (z : PairV) :
      thirdFullSchwartzSixthFluxBudget244 v z ≤ D z := by
    calc
      _ ≤ (F z.1 ^ 2 + F (-(z.1 + z.2)) ^ 2) * H z.2 +
          ((F z.1 ^ 2 + F z.2 ^ 2) * H (-(z.1 + z.2))) / 2 :=
            thirdFullSchwartzSixthFluxBudget_le_squareMomentDensity244 v z
      _ = D z := by dsimp only [D, G, J, K, N]; ring
  have hGInt : (∫ z : PairV, G z ∂μ) =
      thirdFullBudgetFourierMass244 v * thirdFullBudgetFirstMoment244 v := by
    simpa only [G, F, H, thirdFullBudgetFourierMass244,
      thirdFullBudgetFirstMoment244] using
      (integral_prod_mul (μ := (volume : Measure V3))
        (ν := (volume : Measure V3)) (fun ξ : V3 => F ξ ^ 2) H)
  have hKInt : (∫ z : PairV, K z ∂μ) =
      thirdFullBudgetFourierMass244 v * thirdFullBudgetFirstMoment244 v := by
    simpa only [K, F, H, thirdFullBudgetFourierMass244,
      thirdFullBudgetFirstMoment244] using
      (h3Triad_square_middle_integral F H)
  have hNInt : (∫ z : PairV, N z ∂μ) =
      thirdFullBudgetFourierMass244 v * thirdFullBudgetFirstMoment244 v := by
    have hs := integral_prod_swap
      (μ := (volume : Measure V3)) (ν := (volume : Measure V3))
      (fun z : PairV => F z.1 ^ 2 * H (-(z.1 + z.2)))
    change (∫ z : PairV, F z.2 ^ 2 * H (-(z.2 + z.1)) ∂μ) =
      (∫ z : PairV, K z ∂μ) at hs
    have hEq : (∫ z : PairV, N z ∂μ) = ∫ z : PairV, K z ∂μ := by
      simpa only [N, add_comm] using hs
    exact hEq.trans hKInt
  have hJInt : (∫ z : PairV, J z ∂μ) =
      thirdFullBudgetFourierMass244 v * thirdFullBudgetFirstMoment244 v := by
    simpa only [J, F, H, thirdFullBudgetFourierMass244,
      thirdFullBudgetFirstMoment244] using hJIntegral
  have hDInt : (∫ z : PairV, D z ∂μ) =
      3 * thirdFullBudgetFourierMass244 v * thirdFullBudgetFirstMoment244 v := by
    have hDExpr : D =
        (G + J) + (fun z => (1 / (2 : ℝ)) * (K + N) z) := by
      funext z
      change G z + J z + (K z + N z) / 2 =
        (G z + J z) + (1 / (2 : ℝ)) * (K z + N z)
      ring
    have h : (∫ z : PairV, D z ∂μ) =
        (∫ z : PairV, G z ∂μ) + (∫ z : PairV, J z ∂μ) +
          ((∫ z : PairV, K z ∂μ) + (∫ z : PairV, N z ∂μ)) / 2 := by
      have hSplit :
          (∫ z : PairV, D z ∂μ) =
            (∫ z : PairV, (G + J) z ∂μ) +
              (∫ z : PairV,
                (fun z : PairV => (1 / (2 : ℝ)) * (K + N) z) z ∂μ) := by
        calc
          (∫ z : PairV, D z ∂μ) =
              (∫ z : PairV,
                ((G + J) + (fun z : PairV =>
                    (1 / (2 : ℝ)) * (K + N) z)) z ∂μ) := by
                  exact congrArg
                    (fun f : PairV → ℝ => ∫ z : PairV, f z ∂μ) hDExpr
          _ = _ := integral_add (hG.add hJ)
            ((hK.add hN).const_mul (1 / (2 : ℝ)))
      -- Keep the function-valued sums opaque until each integral identity
      -- is specialized. `rw [integral_add ...]` does not match `(G + J) z`
      -- after Lean unfolds `J` inside the theorem's pattern.
      have hGJ :
          (∫ z : PairV, (G + J) z ∂μ) =
            (∫ z : PairV, G z ∂μ) +
              (∫ z : PairV, J z ∂μ) := by
        simpa only [Pi.add_apply] using (integral_add hG hJ)
      have hKN :
          (∫ z : PairV, (K + N) z ∂μ) =
            (∫ z : PairV, K z ∂μ) +
              (∫ z : PairV, N z ∂μ) := by
        simpa only [Pi.add_apply] using (integral_add hK hN)
      have hHalf :
          (∫ z : PairV,
            (fun z : PairV => (1 / (2 : ℝ)) * (K + N) z) z ∂μ) =
              (1 / (2 : ℝ)) *
                ((∫ z : PairV, K z ∂μ) +
                  (∫ z : PairV, N z ∂μ)) := by
        rw [integral_const_mul]
        exact congrArg (fun x : ℝ => (1 / (2 : ℝ)) * x) hKN
      rw [hSplit, hGJ, hHalf]
      ring
    rw [h, hGInt, hJInt, hKInt, hNInt]
    ring
  calc
    thirdFullSchwartzSixthFluxTotalBudget244 v =
        ∫ z : PairV, thirdFullSchwartzSixthFluxBudget244 v z ∂μ := rfl
    _ ≤ ∫ z : PairV, D z ∂μ :=
      integral_mono (thirdFullSchwartzSixthFluxBudget_integrable244 v) hD hPoint
    _ = _ := hDInt

/-- Quantitative uniformity is available along ANY Schwartz family whose
actual Fourier L² mass and first L¹ moment are uniformly bounded. -/
theorem thirdFullSchwartzSixthFluxTotalBudget_uniform_of_moments244
    (v : ℕ → A3 → SchwartzMap V3 ℂ) (M E : ℝ)
    (_hM : 0 ≤ M) (hE : 0 ≤ E)
    (hMass : ∀ n, thirdFullBudgetFourierMass244 (v n) ≤ E)
    (hFirst : ∀ n, thirdFullBudgetFirstMoment244 (v n) ≤ M) :
    ∀ n, thirdFullSchwartzSixthFluxTotalBudget244 (v n) ≤ 3 * E * M := by
  intro n
  have h0 := (thirdFullBudgetMoments_nonneg244 (v n)).2
  have h1 := thirdFullSchwartzSixthFluxTotalBudget_le_L2FirstMoment244 (v n)
  calc
    thirdFullSchwartzSixthFluxTotalBudget244 (v n) ≤
        3 * thirdFullBudgetFourierMass244 (v n) *
          thirdFullBudgetFirstMoment244 (v n) := h1
    _ ≤ 3 * E * thirdFullBudgetFirstMoment244 (v n) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hMass n) (by norm_num)) h0
    _ ≤ 3 * E * M :=
      mul_le_mul_of_nonneg_left (hFirst n) (by positivity)

/-- Strong integrated thin-shell suppression for a CHANGING solenoidal
Schwartz family, provided its actual mass and first moment are uniformly
bounded. No bound on higher Schwartz seminorms and no spectral support
cutoff is required. -/
theorem thirdFullSchwartzSixthPowerFlux_movingAnnulus_vanishes_of_moments244
    (v : ℕ → A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ n : ℕ, ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v n j) x (h3FourierAxisDirection j) = 0)
    (lo hi : ℕ → ℝ) (H M E : ℝ)
    (hlo : ∀ n, 0 ≤ lo n) (hlohi : ∀ n, lo n ≤ hi n)
    (hhi : ∀ n, hi n ≤ H)
    (s : ℕ → Set PairV) (hs : ∀ n, MeasurableSet (s n))
    (hShell : ∀ n z, z ∈ s n →
      thirdFullTriadWithinSquareAnnulus244 (lo n) (hi n) z)
    (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hMass : ∀ n, thirdFullBudgetFourierMass244 (v n) ≤ E)
    (hFirst : ∀ n, thirdFullBudgetFirstMoment244 (v n) ≤ M)
    (hWidth : Tendsto (fun n => hi n - lo n) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => ‖∫ z in s n,
      thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
        ∂volume.prod volume‖) atTop (𝓝 (0 : ℝ)) := by
  have hBudget := thirdFullSchwartzSixthFluxTotalBudget_uniform_of_moments244
    v M E hM hE hMass hFirst
  have hUpper (n : ℕ) :
      ‖∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 (v n) z
          ∂volume.prod volume‖ ≤
        (3 * H ^ 2 * (hi n - lo n)) * (3 * E * M) := by
    have hNear := thirdFullSchwartzSixthPowerFlux_annularIntegral_auto244
      (v n) (hDiv n) (lo n) (hi n) (hlo n) (hlohi n)
      (s n) (hs n) (hShell n)
    have hSquare : (hi n) ^ 2 ≤ H ^ 2 :=
      pow_le_pow_left₀ ((hlo n).trans (hlohi n)) (hhi n) 2
    have hCoeff :
        3 * (hi n) ^ 2 * (hi n - lo n) ≤
          3 * H ^ 2 * (hi n - lo n) := by
      have hSq : 3 * (hi n) ^ 2 ≤ 3 * H ^ 2 := by
        nlinarith only [hSquare]
      exact mul_le_mul_of_nonneg_right hSq (sub_nonneg.mpr (hlohi n))
    have hCoeffPos : 0 ≤ 3 * H ^ 2 * (hi n - lo n) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (hlohi n))
    calc
      _ ≤ (3 * (hi n) ^ 2 * (hi n - lo n)) *
          thirdFullSchwartzSixthFluxTotalBudget244 (v n) := hNear
      _ ≤ (3 * H ^ 2 * (hi n - lo n)) *
          thirdFullSchwartzSixthFluxTotalBudget244 (v n) :=
            mul_le_mul_of_nonneg_right hCoeff
              (thirdFullSchwartzSixthFluxTotalBudget_nonneg244 (v n))
      _ ≤ (3 * H ^ 2 * (hi n - lo n)) * (3 * E * M) :=
            mul_le_mul_of_nonneg_left (hBudget n) hCoeffPos
  have hMajor : Tendsto
      (fun n => (3 * H ^ 2 * (hi n - lo n)) * (3 * E * M))
      atTop (𝓝 (0 : ℝ)) := by
    have h := (hWidth.const_mul (3 * H ^ 2)).mul_const (3 * E * M)
    simpa only [mul_zero, zero_mul] using h
  exact squeeze_zero (fun n => norm_nonneg _) hUpper hMajor

end
end PrimeTensor.FirstMonomialTriad

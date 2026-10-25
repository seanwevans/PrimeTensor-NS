import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusIntegratedWindows244
import Mathlib.Tactic

/-!
# Quantitative finite-annulus temporal modulus from weighted spectral increments

The previous file constructs finite annuli with cubic dissipation heights and
positive persistence windows. Here we quantify the needed state variation.

A bounded Fourier multiplier M_R of norm at most R+1 gives the elementary
quadratic estimate

 |‖M_R G‖² - ‖M_R H‖²|
      ≤ (R+1)² (‖G‖+‖H‖) ‖G-H‖.

Summing over three components and subtracting two radial cutoffs gives a
finite-annulus modulus. For three-coordinate norm ceiling K and increment
ceiling ε, the variation is at most

 6 ((Q+1)²+(R+1)²) K ε.

If ε ≤ V(s-t) on a right-hand interval, a computable amplitude/width
criterion retains its annular height and gives a genuine time-integrated lower
bound. No estimate for V from the projected PDE is claimed here: extracting
that estimate is the next analytic obligation. The full unbounded H³
dissipation need not be temporally continuous.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- One bounded low-radial L² Fourier multiplier has a quadratic norm-square
modulus controlled by its operator norm. -/
theorem h3Path_lowRadialMultiplier_quadraticStability244
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (G H : H3SpectralScalarState) :
    |‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ G‖ ^ 2 -
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ H‖ ^ 2| ≤
      (ρ + 1) ^ 2 * (‖G‖ + ‖H‖) * ‖G - H‖ := by
  let M := h3PathLowRadialGradientMultiplierCLM244 ρ hρ
  have hMG : ‖M G‖ ≤ (ρ + 1) * ‖G‖ := by
    exact h3Path_lowRadialGradientMultiplierApply_norm_le244 ρ hρ G
  have hMH : ‖M H‖ ≤ (ρ + 1) * ‖H‖ := by
    exact h3Path_lowRadialGradientMultiplierApply_norm_le244 ρ hρ H
  have hMD : ‖M G - M H‖ ≤ (ρ + 1) * ‖G - H‖ := by
    calc
      ‖M G - M H‖ = ‖M (G - H)‖ := by rw [map_sub]
      _ ≤ (ρ + 1) * ‖G - H‖ :=
        h3Path_lowRadialGradientMultiplierApply_norm_le244 ρ hρ (G - H)
  have hSum : ‖M G‖ + ‖M H‖ ≤ (ρ + 1) * (‖G‖ + ‖H‖) := by
    nlinarith only [hMG, hMH]
  have hSumNonneg : 0 ≤ ‖M G‖ + ‖M H‖ := by positivity
  have hCNonneg : 0 ≤ (ρ + 1) * ‖G - H‖ := by positivity
  change |‖M G‖ ^ 2 - ‖M H‖ ^ 2| ≤
    (ρ + 1) ^ 2 * (‖G‖ + ‖H‖) * ‖G - H‖
  calc
    |‖M G‖ ^ 2 - ‖M H‖ ^ 2| =
        |‖M G‖ - ‖M H‖| * (‖M G‖ + ‖M H‖) := by
          rw [sq_sub_sq, abs_mul, abs_of_nonneg hSumNonneg]
          ac_rfl
    _ ≤ ‖M G - M H‖ * (‖M G‖ + ‖M H‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) hSumNonneg
    _ ≤ ((ρ + 1) * ‖G - H‖) * (‖M G‖ + ‖M H‖) :=
      mul_le_mul_of_nonneg_right hMD hSumNonneg
    _ ≤ ((ρ + 1) * ‖G - H‖) * ((ρ + 1) * (‖G‖ + ‖H‖)) :=
      mul_le_mul_of_nonneg_left hSum hCNonneg
    _ = (ρ + 1) ^ 2 * (‖G‖ + ‖H‖) * ‖G - H‖ := by ring

/-- Quantitative variation of actual low-radial H³ dissipation under a
three-component weighted Fourier norm ceiling and increment ceiling. -/
theorem h3Path_lowRadialDissipation_boundedIncrementStability244
    (ρ K ε : ℝ) (hρ : 0 ≤ ρ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (G H : H3SpectralVelocityState)
    (hG : ∀ j : Fin 3, ‖G j‖ ≤ K)
    (hH : ∀ j : Fin 3, ‖H j‖ ≤ K)
    (hDiff : ∀ j : Fin 3, ‖G j - H j‖ ≤ ε) :
    |h3PathActualLowRadialDissipation244 ρ G -
      h3PathActualLowRadialDissipation244 ρ H| ≤
      6 * (ρ + 1) ^ 2 * K * ε := by
  let M := h3PathLowRadialGradientMultiplierCLM244 ρ hρ
  let F : H3SpectralScalarState → ℝ := fun x => ‖M x‖ ^ 2
  have hEach (j : Fin 3) :
      |F (G j) - F (H j)| ≤ 2 * (ρ + 1) ^ 2 * K * ε := by
    have hSq := h3Path_lowRadialMultiplier_quadraticStability244
      ρ hρ (G j) (H j)
    have hSum : ‖G j‖ + ‖H j‖ ≤ 2 * K := by
      linarith only [hG j, hH j]
    have hFactor :
        (ρ + 1) ^ 2 * (‖G j‖ + ‖H j‖) * ‖G j - H j‖ ≤
        (ρ + 1) ^ 2 * (2 * K) * ε := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hSum (sq_nonneg _)
      · exact hDiff j
      · exact norm_nonneg _
      · exact mul_nonneg (sq_nonneg _) (by positivity)
    change |F (G j) - F (H j)| ≤ 2 * (ρ + 1) ^ 2 * K * ε
    calc
      |F (G j) - F (H j)| ≤
        (ρ + 1) ^ 2 * (‖G j‖ + ‖H j‖) * ‖G j - H j‖ := hSq
      _ ≤ (ρ + 1) ^ 2 * (2 * K) * ε := hFactor
      _ = 2 * (ρ + 1) ^ 2 * K * ε := by ring
  rw [h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 ρ hρ G,
      h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 ρ hρ H]
  simp only [Fin.sum_univ_three]
  change |(F (G 0) + F (G 1) + F (G 2)) -
      (F (H 0) + F (H 1) + F (H 2))| ≤
      6 * (ρ + 1) ^ 2 * K * ε
  calc
    |(F (G 0) + F (G 1) + F (G 2)) -
        (F (H 0) + F (H 1) + F (H 2))| =
        |(F (G 0) - F (H 0)) +
          ((F (G 1) - F (H 1)) + (F (G 2) - F (H 2)))| := by
            congr 1 <;> ring
    _ ≤ |F (G 0) - F (H 0)| +
          (|F (G 1) - F (H 1)| + |F (G 2) - F (H 2)|) := by
            exact
              (abs_add_le
                (F (G 0) - F (H 0))
                ((F (G 1) - F (H 1)) + (F (G 2) - F (H 2)))).trans
              (add_le_add_right
                (abs_add_le (F (G 1) - F (H 1))
                  (F (G 2) - F (H 2)))
                |F (G 0) - F (H 0)|)
    _ ≤ 6 * (ρ + 1) ^ 2 * K * ε := by
      have h0 := hEach (0 : Fin 3)
      have h1 := hEach (1 : Fin 3)
      have h2 := hEach (2 : Fin 3)
      linarith only [h0, h1, h2]

/-- A finite annular physical H³ dissipation quadratic has a concrete
spectral-state modulus, with neither a full H⁴ norm nor continuity of the
unbounded dissipation functional as input. -/
theorem h3Path_finiteAnnulus_boundedIncrementStability244
    (R Q K ε : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (G H : H3SpectralVelocityState)
    (hG : ∀ j : Fin 3, ‖G j‖ ≤ K)
    (hH : ∀ j : Fin 3, ‖H j‖ ≤ K)
    (hDiff : ∀ j : Fin 3, ‖G j - H j‖ ≤ ε) :
    |(h3PathActualLowRadialDissipation244 Q G -
        h3PathActualLowRadialDissipation244 R G) -
      (h3PathActualLowRadialDissipation244 Q H -
        h3PathActualLowRadialDissipation244 R H)| ≤
      6 * ((Q + 1) ^ 2 + (R + 1) ^ 2) * K * ε := by
  have hQDiff := h3Path_lowRadialDissipation_boundedIncrementStability244
    Q K ε hQ hK hε G H hG hH hDiff
  have hRDiff := h3Path_lowRadialDissipation_boundedIncrementStability244
    R K ε hR hK hε G H hG hH hDiff
  calc
    |(h3PathActualLowRadialDissipation244 Q G -
        h3PathActualLowRadialDissipation244 R G) -
      (h3PathActualLowRadialDissipation244 Q H -
        h3PathActualLowRadialDissipation244 R H)| =
        |(h3PathActualLowRadialDissipation244 Q G -
            h3PathActualLowRadialDissipation244 Q H) -
          (h3PathActualLowRadialDissipation244 R G -
            h3PathActualLowRadialDissipation244 R H)| := by
              congr 1 <;> ring
    _ ≤ |h3PathActualLowRadialDissipation244 Q G -
          h3PathActualLowRadialDissipation244 Q H| +
        |h3PathActualLowRadialDissipation244 R G -
          h3PathActualLowRadialDissipation244 R H| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le
              (h3PathActualLowRadialDissipation244 Q G -
                h3PathActualLowRadialDissipation244 Q H)
              (-(h3PathActualLowRadialDissipation244 R G -
                h3PathActualLowRadialDissipation244 R H)))
    _ ≤ 6 * (Q + 1) ^ 2 * K * ε +
          6 * (R + 1) ^ 2 * K * ε := add_le_add hQDiff hRDiff
    _ = 6 * ((Q + 1) ^ 2 + (R + 1) ^ 2) * K * ε := by ring

/-- An explicit amplitude-duration criterion. A bound `V` on the rate of
change of each weighted H³ spectral velocity coordinate suffices to keep a
finite annular dissipation height `A` throughout a prescribed right window.
The spectral rate is a visible PDE obligation, rather than an assertion that
qualitative temporal continuity supplies a fixed width. -/
theorem h3Path_finiteAnnulus_integratedCost_of_spectralIncrementRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R Q K V A t δ : ℝ)
    (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hV : 0 ≤ V) (hA : 0 ≤ A)
    (ht : t ∈ Set.Ioo a T) (hδ : 0 < δ) (hEnd : t + δ < T)
    (hBase : ∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K)
    (hEnvelope : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ∀ j : Fin 3,
        ‖(h3AuditActualSpectralVelocityTotal hH3 s) j‖ ≤ K)
    (hRate : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ∀ j : Fin 3,
        ‖(h3AuditActualSpectralVelocityTotal hH3 s) j -
          (h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ V * (s - t))
    (hHeight : A <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 t))
    (hWidthBudget :
      (6 * ((Q + 1) ^ 2 + (R + 1) ^ 2) * K * V) * δ <
        (h3PathActualLowRadialDissipation244 Q
          (h3AuditActualSpectralVelocityTotal hH3 t) -
         h3PathActualLowRadialDissipation244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)) - A) :
    (∀ s : ℝ, s ∈ Set.Icc t (t + δ) → A <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
    δ * A ≤
      (∫ s in t..(t + δ),
        h3PathActualLowRadialDissipation244 Q
          (h3AuditActualSpectralVelocityTotal hH3 s) -
        h3PathActualLowRadialDissipation244 R
          (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  let G : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  let B : ℝ → ℝ := fun s =>
    h3PathActualLowRadialDissipation244 Q (G s) -
    h3PathActualLowRadialDissipation244 R (G s)
  have hC : 0 ≤ 6 * ((Q + 1) ^ 2 + (R + 1) ^ 2) * K * V := by
    positivity
  have hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) → A < B s := by
    intro s hs
    have hTime : 0 ≤ s - t := sub_nonneg.mpr hs.1
    have hTimeδ : s - t ≤ δ := by linarith only [hs.2]
    have hDiff := h3Path_finiteAnnulus_boundedIncrementStability244
      R Q K (V * (s - t)) hR hQ hK (mul_nonneg hV hTime)
      (G s) (G t) (hEnvelope s hs) hBase (hRate s hs)
    have hError : B t - B s ≤
        6 * ((Q + 1) ^ 2 + (R + 1) ^ 2) * K * (V * (s - t)) := by
      change |B s - B t| ≤ _ at hDiff
      have hReverse : B t - B s ≤ |B s - B t| := by
        have h := neg_le_abs (B s - B t)
        linarith only [h]
      exact le_trans hReverse hDiff
    have hMaxError :
        6 * ((Q + 1) ^ 2 + (R + 1) ^ 2) * K * (V * (s - t)) ≤
        (6 * ((Q + 1) ^ 2 + (R + 1) ^ 2) * K * V) * δ := by
      calc
        _ = (6 * ((Q + 1) ^ 2 + (R + 1) ^ 2) * K * V) * (s - t) := by ring
        _ ≤ (6 * ((Q + 1) ^ 2 + (R + 1) ^ 2) * K * V) * δ :=
          mul_le_mul_of_nonneg_left hTimeδ hC
    change (6 * ((Q + 1) ^ 2 + (R + 1) ^ 2) * K * V) * δ < B t - A
      at hWidthBudget
    linarith only [hError, hMaxError, hWidthBudget]
  have hSub : Set.Icc t (t + δ) ⊆ Set.Ioo a T := by
    intro s hs
    exact ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hB : ContinuousOn B (Set.Ioo a T) := by
    exact h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass R Q hR hQ
  have hInt : IntervalIntegrable B volume t (t + δ) :=
    (hB.mono hSub).intervalIntegrable_of_Icc (by linarith only [hδ])
  have hIntegral := h3Path_localPositiveHeight_forces_integratedCost244
    B t (t + δ) A (by linarith only [hδ]) hInt
    (fun s hs => (hFloor s hs).le)
  constructor
  · exact hFloor
  · change δ * A ≤ ∫ s in t..(t + δ), B s
    calc
      δ * A = ((t + δ) - t) * A := by ring
      _ ≤ ∫ s in t..(t + δ), B s := hIntegral

end
end PrimeTensor.FirstMonomialTriad

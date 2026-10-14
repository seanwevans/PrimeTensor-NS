import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterWeightedKernel

/-!
# A real-even, nonnegative Schwartz-preserving frequency window

Build a new window out of adjustable smooth compact cutoffs at the primary
quarter-scale frequencies and their pointwise reflections. It is even,
nonnegative, smooth, compactly supported, and positive at P,Q,R.

Its nonzero momentum triples lie in the twelve-center orbit thickening.
Trilinearity of the *original fixed-width Schwartz* symbol then gives the
correct sign for its windowed field wherever all three window factors are
nonzero. We do not claim a nonzero full-space integral in this module.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Metric
open scoped Topology ContDiff SchwartzMap

noncomputable section

private abbrev WindowV := Fin 3 → ℝ
private abbrev WindowA := Fin 3 → ℂ
private abbrev WindowPair := WindowV × WindowV

/-- Positive-frequency sum of three quarter-scale adjustable bump functions. -/
noncomputable def lowNormalQuarterPrimaryWindow (ρ : ℝ) (hρ : 0 < ρ)
    (ξ : WindowV) : ℝ :=
  (lowNormalQuarterNarrowCutoff ρ hρ 0 ξ +
    lowNormalQuarterNarrowCutoff ρ hρ 1 ξ) +
    lowNormalQuarterNarrowCutoff ρ hρ 2 ξ

/-- The *same* scalar window at reflected frequencies. The second summand
makes the Hermitian reality symmetry an algebraic identity. -/
noncomputable def lowNormalQuarterEvenWindow (ρ : ℝ) (hρ : 0 < ρ)
    (ξ : WindowV) : ℝ :=
  lowNormalQuarterPrimaryWindow ρ hρ ξ +
    lowNormalQuarterPrimaryWindow ρ hρ (-ξ)

/-- Each adjustable frequency cutoff is pointwise nonnegative. -/
theorem lowNormalQuarterNarrowCutoff_nonneg
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6) (ξ : WindowV) :
    0 ≤ lowNormalQuarterNarrowCutoff ρ hρ i ξ := by
  exact (lowNormalCenteredFrequencyBump
    (lowNormalSixCenter (1 / 4 : ℝ) i) ρ hρ).nonneg

/-- Nonnegativity of the three primary bumps. -/
theorem lowNormalQuarterPrimaryWindow_nonneg
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : WindowV) :
    0 ≤ lowNormalQuarterPrimaryWindow ρ hρ ξ := by
  unfold lowNormalQuarterPrimaryWindow
  exact add_nonneg
    (add_nonneg (lowNormalQuarterNarrowCutoff_nonneg ρ hρ 0 ξ)
      (lowNormalQuarterNarrowCutoff_nonneg ρ hρ 1 ξ))
    (lowNormalQuarterNarrowCutoff_nonneg ρ hρ 2 ξ)

/-- The reflected six-center scalar window is nonnegative everywhere. -/
theorem lowNormalQuarterEvenWindow_nonneg
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : WindowV) :
    0 ≤ lowNormalQuarterEvenWindow ρ hρ ξ := by
  exact add_nonneg (lowNormalQuarterPrimaryWindow_nonneg ρ hρ ξ)
    (lowNormalQuarterPrimaryWindow_nonneg ρ hρ (-ξ))

/-- Frequency reflection preserves the scalar window exactly. -/
theorem lowNormalQuarterEvenWindow_even
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : WindowV) :
    lowNormalQuarterEvenWindow ρ hρ (-ξ) =
      lowNormalQuarterEvenWindow ρ hρ ξ := by
  unfold lowNormalQuarterEvenWindow
  rw [neg_neg]
  exact add_comm _ _

/-- Three adjustable smooth cutoffs give a smooth primary window. -/
theorem lowNormalQuarterPrimaryWindow_contDiff
    (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiff ℝ ∞ (lowNormalQuarterPrimaryWindow ρ hρ) := by
  have h := ((lowNormalQuarterNarrowCutoff_contDiff ρ hρ 0).add
    (lowNormalQuarterNarrowCutoff_contDiff ρ hρ 1)).add
    (lowNormalQuarterNarrowCutoff_contDiff ρ hρ 2)
  convert h using 1
  funext ξ
  rfl

/-- The primary window has compact support. -/
theorem lowNormalQuarterPrimaryWindow_hasCompactSupport
    (ρ : ℝ) (hρ : 0 < ρ) :
    HasCompactSupport (lowNormalQuarterPrimaryWindow ρ hρ) := by
  exact ((lowNormalQuarterNarrowCutoff_hasCompactSupport ρ hρ 0).add
    (lowNormalQuarterNarrowCutoff_hasCompactSupport ρ hρ 1)).add
    (lowNormalQuarterNarrowCutoff_hasCompactSupport ρ hρ 2)

/-- The real-even window is smooth to all orders. -/
theorem lowNormalQuarterEvenWindow_contDiff
    (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiff ℝ ∞ (lowNormalQuarterEvenWindow ρ hρ) := by
  have hp := lowNormalQuarterPrimaryWindow_contDiff ρ hρ
  change ContDiff ℝ ∞ (fun ξ : WindowV =>
    lowNormalQuarterPrimaryWindow ρ hρ ξ +
      lowNormalQuarterPrimaryWindow ρ hρ (-ξ))
  have h := hp.add (hp.comp contDiff_id.neg)
  convert h using 1
  funext ξ
  rfl

/-- The window remains compactly supported under frequency reflection. -/
theorem lowNormalQuarterEvenWindow_hasCompactSupport
    (ρ : ℝ) (hρ : 0 < ρ) :
    HasCompactSupport (lowNormalQuarterEvenWindow ρ hρ) := by
  have hp := lowNormalQuarterPrimaryWindow_hasCompactSupport ρ hρ
  have hn : HasCompactSupport (fun ξ : WindowV =>
      lowNormalQuarterPrimaryWindow ρ hρ (-ξ)) := by
    simpa only [Function.comp_def, Homeomorph.coe_neg] using
      hp.comp_homeomorph (Homeomorph.neg WindowV)
  change HasCompactSupport (fun ξ : WindowV =>
    lowNormalQuarterPrimaryWindow ρ hρ ξ +
      lowNormalQuarterPrimaryWindow ρ hρ (-ξ))
  exact hp.add hn

/-- The scalar window itself is a genuine real-valued Schwartz function. -/
noncomputable def lowNormalQuarterEvenWindowSchwartz
    (ρ : ℝ) (hρ : 0 < ρ) : 𝓢(WindowV, ℝ) :=
  (lowNormalQuarterEvenWindow_hasCompactSupport ρ hρ).toSchwartzMap
    (lowNormalQuarterEvenWindow_contDiff ρ hρ)

@[simp] theorem lowNormalQuarterEvenWindowSchwartz_apply
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : WindowV) :
    lowNormalQuarterEvenWindowSchwartz ρ hρ ξ =
      lowNormalQuarterEvenWindow ρ hρ ξ := rfl

/-- A center bump has value exactly one at its assigned frequency center. -/
theorem lowNormalQuarterNarrowCutoff_at_center
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6) :
    lowNormalQuarterNarrowCutoff ρ hρ i
      (lowNormalSixCenter (1 / 4 : ℝ) i) = 1 := by
  unfold lowNormalQuarterNarrowCutoff
  apply (lowNormalCenteredFrequencyBump
    (lowNormalSixCenter (1 / 4 : ℝ) i) ρ hρ).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_self]
  dsimp [lowNormalCenteredFrequencyBump]
  linarith

/-- The window is strictly positive at all three primary centers. -/
theorem lowNormalQuarterEvenWindow_pos_at_primary_centers
    (ρ : ℝ) (hρ : 0 < ρ) :
    0 < lowNormalQuarterEvenWindow ρ hρ lowNormalAuditP ∧
    0 < lowNormalQuarterEvenWindow ρ hρ (lowNormalAuditQ (1 / 4 : ℝ)) ∧
    0 < lowNormalQuarterEvenWindow ρ hρ (lowNormalAuditR (1 / 4 : ℝ)) := by
  have h0 := (lowNormalSixCenter_primary (1 / 4 : ℝ)).1
  have h1 := (lowNormalSixCenter_primary (1 / 4 : ℝ)).2.1
  have h2 := (lowNormalSixCenter_primary (1 / 4 : ℝ)).2.2
  have hone0 : lowNormalQuarterNarrowCutoff ρ hρ 0 lowNormalAuditP = 1 := by
    rw [← h0]
    exact lowNormalQuarterNarrowCutoff_at_center ρ hρ 0
  have hone1 : lowNormalQuarterNarrowCutoff ρ hρ 1
      (lowNormalAuditQ (1 / 4 : ℝ)) = 1 := by
    rw [← h1]
    exact lowNormalQuarterNarrowCutoff_at_center ρ hρ 1
  have hone2 : lowNormalQuarterNarrowCutoff ρ hρ 2
      (lowNormalAuditR (1 / 4 : ℝ)) = 1 := by
    rw [← h2]
    exact lowNormalQuarterNarrowCutoff_at_center ρ hρ 2
  have helper (ξ : WindowV) (i : Fin 6)
      (hi : i = 0 ∨ i = 1 ∨ i = 2)
      (hone : lowNormalQuarterNarrowCutoff ρ hρ i ξ = 1) :
      0 < lowNormalQuarterEvenWindow ρ hρ ξ := by
    have ha := lowNormalQuarterNarrowCutoff_nonneg ρ hρ 0 ξ
    have hb := lowNormalQuarterNarrowCutoff_nonneg ρ hρ 1 ξ
    have hc := lowNormalQuarterNarrowCutoff_nonneg ρ hρ 2 ξ
    have hn := lowNormalQuarterPrimaryWindow_nonneg ρ hρ (-ξ)
    change 0 < (lowNormalQuarterNarrowCutoff ρ hρ 0 ξ +
      lowNormalQuarterNarrowCutoff ρ hρ 1 ξ +
      lowNormalQuarterNarrowCutoff ρ hρ 2 ξ) +
      lowNormalQuarterPrimaryWindow ρ hρ (-ξ)
    rcases hi with h | h | h
    · subst i
      linarith
    · subst i
      linarith
    · subst i
      linarith
  exact ⟨helper _ 0 (Or.inl rfl) hone0,
    helper _ 1 (Or.inr (Or.inl rfl)) hone1,
    helper _ 2 (Or.inr (Or.inr rfl)) hone2⟩

/-- Reflection preserves incompressibility under an arbitrary scalar weight. -/
theorem lowNormalQuarterWindowedFourier_divergence
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : WindowV) :
    mixedDot ξ (lowNormalQuarterWeightedFourier
      (lowNormalQuarterEvenWindow ρ hρ) ξ) = 0 := by
  have h : mixedDot ξ (lowNormalQuarterSchwartz ξ) = 0 := by
    exact lowNormalSmoothSixPacketSchwartz_divergence
      (1 / 4 : ℝ) (by norm_num) ξ
  change mixedDot ξ (fun d =>
    ((lowNormalQuarterEvenWindow ρ hρ ξ : ℝ) : ℂ) *
      lowNormalQuarterSchwartz ξ d) = 0
  calc
    _ = (lowNormalQuarterEvenWindow ρ hρ ξ : ℂ) *
      mixedDot ξ (lowNormalQuarterSchwartz ξ) := by
        simp only [mixedDot, Fin.sum_univ_succ]
        ring
    _ = 0 := by rw [h]; ring

/-- Hermitian reality is preserved because the scalar window is real and even. -/
theorem lowNormalQuarterWindowedFourier_reality
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : WindowV) :
    lowNormalQuarterWeightedFourier (lowNormalQuarterEvenWindow ρ hρ) (-ξ) =
      fun d => star
        (lowNormalQuarterWeightedFourier (lowNormalQuarterEvenWindow ρ hρ) ξ d) := by
  funext d
  change ((lowNormalQuarterEvenWindow ρ hρ (-ξ) : ℝ) : ℂ) *
      lowNormalQuarterSchwartz (-ξ) d =
    star (((lowNormalQuarterEvenWindow ρ hρ ξ : ℝ) : ℂ) *
      lowNormalQuarterSchwartz ξ d)
  have hReality : lowNormalQuarterSchwartz (-ξ) =
      (fun k => star (lowNormalQuarterSchwartz ξ k)) := by
    exact lowNormalSmoothSixPacketSchwartz_reality
      (1 / 4 : ℝ) (by norm_num) ξ
  rw [lowNormalQuarterEvenWindow_even, hReality]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]

/-- The real-even scalar window times the original solenoidal Schwartz
field remains smooth to every order. -/
theorem lowNormalQuarterWindowedFourier_contDiff
    (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiff ℝ ∞ (lowNormalQuarterWeightedFourier
      (lowNormalQuarterEvenWindow ρ hρ)) := by
  apply contDiff_pi'
  intro d
  have hw : ContDiff ℝ ∞
      (fun ξ : WindowV => ((lowNormalQuarterEvenWindow ρ hρ ξ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (lowNormalQuarterEvenWindow_contDiff ρ hρ)
  have hu : ContDiff ℝ ∞
      (fun ξ : WindowV => lowNormalSmoothSixPacketFourier
        (1 / 4 : ℝ) (by norm_num) ξ d) :=
    (contDiff_apply ℝ ℂ d).comp
      (lowNormalSmoothSixPacketFourier_contDiff (1 / 4 : ℝ) (by norm_num))
  change ContDiff ℝ ∞ (fun ξ : WindowV =>
    ((lowNormalQuarterEvenWindow ρ hρ ξ : ℝ) : ℂ) *
      lowNormalSmoothSixPacketFourier (1 / 4 : ℝ) (by norm_num) ξ d)
  exact hw.mul hu

/-- The weighted vector Fourier field inherits compact support from the
frequency window, independently of the original field's support. -/
theorem lowNormalQuarterWindowedFourier_hasCompactSupport
    (ρ : ℝ) (hρ : 0 < ρ) :
    HasCompactSupport (lowNormalQuarterWeightedFourier
      (lowNormalQuarterEvenWindow ρ hρ)) := by
  have hs := (lowNormalQuarterEvenWindow_hasCompactSupport ρ hρ).smul_right
    (f' := fun ξ : WindowV => lowNormalQuarterSchwartz ξ)
  convert hs using 1
  funext ξ d
  change ((lowNormalQuarterEvenWindow ρ hρ ξ : ℂ) *
      lowNormalQuarterSchwartz ξ d) =
    (lowNormalQuarterEvenWindow ρ hρ ξ : ℝ) •
      lowNormalQuarterSchwartz ξ d
  rw [← Complex.coe_smul, smul_eq_mul]

/-- The windowed field itself is packaged as a complex vector Schwartz map. -/
noncomputable def lowNormalQuarterWindowedSchwartz
    (ρ : ℝ) (hρ : 0 < ρ) : 𝓢(WindowV, WindowA) :=
  (lowNormalQuarterWindowedFourier_hasCompactSupport ρ hρ).toSchwartzMap
    (lowNormalQuarterWindowedFourier_contDiff ρ hρ)

@[simp] theorem lowNormalQuarterWindowedSchwartz_apply
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : WindowV) :
    lowNormalQuarterWindowedSchwartz ρ hρ ξ =
      lowNormalQuarterWeightedFourier (lowNormalQuarterEvenWindow ρ hρ) ξ := rfl

/-- A nonzero scalar window is located near one of the six frequency centers. -/
theorem lowNormalQuarterEvenWindow_nonzero_center
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : WindowV)
    (hw : lowNormalQuarterEvenWindow ρ hρ ξ ≠ 0) :
    ∃ i : Fin 6, dist ξ (lowNormalSixCenter (1 / 4 : ℝ) i) < ρ := by
  by_contra hn
  have hfar (i : Fin 6) :
      ρ ≤ dist ξ (lowNormalSixCenter (1 / 4 : ℝ) i) :=
    le_of_not_gt (fun hi => hn ⟨i, hi⟩)
  have hzero (i : Fin 6) (x : WindowV)
      (h : ρ ≤ dist x (lowNormalSixCenter (1 / 4 : ℝ) i)) :
      lowNormalQuarterNarrowCutoff ρ hρ i x = 0 := by
    by_contra hχ
    exact (not_lt.mpr h)
      (lowNormalQuarterNarrowCutoff_nonzero_ball ρ hρ i x hχ)
  have hp := hzero 0 ξ (hfar 0)
  have hq := hzero 1 ξ (hfar 1)
  have hr := hzero 2 ξ (hfar 2)
  have hNegFar (i j : Fin 6)
      (hj : lowNormalSixCenter (1 / 4 : ℝ) j =
        -(lowNormalSixCenter (1 / 4 : ℝ) i)) :
      ρ ≤ dist (-ξ) (lowNormalSixCenter (1 / 4 : ℝ) i) := by
    have hEq : dist (-ξ) (lowNormalSixCenter (1 / 4 : ℝ) i) =
        dist ξ (lowNormalSixCenter (1 / 4 : ℝ) j) := by
      rw [hj]
      simpa only [neg_neg] using
        (dist_neg_neg ξ (-(lowNormalSixCenter (1 / 4 : ℝ) i)))
    rw [hEq]
    exact hfar j
  have hc0 : lowNormalSixCenter (1 / 4 : ℝ) 3 =
      -(lowNormalSixCenter (1 / 4 : ℝ) 0) := by
    rw [(lowNormalSixCenter_reflected (1 / 4 : ℝ)).1,
      (lowNormalSixCenter_primary (1 / 4 : ℝ)).1]
    rfl
  have hc1 : lowNormalSixCenter (1 / 4 : ℝ) 4 =
      -(lowNormalSixCenter (1 / 4 : ℝ) 1) := by
    rw [(lowNormalSixCenter_reflected (1 / 4 : ℝ)).2.1,
      (lowNormalSixCenter_primary (1 / 4 : ℝ)).2.1]
    rfl
  have hc2 : lowNormalSixCenter (1 / 4 : ℝ) 5 =
      -(lowNormalSixCenter (1 / 4 : ℝ) 2) := by
    rw [(lowNormalSixCenter_reflected (1 / 4 : ℝ)).2.2,
      (lowNormalSixCenter_primary (1 / 4 : ℝ)).2.2]
    rfl
  have hpn := hzero 0 (-ξ) (hNegFar 0 3 hc0)
  have hqn := hzero 1 (-ξ) (hNegFar 1 4 hc1)
  have hrn := hzero 2 (-ξ) (hNegFar 2 5 hc2)
  apply hw
  simp [lowNormalQuarterEvenWindow, lowNormalQuarterPrimaryWindow,
    hp, hq, hr, hpn, hqn, hrn]

/-- Any nonzero momentum triple for the window has coherent labels. -/
theorem lowNormalQuarterEvenWindow_three_support_in_tube
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 / 4 : ℝ))
    (p r : WindowV)
    (hp : lowNormalQuarterEvenWindow ρ hρ p ≠ 0)
    (hq : lowNormalQuarterEvenWindow ρ hρ (middleFrequency p r) ≠ 0)
    (hr : lowNormalQuarterEvenWindow ρ hρ r ≠ 0) :
    (p, r) ∈ Metric.thickening ρ lowNormalQuarterCoherentCenterSet := by
  obtain ⟨i, hi⟩ := lowNormalQuarterEvenWindow_nonzero_center ρ hρ p hp
  obtain ⟨j, hj⟩ := lowNormalQuarterEvenWindow_nonzero_center ρ hρ
    (middleFrequency p r) hq
  obtain ⟨k, hk⟩ := lowNormalQuarterEvenWindow_nonzero_center ρ hρ r hr
  have hBall (l : Fin 6) (x : WindowV)
      (hd : dist x (lowNormalSixCenter (1 / 4 : ℝ) l) < ρ) :
      lowNormalSixCenterCoordinateBall (1 / 4 : ℝ) l x := by
    intro d
    have hCoord : |x d - lowNormalSixCenter (1 / 4 : ℝ) l d| ≤
        dist x (lowNormalSixCenter (1 / 4 : ℝ) l) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply, dist_eq_norm] using
        (norm_le_pi_norm (x - lowNormalSixCenter (1 / 4 : ℝ) l) d)
    exact lt_of_le_of_lt hCoord (lt_of_lt_of_le hd hSmall)
  have hCoherent : lowNormalCoherentCenters i j k :=
    lowNormalSixCenterCoordinateBall_zero_sum_coherent (1 / 4 : ℝ)
      (by norm_num) i j k p (middleFrequency p r) r
      (hBall i p hi) (hBall j (middleFrequency p r) hj)
      (hBall k r hk) (middleFrequency_momentum p r)
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(lowNormalSixCenter (1 / 4 : ℝ) i,
      lowNormalSixCenter (1 / 4 : ℝ) k), ?_, ?_⟩
  · rw [← lowNormalQuarterLabeledCoherentPairSet_eq_centerSet]
    exact ⟨i, j, k, hCoherent, rfl⟩
  · simpa only [Prod.dist_eq, max_lt_iff] using And.intro hi hk

/-- There exists a nonresonant window width for which every nonzero
momentum triple stays inside the positive tube of the ORIGINAL signed
kernel, so the actual weighted signed kernel is strictly positive there. -/
theorem lowNormalQuarterEvenWindow_exists_positive_kernel_on_triples :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ρ ≤ lowNormalSixCenterSeparationRadius (1 / 4 : ℝ) ∧
      (∀ p r : WindowV,
        lowNormalQuarterEvenWindow ρ hρ p ≠ 0 →
        lowNormalQuarterEvenWindow ρ hρ (middleFrequency p r) ≠ 0 →
        lowNormalQuarterEvenWindow ρ hρ r ≠ 0 →
        0 < lowNormalQuarterWeightedSignedKernel
          (lowNormalQuarterEvenWindow ρ hρ) (p, r)) := by
  obtain ⟨δ, hδ, hPositive⟩ :=
    lowNormalQuarterSignedKernel_exists_uniform_positive_tube
  let σ := lowNormalSixCenterSeparationRadius (1 / 4 : ℝ)
  have hσ : 0 < σ := lowNormalSixCenterSeparationRadius_pos
    (1 / 4 : ℝ) (by norm_num)
  let ρ : ℝ := min δ σ / 2
  have hρ : 0 < ρ := half_pos (lt_min hδ hσ)
  have hSmall : ρ ≤ σ := by
    dsimp [ρ]
    linarith [min_le_right δ σ]
  have hρδ : ρ ≤ δ := by
    dsimp [ρ]
    linarith [min_le_left δ σ]
  refine ⟨ρ, hρ, hSmall, ?_⟩
  intro p r hp hq hr
  have hNear := lowNormalQuarterEvenWindow_three_support_in_tube
    ρ hρ hSmall p r hp hq hr
  have hIn : (p, r) ∈ Metric.cthickening δ
      lowNormalQuarterCoherentCenterSet :=
    (Metric.thickening_subset_cthickening_of_le hρδ
      lowNormalQuarterCoherentCenterSet) hNear
  have hwp : 0 < lowNormalQuarterEvenWindow ρ hρ p :=
    lt_of_le_of_ne (lowNormalQuarterEvenWindow_nonneg ρ hρ p) (Ne.symm hp)
  have hwq : 0 < lowNormalQuarterEvenWindow ρ hρ (middleFrequency p r) :=
    lt_of_le_of_ne
      (lowNormalQuarterEvenWindow_nonneg ρ hρ (middleFrequency p r)) (Ne.symm hq)
  have hwr : 0 < lowNormalQuarterEvenWindow ρ hρ r :=
    lt_of_le_of_ne (lowNormalQuarterEvenWindow_nonneg ρ hρ r) (Ne.symm hr)
  exact lowNormalQuarterWeightedSignedKernel_pos_in_centerTube
    (lowNormalQuarterEvenWindow ρ hρ) δ hPositive p r hIn hwp hwq hwr

/-- The six-permutation *weighted* signed kernel is strictly positive at
its primary resonant center, for every positive window width. -/
theorem lowNormalQuarterEvenWindow_weightedKernel_pos_at_center
    (ρ : ℝ) (hρ : 0 < ρ) :
    0 < lowNormalQuarterWeightedSignedKernel
      (lowNormalQuarterEvenWindow ρ hρ)
      (lowNormalAuditP, lowNormalAuditR (1 / 4 : ℝ)) := by
  obtain ⟨hp, hq, hr⟩ := lowNormalQuarterEvenWindow_pos_at_primary_centers ρ hρ
  have hm : middleFrequency lowNormalAuditP (lowNormalAuditR (1 / 4 : ℝ)) =
      lowNormalAuditQ (1 / 4 : ℝ) := by
    funext d
    have h := lowNormalAudit_momentum (1 / 4 : ℝ) d
    dsimp [middleFrequency]
    linarith
  apply lowNormalQuarterWeightedSignedKernel_pos
  · exact hp
  · rw [hm]
    exact hq
  · exact hr
  · rw [lowNormalQuarterSignedKernel_at_center]
    norm_num

end
end PrimeTensor.FirstMonomialTriad

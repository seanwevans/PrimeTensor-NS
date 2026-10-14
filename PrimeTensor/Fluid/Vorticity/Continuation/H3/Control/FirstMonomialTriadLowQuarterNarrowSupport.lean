import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterUniformTube
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowVectorSchwartz

/-!
# Adjustable Schwartz-packet width and exact coherent-support geometry

The previously used six-packet Fourier Schwartz field has an outer cutoff
radius fixed at 1/16. The existing uniform signed-kernel tube theorem is
about that *fixed field*: its positivity does not automatically transfer to
a new Schwartz field whose cutoffs have been narrowed.

Here the radius is an independent positive parameter. We construct smooth,
compactly supported scalar packets and their Hermitian, divergence-free
vector-valued Schwartz assembly. If the width does not exceed the existing
quantitative separation radius, any triple of nonzero Fourier amplitudes
with zero total momentum must carry coherent labels. Moreover its two
independent Fourier frequencies lie in the corresponding product ball of
the chosen width. This is the support-geometric half of the global-integral
problem. The sign of the *new width-dependent kernel* is not asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Metric
open scoped Topology SchwartzMap ContDiff

noncomputable section

private abbrev NarrowV := Fin 3 → ℝ

/-- Independently adjustable smooth cutoff around one of the six fixed centers. -/
noncomputable def lowNormalQuarterNarrowCutoff
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6) : NarrowV → ℝ :=
  lowNormalCenteredFrequencyBump (lowNormalSixCenter (1 / 4 : ℝ) i) ρ hρ

/-- A nonzero adjustable cutoff must lie strictly inside its center ball. -/
theorem lowNormalQuarterNarrowCutoff_nonzero_ball
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6) (ξ : NarrowV)
    (hχ : lowNormalQuarterNarrowCutoff ρ hρ i ξ ≠ 0) :
    dist ξ (lowNormalSixCenter (1 / 4 : ℝ) i) < ρ := by
  let b := lowNormalCenteredFrequencyBump
    (lowNormalSixCenter (1 / 4 : ℝ) i) ρ hρ
  have hs : ξ ∈ Function.support (b : NarrowV → ℝ) := by
    change b ξ ≠ 0
    exact hχ
  rw [b.support_eq] at hs
  change ξ ∈ Metric.ball (lowNormalSixCenter (1 / 4 : ℝ) i) ρ at hs
  exact hs

/-- Each adjustable cutoff is smooth. -/
theorem lowNormalQuarterNarrowCutoff_contDiff
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6) :
    ContDiff ℝ ∞ (lowNormalQuarterNarrowCutoff ρ hρ i) :=
  (lowNormalCenteredFrequencyBump
    (lowNormalSixCenter (1 / 4 : ℝ) i) ρ hρ).contDiff

/-- Each adjustable cutoff has compact support. -/
theorem lowNormalQuarterNarrowCutoff_hasCompactSupport
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6) :
    HasCompactSupport (lowNormalQuarterNarrowCutoff ρ hρ i) :=
  (lowNormalCenteredFrequencyBump
    (lowNormalSixCenter (1 / 4 : ℝ) i) ρ hρ).hasCompactSupport

/-- The Hermitianized six-packet Fourier field at the chosen width. -/
noncomputable def lowNormalQuarterNarrowFourier
    (ρ : ℝ) (hρ : 0 < ρ) : NarrowV → Fin 3 → ℂ :=
  lowNormalSixPacketFourier (1 / 4 : ℝ)
    (lowNormalQuarterNarrowCutoff ρ hρ 0)
    (lowNormalQuarterNarrowCutoff ρ hρ 1)
    (lowNormalQuarterNarrowCutoff ρ hρ 2)

/-- The narrower Fourier field remains pointwise divergence-free. -/
theorem lowNormalQuarterNarrowFourier_divergence
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : NarrowV) :
    mixedDot ξ (lowNormalQuarterNarrowFourier ρ hρ ξ) = 0 :=
  lowNormalSixPacketFourier_divergence (1 / 4 : ℝ) _ _ _ ξ

/-- The narrower field retains exact conjugate-reflection reality. -/
theorem lowNormalQuarterNarrowFourier_reality
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : NarrowV) :
    lowNormalQuarterNarrowFourier ρ hρ (-ξ) =
      fun d => star (lowNormalQuarterNarrowFourier ρ hρ ξ d) := by
  exact lowNormalSixPacketFourier_reality (1 / 4 : ℝ) _ _ _ ξ

/-- The narrowed field is still smooth to every order. -/
theorem lowNormalQuarterNarrowFourier_contDiff
    (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiff ℝ ∞ (lowNormalQuarterNarrowFourier ρ hρ) :=
  lowNormalHermitianize_contDiff _
    (lowNormalPositiveThreePacketSum_contDiff (1 / 4 : ℝ) _ _ _
      (lowNormalQuarterNarrowCutoff_contDiff ρ hρ 0)
      (lowNormalQuarterNarrowCutoff_contDiff ρ hρ 1)
      (lowNormalQuarterNarrowCutoff_contDiff ρ hρ 2))

/-- All six narrowed Fourier packets together have compact support. -/
theorem lowNormalQuarterNarrowFourier_hasCompactSupport
    (ρ : ℝ) (hρ : 0 < ρ) :
    HasCompactSupport (lowNormalQuarterNarrowFourier ρ hρ) :=
  lowNormalHermitianize_hasCompactSupport _
    (lowNormalPositiveThreePacketSum_hasCompactSupport (1 / 4 : ℝ) _ _ _
      (lowNormalQuarterNarrowCutoff_hasCompactSupport ρ hρ 0)
      (lowNormalQuarterNarrowCutoff_hasCompactSupport ρ hρ 1)
      (lowNormalQuarterNarrowCutoff_hasCompactSupport ρ hρ 2))

/-- A genuine vector-valued Schwartz function for every chosen positive width. -/
noncomputable def lowNormalQuarterNarrowSchwartz
    (ρ : ℝ) (hρ : 0 < ρ) : 𝓢(NarrowV, Fin 3 → ℂ) :=
  (lowNormalQuarterNarrowFourier_hasCompactSupport ρ hρ).toSchwartzMap
    (lowNormalQuarterNarrowFourier_contDiff ρ hρ)

@[simp] theorem lowNormalQuarterNarrowSchwartz_apply
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : NarrowV) :
    lowNormalQuarterNarrowSchwartz ρ hρ ξ =
      lowNormalQuarterNarrowFourier ρ hρ ξ := rfl

/-- Negation exchanges each primary frequency center with its mirror. -/
private theorem lowNormalQuarterCenter_reflect_zero :
    lowNormalSixCenter (1 / 4 : ℝ) 3 =
      -(lowNormalSixCenter (1 / 4 : ℝ) 0) := by
  rw [(lowNormalSixCenter_reflected (1 / 4 : ℝ)).1,
    (lowNormalSixCenter_primary (1 / 4 : ℝ)).1]
  rfl

private theorem lowNormalQuarterCenter_reflect_one :
    lowNormalSixCenter (1 / 4 : ℝ) 4 =
      -(lowNormalSixCenter (1 / 4 : ℝ) 1) := by
  rw [(lowNormalSixCenter_reflected (1 / 4 : ℝ)).2.1,
    (lowNormalSixCenter_primary (1 / 4 : ℝ)).2.1]
  rfl

private theorem lowNormalQuarterCenter_reflect_two :
    lowNormalSixCenter (1 / 4 : ℝ) 5 =
      -(lowNormalSixCenter (1 / 4 : ℝ) 2) := by
  rw [(lowNormalSixCenter_reflected (1 / 4 : ℝ)).2.2,
    (lowNormalSixCenter_primary (1 / 4 : ℝ)).2.2]
  rfl

/-- No nonzero amplitude can occur outside all six radius-ρ frequency balls. -/
theorem lowNormalQuarterNarrowFourier_nonzero_center
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : NarrowV)
    (hU : lowNormalQuarterNarrowFourier ρ hρ ξ ≠ 0) :
    ∃ i : Fin 6, dist ξ (lowNormalSixCenter (1 / 4 : ℝ) i) < ρ := by
  by_contra hn
  push Not at hn
  have hZero (i : Fin 6) (x : NarrowV)
      (hdist : ρ ≤ dist x (lowNormalSixCenter (1 / 4 : ℝ) i)) :
      lowNormalQuarterNarrowCutoff ρ hρ i x = 0 := by
    by_contra hχ
    exact (not_lt.mpr hdist)
      (lowNormalQuarterNarrowCutoff_nonzero_ball ρ hρ i x hχ)
  have hp : lowNormalQuarterNarrowCutoff ρ hρ 0 ξ = 0 := hZero 0 ξ (hn 0)
  have hq : lowNormalQuarterNarrowCutoff ρ hρ 1 ξ = 0 := hZero 1 ξ (hn 1)
  have hr : lowNormalQuarterNarrowCutoff ρ hρ 2 ξ = 0 := hZero 2 ξ (hn 2)
  have hNegDist (i j : Fin 6)
      (hj : lowNormalSixCenter (1 / 4 : ℝ) j =
        -(lowNormalSixCenter (1 / 4 : ℝ) i)) :
      ρ ≤ dist (-ξ) (lowNormalSixCenter (1 / 4 : ℝ) i) := by
    have hEq : dist (-ξ) (lowNormalSixCenter (1 / 4 : ℝ) i) =
        dist ξ (lowNormalSixCenter (1 / 4 : ℝ) j) := by
      rw [hj]
      simpa only [neg_neg] using
        (dist_neg_neg ξ (-(lowNormalSixCenter (1 / 4 : ℝ) i)))
    rw [hEq]
    exact hn j
  have hpn : lowNormalQuarterNarrowCutoff ρ hρ 0 (-ξ) = 0 :=
    hZero 0 (-ξ) (hNegDist 0 3 lowNormalQuarterCenter_reflect_zero)
  have hqn : lowNormalQuarterNarrowCutoff ρ hρ 1 (-ξ) = 0 :=
    hZero 1 (-ξ) (hNegDist 1 4 lowNormalQuarterCenter_reflect_one)
  have hrn : lowNormalQuarterNarrowCutoff ρ hρ 2 (-ξ) = 0 :=
    hZero 2 (-ξ) (hNegDist 2 5 lowNormalQuarterCenter_reflect_two)
  -- The generic six-packet lemma uses pointwise negation notation,
  -- whereas the local cutoff hypotheses use Pi's negation instance.
  have hNeg : (-ξ : NarrowV) = (fun k => -ξ k) := by
    funext k
    simp only [Pi.neg_apply]
  have hVanish : lowNormalQuarterNarrowFourier ρ hρ ξ = fun _ => 0 := by
    apply lowNormalSixPacketFourier_zero_of_cutoffs_zero
      (1 / 4 : ℝ) _ _ _ ξ hp hq hr
    · exact hNeg ▸ hpn
    · exact hNeg ▸ hqn
    · exact hNeg ▸ hrn
  exact hU hVanish

/-- Width bounded by the old separation threshold supplies its proven
coordinatewise resonance classification for the new field. -/
theorem lowNormalQuarterNarrowFourier_nonzero_coordinateBall
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 / 4 : ℝ))
    (ξ : NarrowV) (hU : lowNormalQuarterNarrowFourier ρ hρ ξ ≠ 0) :
    ∃ i : Fin 6, lowNormalSixCenterCoordinateBall (1 / 4 : ℝ) i ξ := by
  obtain ⟨i, hi⟩ := lowNormalQuarterNarrowFourier_nonzero_center ρ hρ ξ hU
  refine ⟨i, ?_⟩
  intro d
  have hCoord : |ξ d - lowNormalSixCenter (1 / 4 : ℝ) i d| ≤
      dist ξ (lowNormalSixCenter (1 / 4 : ℝ) i) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, dist_eq_norm] using
      (norm_le_pi_norm (ξ - lowNormalSixCenter (1 / 4 : ℝ) i) d)
  exact lt_of_le_of_lt hCoord (lt_of_lt_of_le hi hSmall)

/-- All momentum-conserving nonzero triple interactions have coherent labels
and the independent frequencies lie in a product ball of the actual width.
This proves the support geometry without any sign claim for the new kernel. -/
theorem lowNormalQuarterNarrowFourier_coherent_pair_support
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 / 4 : ℝ))
    (p r : NarrowV)
    (hp : lowNormalQuarterNarrowFourier ρ hρ p ≠ 0)
    (hq : lowNormalQuarterNarrowFourier ρ hρ (middleFrequency p r) ≠ 0)
    (hr : lowNormalQuarterNarrowFourier ρ hρ r ≠ 0) :
    ∃ i j k : Fin 6,
      lowNormalCoherentCenters i j k ∧
      dist (p, r)
        (lowNormalSixCenter (1 / 4 : ℝ) i,
         lowNormalSixCenter (1 / 4 : ℝ) k) < ρ := by
  obtain ⟨i, hi⟩ := lowNormalQuarterNarrowFourier_nonzero_center ρ hρ p hp
  obtain ⟨j, hj⟩ := lowNormalQuarterNarrowFourier_nonzero_center ρ hρ
    (middleFrequency p r) hq
  obtain ⟨k, hk⟩ := lowNormalQuarterNarrowFourier_nonzero_center ρ hρ r hr
  have hBall (l : Fin 6) (x : NarrowV)
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
  refine ⟨i, j, k, hCoherent, ?_⟩
  simpa only [Prod.dist_eq, max_lt_iff] using And.intro hi hk

/-- The finite geometric center locus of *labeled coherent* momentum triples.
The next combinatorial bridge will identify it with the existing twelve-center
orbit defined in `FirstMonomialTriadLowQuarterUniformTube`. -/
def lowNormalQuarterLabeledCoherentPairSet : Set (NarrowV × NarrowV) :=
  {z | ∃ i j k : Fin 6,
    lowNormalCoherentCenters i j k ∧
      z = (lowNormalSixCenter (1 / 4 : ℝ) i,
           lowNormalSixCenter (1 / 4 : ℝ) k)}

/-- **Unconditional support localization for the new Schwartz field:**
nonzero values at all three momentum-conserving frequencies put the independent
pair in the open ρ-thickening of the finite coherent center locus. -/
theorem lowNormalQuarterNarrowFourier_support_in_coherent_thickening
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 / 4 : ℝ))
    (p r : NarrowV)
    (hp : lowNormalQuarterNarrowFourier ρ hρ p ≠ 0)
    (hq : lowNormalQuarterNarrowFourier ρ hρ (middleFrequency p r) ≠ 0)
    (hr : lowNormalQuarterNarrowFourier ρ hρ r ≠ 0) :
    (p, r) ∈ Metric.thickening ρ lowNormalQuarterLabeledCoherentPairSet := by
  obtain ⟨i, j, k, hcoh, hdist⟩ :=
    lowNormalQuarterNarrowFourier_coherent_pair_support ρ hρ hSmall p r hp hq hr
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(lowNormalSixCenter (1 / 4 : ℝ) i,
    lowNormalSixCenter (1 / 4 : ℝ) k), ?_, hdist⟩
  exact ⟨i, j, k, hcoh, rfl⟩

end
end PrimeTensor.FirstMonomialTriad

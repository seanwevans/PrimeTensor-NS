import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinStrongOverlapUniqueness
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
# Unrestricted overlap uniqueness for the actual finite Z³ Leray-Galerkin ODE

We remove the externally supplied compact-state radius from strong Galerkin
uniqueness. For any two genuinely differentiable coefficient paths on a
compact time interval, their images are compact and therefore bounded; the
previously verified bounded-ball uniqueness theorem then applies.

This yields uniqueness for any two half-open initial solution segments,
regardless of their durations or the viscosity parameter. It also proves
that a longer solution segment is a bona fide strong right extension of a
shorter one without a separate agreement assumption.

The result is the overlap-consistency input to the maximal-solution
construction, NOT itself a construction of a maximal solution or a proof
of a common lifespan. All fields remain the exact complete projected
complex Leray-Galerkin convolution.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev UnrestrictedIndex244 := thirdFullThreeBandZ3Index244

/-- Any two genuine strong finite Galerkin trajectories on a compact
interval automatically lie in ONE finite coefficient ball. The radius
may depend on the cutoff and on the two paths; no analytic or energy
inequality is used. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_compactPaths_commonBall244
    (mu a b : ℝ) (s : Finset UnrestrictedIndex244)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hAlphaODE : ∀ t ∈ Icc a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hBetaODE : ∀ t ∈ Icc a b,
      HasDerivAt beta
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (beta t)) t) :
    ∃ R : ℝ,
      (∀ t ∈ Icc a b, ‖alpha t‖ ≤ R) ∧
      (∀ t ∈ Icc a b, ‖beta t‖ ≤ R) := by
  let E := thirdFullThreeBandZ3GalerkinFiniteState244 s
  have hAlphaContinuous : ContinuousOn alpha (Icc a b) := by
    intro t ht
    exact (hAlphaODE t ht).continuousAt.continuousWithinAt
  have hBetaContinuous : ContinuousOn beta (Icc a b) := by
    intro t ht
    exact (hBetaODE t ht).continuousAt.continuousWithinAt
  have hCompactAlpha : IsCompact (alpha '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hAlphaContinuous
  have hCompactBeta : IsCompact (beta '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hBetaContinuous
  obtain ⟨R, hBound⟩ :=
    (hCompactAlpha.union hCompactBeta).isBounded.subset_closedBall (0 : E)
  refine ⟨R, ?_, ?_⟩
  · intro t ht
    have hMem : alpha t ∈ (alpha '' Icc a b) ∪ (beta '' Icc a b) :=
      Or.inl ⟨t, ht, rfl⟩
    have h := hBound hMem
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  · intro t ht
    have hMem : beta t ∈ (alpha '' Icc a b) ∪ (beta '' Icc a b) :=
      Or.inr ⟨t, ht, rfl⟩
    have h := hBound hMem
    simpa only [Metric.mem_closedBall, dist_zero_right] using h

/-- Unrestricted uniqueness on any shared closed time interval. Unlike
`uniqueOnCompactBall244`, the state bound is DERIVED automatically,
and no sign, analytic-window or viscosity-size condition is imposed. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_unrestrictedUniqueOnIcc244
    (mu a b : ℝ) (s : Finset UnrestrictedIndex244)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hAlphaODE : ∀ t ∈ Icc a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hBetaODE : ∀ t ∈ Icc a b,
      HasDerivAt beta
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (beta t)) t)
    (hInitial : alpha a = beta a) :
    Set.EqOn alpha beta (Icc a b) := by
  obtain ⟨R, hAlphaBound, hBetaBound⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteODE_compactPaths_commonBall244
      mu a b s alpha beta hAlphaODE hBetaODE
  exact thirdFullThreeBand_z3GalerkinFiniteODE_uniqueOnCompactBall244
    mu a b s alpha beta R hAlphaODE hBetaODE
    hAlphaBound hBetaBound hInitial

/-- Two exact finite Galerkin solutions with the same initial value agree
through every common half-open interval. This holds arbitrarily far beyond
the analytic window: the compactness argument is applied separately to
`[a,t]` for each time `t` in that overlap. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_unrestrictedOverlapUnique244
    (mu a b : ℝ) (s : Finset UnrestrictedIndex244)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hAlphaODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hBetaODE : ∀ t ∈ Ico a b,
      HasDerivAt beta
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (beta t)) t)
    (hInitial : alpha a = beta a) :
    Set.EqOn alpha beta (Ico a b) := by
  intro t ht
  have hSubset : Icc a t ⊆ Ico a b := by
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt hz.2 ht.2⟩
  have hEqual :=
    thirdFullThreeBand_z3GalerkinFiniteODE_unrestrictedUniqueOnIcc244
      mu a t s alpha beta
      (fun z hz => hAlphaODE z (hSubset hz))
      (fun z hz => hBetaODE z (hSubset hz)) hInitial
  exact hEqual ⟨ht.1, le_rfl⟩

/-- Initial segments with DIFFERENT endpoint times also agree on their
common lifespan. Neither endpoint needs to lie within the analytic window. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_differentEndsAgree244
    (mu a b c : ℝ) (s : Finset UnrestrictedIndex244)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hAlphaODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hBetaODE : ∀ t ∈ Ico a c,
      HasDerivAt beta
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (beta t)) t)
    (hInitial : alpha a = beta a) :
    Set.EqOn alpha beta (Ico a (min b c)) := by
  have hSubB : Ico a (min b c) ⊆ Ico a b := by
    intro t ht
    exact ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hSubC : Ico a (min b c) ⊆ Ico a c := by
    intro t ht
    exact ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  exact thirdFullThreeBand_z3GalerkinFiniteODE_unrestrictedOverlapUnique244
    mu a (min b c) s alpha beta
    (fun t ht => hAlphaODE t (hSubB ht))
    (fun t ht => hBetaODE t (hSubC ht)) hInitial

/-- Any longer genuine initial solution segment is automatically an
extension of every shorter one with the SAME initial condition. Agreement
is proved, not added as an extra hypothesis. The full ODE holds through
the shorter endpoint because it holds for the longer solution. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_longerSegment_extends244
    (mu a b c : ℝ) (hab : a < b) (hbc : b < c)
    (s : Finset UnrestrictedIndex244)
    (alpha beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hAlphaODE : ∀ t ∈ Ico a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t)
    (hBetaODE : ∀ t ∈ Ico a c,
      HasDerivAt beta
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (beta t)) t)
    (hInitial : alpha a = beta a) :
    thirdFullThreeBandZ3GalerkinStrongRightExtendible244 mu a b s alpha := by
  have hAgreement : Set.EqOn alpha beta (Ico a b) := by
    have hSame := thirdFullThreeBand_z3GalerkinFiniteODE_differentEndsAgree244
      mu a b c s alpha beta hAlphaODE hBetaODE hInitial
    have hMin : min b c = b := min_eq_left hbc.le
    simpa only [hMin] using hSame
  refine ⟨c - b, sub_pos.mpr hbc, beta, ?_, ?_⟩
  · intro t ht
    exact (hAgreement ht).symm
  · have hTime : b + (c - b) = c := by ring
    simpa only [hTime] using hBetaODE

end
end PrimeTensor.FirstMonomialTriad

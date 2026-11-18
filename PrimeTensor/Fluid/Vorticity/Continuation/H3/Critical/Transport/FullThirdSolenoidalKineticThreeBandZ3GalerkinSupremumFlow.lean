import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinUnrestrictedOverlap
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic

/-!
# The actual finite Z³ Galerkin flow exists across the common analytic horizon

All solution segments here solve the *exact* viscous plus full Leray-Galerkin
polynomial field. We construct the canonical union of every initial strong
segment using the proved unrestricted overlap uniqueness theorem.

The endpoint supremum is capped at the analytic horizon a + log(10/9)/100.
If the supremum were strictly shorter, the verified strong restart would
supply a larger segment, contradicting the least-upper-bound property.
Consequently the canonical union solves the ODE up to the horizon; one last
Picard restart gives a strong solution THROUGH its closed right endpoint.

Neither a maximal trajectory nor a uniform local Picard time is postulated.
The theorem concerns finite Galerkin systems, not the infinite-dimensional
Navier--Stokes continuation problem.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev SupIndex244 := thirdFullThreeBandZ3Index244

/-- A genuine positive-lifespan strong initial solution segment. -/
structure thirdFullThreeBandZ3GalerkinStrongSegment244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s) where
  endpoint : ℝ
  start_lt : a < endpoint
  curve : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s
  initial : curve a = x0
  ode : ∀ t ∈ Ico a endpoint,
    HasDerivAt curve
      (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (curve t)) t

/-- Picard provides a genuinely nonempty family of initial segments. -/
theorem thirdFullThreeBand_z3GalerkinStrongSegment_nonempty244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    Nonempty (thirdFullThreeBandZ3GalerkinStrongSegment244 mu a s x0) := by
  obtain ⟨alpha, hInit, delta, hDelta, hODE⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteField_exists_local244 mu a s x0
  let b : ℝ := a + delta / 2
  have hab : a < b := by dsimp [b]; linarith
  refine ⟨{
    endpoint := b
    start_lt := hab
    curve := alpha
    initial := hInit
    ode := ?_
  }⟩
  intro t ht
  apply hODE t
  dsimp [b] at ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- A fixed local Picard segment supplies values before the initial time,
so the eventual canonical union retains a genuine two-sided derivative at a. -/
noncomputable def thirdFullThreeBandZ3GalerkinBaseSegment244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    thirdFullThreeBandZ3GalerkinStrongSegment244 mu a s x0 :=
  Classical.choice (thirdFullThreeBand_z3GalerkinStrongSegment_nonempty244 mu a s x0)

/-- Reachable times are covered by at least one genuine initial segment. -/
def thirdFullThreeBandZ3GalerkinReachable244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (t : ℝ) : Prop :=
  a ≤ t ∧ ∃ q : thirdFullThreeBandZ3GalerkinStrongSegment244 mu a s x0,
    t < q.endpoint

/-- Select a genuine segment covering each reachable time. The choice is
canonical at the level of values by unrestricted overlap uniqueness. -/
noncomputable def thirdFullThreeBandZ3GalerkinCanonicalUnion244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (t : ℝ) : thirdFullThreeBandZ3GalerkinFiniteState244 s := by
  classical
  exact if h : thirdFullThreeBandZ3GalerkinReachable244 mu a s x0 t then
    (Classical.choose h.2).curve t
  else
    (thirdFullThreeBandZ3GalerkinBaseSegment244 mu a s x0).curve t

/-- No two local Picard segments can assign different values to the
canonical union on their shared interval. -/
theorem thirdFullThreeBand_z3GalerkinCanonicalUnion_agrees244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (q : thirdFullThreeBandZ3GalerkinStrongSegment244 mu a s x0)
    (t : ℝ) (ht : t ∈ Ico a q.endpoint) :
    thirdFullThreeBandZ3GalerkinCanonicalUnion244 mu a s x0 t = q.curve t := by
  classical
  have hReach : thirdFullThreeBandZ3GalerkinReachable244 mu a s x0 t :=
    ⟨ht.1, ⟨q, ht.2⟩⟩
  unfold thirdFullThreeBandZ3GalerkinCanonicalUnion244
  rw [dif_pos hReach]
  let q' : thirdFullThreeBandZ3GalerkinStrongSegment244 mu a s x0 :=
    Classical.choose hReach.2
  have hEnd : t < q'.endpoint := Classical.choose_spec hReach.2
  have hInit : q.curve a = q'.curve a := by rw [q.initial, q'.initial]
  have hEqual := thirdFullThreeBand_z3GalerkinFiniteODE_differentEndsAgree244
    mu a q.endpoint q'.endpoint s q.curve q'.curve q.ode q'.ode hInit
  exact (hEqual ⟨ht.1, lt_min ht.2 hEnd⟩).symm

/-- The canonical union starts at the prescribed finite Fourier state. -/
theorem thirdFullThreeBand_z3GalerkinCanonicalUnion_initial244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    thirdFullThreeBandZ3GalerkinCanonicalUnion244 mu a s x0 a = x0 := by
  let q := thirdFullThreeBandZ3GalerkinBaseSegment244 mu a s x0
  have hAgree := thirdFullThreeBand_z3GalerkinCanonicalUnion_agrees244
    mu a s x0 q a ⟨le_rfl, q.start_lt⟩
  exact hAgree.trans q.initial

/-- The canonical union solves the full strong ODE at EVERY reachable
nonnegative time. At a, the fixed Picard segment supplies the left
neighbourhood, so this proves `HasDerivAt`, not merely a one-sided ODE. -/
theorem thirdFullThreeBand_z3GalerkinCanonicalUnion_strong244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (t : ℝ)
    (ht : thirdFullThreeBandZ3GalerkinReachable244 mu a s x0 t) :
    HasDerivAt
      (thirdFullThreeBandZ3GalerkinCanonicalUnion244 mu a s x0)
      (thirdFullThreeBandZ3GalerkinFiniteField244 mu s
        (thirdFullThreeBandZ3GalerkinCanonicalUnion244 mu a s x0 t)) t := by
  classical
  by_cases hat : a < t
  · obtain ⟨q, hEnd⟩ := ht.2
    have hAt := thirdFullThreeBand_z3GalerkinCanonicalUnion_agrees244
      mu a s x0 q t ⟨ht.1, hEnd⟩
    have hEvent :
        thirdFullThreeBandZ3GalerkinCanonicalUnion244 mu a s x0
          =ᶠ[nhds t] q.curve := by
      filter_upwards [Ioo_mem_nhds hat hEnd] with z hz
      exact thirdFullThreeBand_z3GalerkinCanonicalUnion_agrees244
        mu a s x0 q z ⟨hz.1.le, hz.2⟩
    have hDeriv := (q.ode t ⟨ht.1, hEnd⟩).congr_of_eventuallyEq hEvent
    rw [hAt]
    exact hDeriv
  · have hteq : t = a := le_antisymm (le_of_not_gt hat) ht.1
    subst t
    let q := thirdFullThreeBandZ3GalerkinBaseSegment244 mu a s x0
    have hAt := thirdFullThreeBand_z3GalerkinCanonicalUnion_agrees244
      mu a s x0 q a ⟨le_rfl, q.start_lt⟩
    have hEvent :
        thirdFullThreeBandZ3GalerkinCanonicalUnion244 mu a s x0
          =ᶠ[nhds a] q.curve := by
      filter_upwards [isOpen_Iio.mem_nhds q.start_lt] with z hz
      by_cases haz : a ≤ z
      · exact thirdFullThreeBand_z3GalerkinCanonicalUnion_agrees244
          mu a s x0 q z ⟨haz, hz⟩
      · have hn : ¬ thirdFullThreeBandZ3GalerkinReachable244 mu a s x0 z := by
          intro hr
          exact haz hr.1
        simp only [thirdFullThreeBandZ3GalerkinCanonicalUnion244, dif_neg hn, q]
    have hDeriv := (q.ode a ⟨le_rfl, q.start_lt⟩).congr_of_eventuallyEq hEvent
    rw [hAt]
    exact hDeriv

/-- The common target time depends only on the initial time and the
cutoff-independent analytic radius reserve. -/
def thirdFullThreeBandZ3GalerkinCommonHorizon244 (a : ℝ) : ℝ :=
  a + thirdFullThreeBandZ3GalerkinMovingRadiusWindow244

theorem thirdFullThreeBand_z3GalerkinCommonHorizon_gt244 (a : ℝ) :
    a < thirdFullThreeBandZ3GalerkinCommonHorizon244 a := by
  unfold thirdFullThreeBandZ3GalerkinCommonHorizon244
  linarith [thirdFullThreeBand_z3MovingRadiusWindow_pos244]

/-- Bound the endpoint set to obtain an ordinary real supremum. -/
def thirdFullThreeBandZ3GalerkinCappedEndpoints244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s) : Set ℝ :=
  {b | (∃ q : thirdFullThreeBandZ3GalerkinStrongSegment244 mu a s x0,
    q.endpoint = b) ∧ b ≤ thirdFullThreeBandZ3GalerkinCommonHorizon244 a}

/-- The capped endpoint set is nonempty even when the initial Picard
segment lasts longer than the common window: shorten the segment. -/
theorem thirdFullThreeBand_z3GalerkinCappedEndpoints_nonempty244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    (thirdFullThreeBandZ3GalerkinCappedEndpoints244 mu a s x0).Nonempty := by
  let q := thirdFullThreeBandZ3GalerkinBaseSegment244 mu a s x0
  let b := min q.endpoint (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)
  have hab : a < b := lt_min q.start_lt
    (thirdFullThreeBand_z3GalerkinCommonHorizon_gt244 a)
  let q' : thirdFullThreeBandZ3GalerkinStrongSegment244 mu a s x0 := {
    endpoint := b
    start_lt := hab
    curve := q.curve
    initial := q.initial
    ode := by
      intro t ht
      apply q.ode t
      exact ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  }
  refine ⟨b, ?_⟩
  exact ⟨⟨q', rfl⟩, min_le_right _ _⟩

/-- The cap is an explicit upper bound on all capped endpoints. -/
theorem thirdFullThreeBand_z3GalerkinCappedEndpoints_bddAbove244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    BddAbove (thirdFullThreeBandZ3GalerkinCappedEndpoints244 mu a s x0) := by
  refine ⟨thirdFullThreeBandZ3GalerkinCommonHorizon244 a, ?_⟩
  intro b hb
  exact hb.2

/-- Canonical maximal candidate time, capped at the universal horizon. -/
noncomputable def thirdFullThreeBandZ3GalerkinCappedSup244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s) : ℝ :=
  sSup (thirdFullThreeBandZ3GalerkinCappedEndpoints244 mu a s x0)

/-- The capped supremum has a positive lifespan. -/
theorem thirdFullThreeBand_z3GalerkinCappedSup_start_lt244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    a < thirdFullThreeBandZ3GalerkinCappedSup244 mu a s x0 := by
  obtain ⟨b, hb⟩ := thirdFullThreeBand_z3GalerkinCappedEndpoints_nonempty244 mu a s x0
  obtain ⟨⟨q, hq⟩, hCap⟩ := hb
  have hle : b ≤ thirdFullThreeBandZ3GalerkinCappedSup244 mu a s x0 :=
    le_csSup (thirdFullThreeBand_z3GalerkinCappedEndpoints_bddAbove244 mu a s x0)
      ⟨⟨q, hq⟩, hCap⟩
  exact lt_of_lt_of_le (hq ▸ q.start_lt) hle

/-- The capped supremum never exceeds the horizon. -/
theorem thirdFullThreeBand_z3GalerkinCappedSup_le_horizon244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    thirdFullThreeBandZ3GalerkinCappedSup244 mu a s x0 ≤
      thirdFullThreeBandZ3GalerkinCommonHorizon244 a := by
  apply csSup_le (thirdFullThreeBand_z3GalerkinCappedEndpoints_nonempty244 mu a s x0)
  intro b hb
  exact hb.2

/-- Every time strictly below the capped supremum is covered by a real
strong segment; the canonical union therefore solves the ODE there. -/
theorem thirdFullThreeBand_z3GalerkinReachable_belowCappedSup244
    (mu a : ℝ) (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (t : ℝ) (hat : a ≤ t)
    (ht : t < thirdFullThreeBandZ3GalerkinCappedSup244 mu a s x0) :
    thirdFullThreeBandZ3GalerkinReachable244 mu a s x0 t := by
  obtain ⟨b, hb, htb⟩ := exists_lt_of_lt_csSup
    (thirdFullThreeBand_z3GalerkinCappedEndpoints_nonempty244 mu a s x0) ht
  obtain ⟨⟨q, hq⟩, _⟩ := hb
  have hqTime : t < q.endpoint := by simpa only [hq] using htb
  exact ⟨hat, ⟨q, hqTime⟩⟩

/-- The crucial supremum contradiction: if the canonical union stopped
strictly before the universal horizon, the strong seam restart constructs
a capped endpoint strictly larger than the least upper bound. -/
theorem thirdFullThreeBand_z3GalerkinCappedSup_eq_horizon244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x0) < 100) :
    thirdFullThreeBandZ3GalerkinCappedSup244 mu a s x0 =
      thirdFullThreeBandZ3GalerkinCommonHorizon244 a := by
  let B := thirdFullThreeBandZ3GalerkinCappedSup244 mu a s x0
  let T := thirdFullThreeBandZ3GalerkinCommonHorizon244 a
  have hAB : a < B := thirdFullThreeBand_z3GalerkinCappedSup_start_lt244 mu a s x0
  have hBTle : B ≤ T := thirdFullThreeBand_z3GalerkinCappedSup_le_horizon244 mu a s x0
  apply le_antisymm hBTle
  by_contra hNot
  have hBT : B < T := lt_of_not_ge hNot
  let alpha := thirdFullThreeBandZ3GalerkinCanonicalUnion244 mu a s x0
  have hAt : alpha a = x0 := thirdFullThreeBand_z3GalerkinCanonicalUnion_initial244 mu a s x0
  have hODE : ∀ t ∈ Ico a B,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t := by
    intro t ht
    exact thirdFullThreeBand_z3GalerkinCanonicalUnion_strong244 mu a s x0 t
      (thirdFullThreeBand_z3GalerkinReachable_belowCappedSup244
        mu a s x0 t ht.1 ht.2)
  have hWindow : B - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 := by
    dsimp [T, thirdFullThreeBandZ3GalerkinCommonHorizon244] at hBTle
    linarith
  have hInit : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100 := by
    simpa only [hAt] using hInitial
  obtain ⟨delta, hDelta, gamma, hGammaStart, _hAgree, hGammaODE,
      _hHigh, _hSpeed⟩ :=
    thirdFullThreeBand_z3GalerkinPreterminalGluedStrongRestart244
      mu a B hAB hmu hmuMax hWindow s alpha hODE hInit
  let b' : ℝ := min (B + delta / 2) T
  have hBb : B < b' := lt_min (by linarith) hBT
  have hbT : b' ≤ T := min_le_right _ _
  have hbDelta : b' ≤ B + delta := by
    dsimp [b']
    have h := min_le_left (B + delta / 2) T
    linarith
  let q : thirdFullThreeBandZ3GalerkinStrongSegment244 mu a s x0 := {
    endpoint := b'
    start_lt := lt_trans hAB hBb
    curve := gamma
    initial := by simpa only [hAt] using hGammaStart
    ode := by
      intro t ht
      exact hGammaODE t ⟨ht.1, lt_of_lt_of_le ht.2 hbDelta⟩
  }
  have hbMem : b' ∈ thirdFullThreeBandZ3GalerkinCappedEndpoints244 mu a s x0 :=
    ⟨⟨q, rfl⟩, hbT⟩
  have hUpper : b' ≤ B :=
    le_csSup (thirdFullThreeBand_z3GalerkinCappedEndpoints_bddAbove244 mu a s x0) hbMem
  exact (not_le_of_gt hBb) hUpper

/-- Actual finite Leray-Galerkin existence on a cutoff-independent CLOSED
interval. It is constructed from Picard segments via their compatible
canonical union and the capped-endpoint supremum, then restarted at the
horizon to obtain an honest derivative at its final time. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_exists_commonHorizon244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset SupIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x0) < 100) :
    ∃ gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
      gamma a = x0 ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        HasDerivAt gamma
          (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        thirdFullThreeBandZ3GalerkinWienerMass244
          (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t)) ≤ 100) := by
  classical
  let T := thirdFullThreeBandZ3GalerkinCommonHorizon244 a
  let alpha := thirdFullThreeBandZ3GalerkinCanonicalUnion244 mu a s x0
  have hAT : a < T := thirdFullThreeBand_z3GalerkinCommonHorizon_gt244 a
  have hSup : thirdFullThreeBandZ3GalerkinCappedSup244 mu a s x0 = T :=
    thirdFullThreeBand_z3GalerkinCappedSup_eq_horizon244
      mu a hmu hmuMax s x0 hInitial
  have hAlphaStart : alpha a = x0 :=
    thirdFullThreeBand_z3GalerkinCanonicalUnion_initial244 mu a s x0
  have hAlphaODE : ∀ t ∈ Ico a T,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t := by
    intro t ht
    apply thirdFullThreeBand_z3GalerkinCanonicalUnion_strong244 mu a s x0 t
    apply thirdFullThreeBand_z3GalerkinReachable_belowCappedSup244
      mu a s x0 t ht.1
    simpa only [hSup] using ht.2
  have hWindow : T - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 := by
    dsimp [T, thirdFullThreeBandZ3GalerkinCommonHorizon244]
    simp
  have hInit : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha a)) < 100 := by
    simpa only [hAlphaStart] using hInitial
  obtain ⟨delta, hDelta, gamma, hGammaStart, _hAgreement, hGammaODE,
      _hHigh, _hSpeed⟩ :=
    thirdFullThreeBand_z3GalerkinPreterminalGluedStrongRestart244
      mu a T hAT hmu hmuMax hWindow s alpha hAlphaODE hInit
  have hStrong : ∀ t ∈ Icc a T,
      HasDerivAt gamma
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)) t := by
    intro t ht
    apply hGammaODE t
    exact ⟨ht.1, by linarith [ht.2]⟩
  let u : ℝ → SupIndex244 → EuclideanSpace ℂ (Fin 3) :=
    fun t => thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t)
  have hContinuous : ∀ n ∈ s, ContinuousOn (fun t : ℝ => u t n) (Icc a T) := by
    intro n hn t ht
    exact (thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_continuousAt244
      s gamma t (hStrong t ht).continuousAt n hn).continuousWithinAt
  have hCoordinates : ∀ n ∈ s, ∀ t ∈ Ico a T,
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t := by
    intro n hn t ht
    exact thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_hasDerivAt244
      mu s gamma t (hStrong t ⟨ht.1, ht.2.le⟩) n hn
  have hGammaInitial : gamma a = x0 := hGammaStart.trans hAlphaStart
  have hMoving := thirdFullThreeBand_z3MovingBall_cutoffFreePersistence244
    mu a T hmu hWindow s u hContinuous hCoordinates
    (by simpa only [u, hGammaInitial] using hInitial)
  refine ⟨gamma, hGammaInitial, hStrong, ?_⟩
  simpa only [u] using hMoving

end
end PrimeTensor.FirstMonomialTriad

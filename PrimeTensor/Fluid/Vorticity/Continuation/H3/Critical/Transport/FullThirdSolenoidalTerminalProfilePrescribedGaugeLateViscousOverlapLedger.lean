import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousSecondarySquaredTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The first and secondary physical PDE clocks: separation or overlap

The constructive secondary clock and the primary finite-band PDE clock both
charge the SAME terminal interval integral of actual full H3 dissipation.
Their separate charges cannot simply be added. A sum is legitimate if their
physical intervals are ordered and disjoint. If the combined charges exceed
the terminal budget, the intervals must overlap in the strict time sense.

This file proves the exact two-interval integral lemma, its overlap-or-charge
corollary and the physical Navier--Stokes specialization on the ACTUAL two
clock certificates. The secondary certificate may arise from the previously
proved constructive square-root tail branch, but this theorem does not
assume that branch is present at every cofinal index. The current cofinal
squared-tail theorem does not retain the primary height at its late point;
that height must be supplied to reconstruct the primary interval.

No independent dissipation cost, terminal-uniform rate estimate, or
Navier--Stokes regularity is inferred from possibly overlapping windows.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Two nonoverlapping positive-time intervals carry additive costs in
ONE real terminal integral. The gap between them is nonnegative and may
carry additional physical dissipation, but is not charged here. -/
theorem thirdFull_scalar_orderedTwoWindows_additiveTailCharge244
    (f : ℝ → ℝ) (m T r s eta theta A H : ℝ)
    (hInt : IntervalIntegrable f volume m T)
    (hmT : m ≤ T)
    (hPos : ∀ x : ℝ, 0 ≤ f x)
    (hmr : m ≤ r) (heta : 0 ≤ eta)
    (hSep : r + eta ≤ s) (htheta : 0 ≤ theta)
    (hEnd : s + theta ≤ T)
    (hFirst : eta * A ≤ ∫ x in r..(r + eta), f x ∂volume)
    (hSecond : theta * H ≤ ∫ x in s..(s + theta), f x ∂volume) :
    eta * A + theta * H ≤ ∫ x in m..T, f x ∂volume := by
  have hrs : r ≤ s :=
    (le_add_of_nonneg_right heta).trans hSep
  have hms : m ≤ s := hmr.trans hrs
  have hse : s ≤ s + theta := le_add_of_nonneg_right htheta
  have hin (x y : ℝ) (hmx : m ≤ x) (hxy : x ≤ y)
      (hyT : y ≤ T) : IntervalIntegrable f volume x y := by
    apply hInt.mono_set
    intro z hz
    have hzIcc : z ∈ Set.Icc x y := by
      simpa only [Set.uIcc_of_le hxy] using hz
    have hzMain : z ∈ Set.Icc m T :=
      ⟨hmx.trans hzIcc.1, hzIcc.2.trans hyT⟩
    simpa only [Set.uIcc_of_le hmT] using hzMain
  have hIntRS : IntervalIntegrable f volume r s :=
    hin r s hmr hrs (hse.trans hEnd)
  have hIntSE : IntervalIntegrable f volume s (s + theta) :=
    hin s (s + theta) hms hse hEnd
  have hAErs : 0 ≤ᵐ[volume.restrict (Set.Ioc r s)] f := by
    filter_upwards [] with x
    exact hPos x
  have hAEmain : 0 ≤ᵐ[volume.restrict (Set.Ioc m T)] f := by
    filter_upwards [] with x
    exact hPos x
  have hExtend :
      (∫ x in r..(r + eta), f x ∂volume) ≤
        ∫ x in r..s, f x ∂volume :=
    intervalIntegral.integral_mono_interval
      le_rfl (le_add_of_nonneg_right heta) hSep hAErs hIntRS
  have hAdjacent :
      (∫ x in r..s, f x ∂volume) +
        (∫ x in s..(s + theta), f x ∂volume) =
          ∫ x in r..(s + theta), f x ∂volume :=
    intervalIntegral.integral_add_adjacent_intervals hIntRS hIntSE
  have hFull :
      (∫ x in r..(s + theta), f x ∂volume) ≤
        ∫ x in m..T, f x ∂volume :=
    intervalIntegral.integral_mono_interval
      hmr (hrs.trans hse) hEnd hAEmain hInt
  calc
    eta * A + theta * H ≤
        (∫ x in r..(r + eta), f x ∂volume) +
          (∫ x in s..(s + theta), f x ∂volume) :=
      add_le_add hFirst hSecond
    _ ≤ (∫ x in r..s, f x ∂volume) +
        (∫ x in s..(s + theta), f x ∂volume) := by
      simpa only [add_comm] using
        (add_le_add_right hExtend
          (∫ x in s..(s + theta), f x ∂volume))
    _ = ∫ x in r..(s + theta), f x ∂volume := hAdjacent
    _ ≤ ∫ x in m..T, f x ∂volume := hFull

/-- Without an ordering assumption, two actual positive-time persistence
windows either have an additive terminal cost or overlap. The overlap means
that their OPEN interiors intersect; merely meeting at an endpoint falls
in the additive (disjoint) case. -/
theorem thirdFull_scalar_twoWindows_overlapOrAdditiveTailCharge244
    (f : ℝ → ℝ) (m T r s eta theta A H : ℝ)
    (hInt : IntervalIntegrable f volume m T)
    (hmT : m ≤ T) (hPos : ∀ x : ℝ, 0 ≤ f x)
    (hmr : m ≤ r) (hms : m ≤ s)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hrEnd : r + eta ≤ T) (hsEnd : s + theta ≤ T)
    (hFirst : eta * A ≤ ∫ x in r..(r + eta), f x ∂volume)
    (hSecond : theta * H ≤ ∫ x in s..(s + theta), f x ∂volume) :
    eta * A + theta * H ≤ ∫ x in m..T, f x ∂volume ∨
      (r < s + theta ∧ s < r + eta) := by
  by_cases hLeft : r + eta ≤ s
  · left
    exact thirdFull_scalar_orderedTwoWindows_additiveTailCharge244
      f m T r s eta theta A H hInt hmT hPos hmr heta hLeft htheta
      hsEnd hFirst hSecond
  by_cases hRight : s + theta ≤ r
  · left
    have hReverse := thirdFull_scalar_orderedTwoWindows_additiveTailCharge244
      f m T s r theta eta H A hInt hmT hPos hms htheta hRight heta
      hrEnd hSecond hFirst
    simpa only [add_comm] using hReverse
  · right
    exact ⟨lt_of_not_ge hRight, lt_of_not_ge hLeft⟩

/-- If the certified sum of local costs exceeds the terminal budget,
non-disjointness is forced geometrically, with no double counting. -/
theorem thirdFull_scalar_twoWindows_overBudget_forcesOverlap244
    (f : ℝ → ℝ) (m T r s eta theta A H : ℝ)
    (hInt : IntervalIntegrable f volume m T)
    (hmT : m ≤ T) (hPos : ∀ x : ℝ, 0 ≤ f x)
    (hmr : m ≤ r) (hms : m ≤ s)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hrEnd : r + eta ≤ T) (hsEnd : s + theta ≤ T)
    (hFirst : eta * A ≤ ∫ x in r..(r + eta), f x ∂volume)
    (hSecond : theta * H ≤ ∫ x in s..(s + theta), f x ∂volume)
    (hOver : (∫ x in m..T, f x ∂volume) < eta * A + theta * H) :
    r < s + theta ∧ s < r + eta := by
  rcases thirdFull_scalar_twoWindows_overlapOrAdditiveTailCharge244
      f m T r s eta theta A H hInt hmT hPos hmr hms heta htheta
      hrEnd hsEnd hFirst hSecond with hCost | hOverlap
  · exact False.elim ((not_lt_of_ge hCost) hOver)
  · exact hOverlap

/-- A primary ACTUAL finite-band PDE clock and a constructive secondary
actual physical PDE clock either pay ADDITIVELY from one terminal viscous
integral, or must have intersecting interiors in physical time. This is a
conditional two-clock conclusion: the currently retained squared-tail
cofinal statement does not by itself expose the primary cutoff spike. -/
theorem thirdFullPhysical_primarySecondaryPDEClocks_overlapOrAdditiveCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m r P V : ℝ) (J : ℕ)
    (hm : m ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo m T)
    (hP : 0 < P) (hV : 0 < V)
    (hPrimary : V < P * h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r))
    (sState sSource h : ℝ)
    (hsState : sState ∈ Set.Ioo m T)
    (hsSource : sSource ∈ Set.Ioo m T)
    (hSecondary : ThirdFullLateSecondaryPDEClock244
      hH3 m sState sSource h) :
    ∃ (s eta1 eta2 : ℝ),
      (s = sState ∨ s = sSource) ∧
      0 < eta1 ∧ 0 < eta2 ∧
      r + eta1 < T ∧ s + eta2 < T ∧
      (eta1 * (V / (2 * P)) + eta2 * (h / 2) ≤
        ∫ x in m..T, velocityH3DissipationAt u x ∂volume ∨
       (r < s + eta2 ∧ s < r + eta1)) := by
  let D : ℝ → ℝ := velocityH3DissipationAt u
  obtain ⟨_pSource, _pState, eta1, _hpSource, _hpState, _hEq1,
      heta1, hend1, hFloor1, _hTail1⟩ :=
    thirdFullPhysical_lateLowRadialSpike_explicitPDEClock244
      hH3 hClass hDInt m r P V J hm hr hP hV hPrimary
  rcases hSecondary with ⟨s, hChoice, _J2, _zSource, _zState, eta2,
      _hzSource, _hzState, _hEq2, heta2, hend2, hFloor2, _hTail2⟩
  have hs : s ∈ Set.Ioo m T := by
    rcases hChoice with rfl | rfl
    · exact hsState
    · exact hsSource
  have hDtail : IntervalIntegrable D volume m T := by
    apply hDInt.mono_set
    intro x hx
    have hx' : x ∈ Set.Icc m T := by
      simpa only [Set.uIcc_of_le hm.2.le] using hx
    have hx'' : x ∈ Set.Icc a T :=
      ⟨hm.1.le.trans hx'.1, hx'.2⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hx''
  have hDwin (x eta : ℝ) (hmx : m ≤ x)
      (heta : 0 ≤ eta) (hend : x + eta ≤ T) :
      IntervalIntegrable D volume x (x + eta) := by
    apply hDtail.mono_set
    intro z hz
    have hz' : z ∈ Set.Icc x (x + eta) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right heta)] using hz
    have hz'' : z ∈ Set.Icc m T :=
      ⟨hmx.trans hz'.1, hz'.2.trans hend⟩
    simpa only [Set.uIcc_of_le hm.2.le] using hz''
  have hCharge1 : eta1 * (V / (2 * P)) ≤
      ∫ x in r..(r + eta1), D x ∂volume := by
    have hDint1 := hDwin r eta1 hr.1.le heta1.le hend1.le
    have hIntegral :
        (∫ _x in r..(r + eta1), V / (2 * P) ∂volume) ≤
          ∫ x in r..(r + eta1), D x ∂volume := by
      apply intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right heta1.le)
        intervalIntegrable_const hDint1
      intro x hx
      exact (hFloor1 x hx).2.le
    calc
      eta1 * (V / (2 * P)) =
          ∫ _x in r..(r + eta1), V / (2 * P) ∂volume := by
        simp [mul_comm] <;> ring
      _ ≤ ∫ x in r..(r + eta1), D x ∂volume := hIntegral
  have hCharge2 : eta2 * (h / 2) ≤
      ∫ x in s..(s + eta2), D x ∂volume := by
    have hDint2 := hDwin s eta2 hs.1.le heta2.le hend2.le
    have hIntegral :
        (∫ _x in s..(s + eta2), h / 2 ∂volume) ≤
          ∫ x in s..(s + eta2), D x ∂volume := by
      apply intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right heta2.le)
        intervalIntegrable_const hDint2
      intro x hx
      exact (hFloor2 x hx).2.le
    calc
      eta2 * (h / 2) =
          ∫ _x in s..(s + eta2), h / 2 ∂volume := by
        simp [mul_comm] <;> ring
      _ ≤ ∫ x in s..(s + eta2), D x ∂volume := hIntegral
  have hBoth := thirdFull_scalar_twoWindows_overlapOrAdditiveTailCharge244
    D m T r s eta1 eta2 (V / (2 * P)) (h / 2)
    hDtail hm.2.le (velocityH3DissipationAt_nonneg u)
    hr.1.le hs.1.le heta1.le heta2.le hend1.le hend2.le
    hCharge1 hCharge2
  exact ⟨s, eta1, eta2, hChoice, heta1, heta2, hend1, hend2, hBoth⟩

/-- The constructive reciprocal-square-root two-slice branch produces the
secondary clock automatically. If the original primary finite-band spike is
also retained at r, the resulting TWO actual physical windows have the
precise additive-charge OR overlap alternative, without assuming either. -/
theorem thirdFullPhysical_constructiveTwoSlice_dualClockOverlapGate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m r P V : ℝ) (J : ℕ)
    (hm : m ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo m T)
    (hP : 0 < P) (hV : 0 < V)
    (hPrimary : V < P * h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r))
    (sState sSource B R E : ℝ)
    (hsState : sState ∈ Set.Ioo m T)
    (hsSource : sSource ∈ Set.Ioo m T)
    (hB : 0 < B) (hR : 0 < R) (hE : 0 ≤ E)
    (hRate : (V / (2 * P)) ^ 2 ≤
      R * (E + 3 * velocityH3DissipationAt u sState) *
        (E + 3 * velocityH3DissipationAt u sSource) * B)
    (hGap : 4 * R * B * E ^ 2 < (V / (2 * P)) ^ 2) :
    ∃ (s eta1 eta2 : ℝ),
      (s = sState ∨ s = sSource) ∧
      0 < eta1 ∧ 0 < eta2 ∧
      r + eta1 < T ∧ s + eta2 < T ∧
      (eta1 * (V / (2 * P)) +
          eta2 * ((V / (2 * P)) / (24 * Real.sqrt (R * B))) ≤
        ∫ x in m..T, velocityH3DissipationAt u x ∂volume ∨
       (r < s + eta2 ∧ s < r + eta1)) := by
  have hA : 0 < V / (2 * P) := by positivity
  obtain ⟨_hh, _hSpike, hSecondary⟩ :=
    thirdFullPhysical_twoSlice_constructiveSqrtTailPDEClock244
      hH3 hClass hDInt m sState sSource
      (V / (2 * P)) B R E
      hm hsState hsSource hA hB hR hE hRate hGap
  obtain ⟨s, eta1, eta2, hWhich, hEta1, hEta2, hEnd1, hEnd2, hGate⟩ :=
    thirdFullPhysical_primarySecondaryPDEClocks_overlapOrAdditiveCharge244
      hH3 hClass hDInt m r P V J hm hr hP hV hPrimary
      sState sSource ((V / (2 * P)) / (12 * Real.sqrt (R * B)))
      hsState hsSource hSecondary
  refine ⟨s, eta1, eta2, hWhich, hEta1, hEta2, hEnd1, hEnd2, ?_⟩
  have hq : 0 < Real.sqrt (R * B) :=
    Real.sqrt_pos.2 (mul_pos hR hB)
  have hHeight :
      ((V / (2 * P)) / (12 * Real.sqrt (R * B))) / 2 =
        (V / (2 * P)) / (24 * Real.sqrt (R * B)) := by
    field_simp [ne_of_gt hP, ne_of_gt hq]
    <;> ring
  simpa only [hHeight] using hGate

end
end PrimeTensor.FirstMonomialTriad

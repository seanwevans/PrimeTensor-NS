import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessAnchoredTemporalExcursionGate
import Mathlib.Tactic

/-!
# Genuine source-peak temporal radii and unavoidable excursion widths

Both the physical projected momentum source and the H³-weighted spectral
velocity are strongly continuous on strictly preterminal compact intervals.
At each actual source peak and each positive physical observation threshold,
continuity supplies a positive radius. A temporal excursion above threshold
then *forces the original source window to reach that radius*.

The radius is local to the actual peak/window and can tend to zero near T.
We do NOT assume a terminal-uniform time modulus or that a maximizing time
belongs to the shorter quartic-calibrated dissipation interval.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A genuine continuous Hilbert-valued path has a positive relative
anchor radius for every positive increment threshold. -/
theorem h3Critical_continuousOn_anchor_has_positiveTemporalRadius
    {V : Type*} [NormedAddCommGroup V]
    (F : ℝ → V) (x w ε : ℝ) (hw : 0 < w) (hε : 0 < ε)
    (hCont : ContinuousOn F (Set.Icc x (x + w))) :
    ∃ η : ℝ, 0 < η ∧
      ∀ s : ℝ, s ∈ Set.Icc x (x + w) →
        |s - x| < η → ‖F s - F x‖ < ε := by
  have hx : x ∈ Set.Icc x (x + w) :=
    ⟨le_rfl, le_add_of_nonneg_right hw.le⟩
  obtain ⟨η, hη, hNear⟩ :=
    (Metric.continuousWithinAt_iff.mp (hCont x hx)) ε hε
  refine ⟨η, hη, ?_⟩
  intro s hs hDist
  have hDist' : dist s x < η := by
    simpa only [Real.dist_eq] using hDist
  have hSmall := hNear hs hDist'
  simpa only [dist_eq_norm] using hSmall

/-- A super-threshold excursion in a selected window forces the original
window to extend beyond the relative continuity radius. -/
theorem h3Critical_anchorExcursion_forces_windowWidth
    {V : Type*} [NormedAddCommGroup V]
    (F : ℝ → V) (x w s ε η : ℝ)
    (hs : s ∈ Set.Icc x (x + w))
    (hNear : ∀ r : ℝ, r ∈ Set.Icc x (x + w) →
      |r - x| < η → ‖F r - F x‖ < ε)
    (hExcursion : ε ≤ ‖F s - F x‖) :
    η ≤ w := by
  by_contra hNot
  have hShort : w < η := lt_of_not_ge hNot
  have hLower : 0 ≤ s - x := sub_nonneg.mpr hs.1
  have hUpper : s - x ≤ w := by linarith only [hs.2]
  have hClose : |s - x| < η := by
    rw [abs_of_nonneg hLower]
    exact lt_of_le_of_lt hUpper hShort
  have hNear' := hNear s hs hClose
  exact (not_lt_of_ge hExcursion) hNear'

/-- Both *actual* physical trajectories have positive anchor radii on any
strictly preterminal interval. The radius is independently selectable for
each threshold and is not a terminal-uniform Lipschitz coefficient. -/
theorem h3Critical_actualSourceSpectral_positiveAnchorRadii
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x w εU εR : ℝ)
    (hx : 0 < x) (hw : 0 < w) (hEnd : x + w < T)
    (hεU : 0 < εU) (hεR : 0 < εR) :
    ∃ ηU ηR : ℝ, 0 < ηU ∧ 0 < ηR ∧
      (∀ s : ℝ, s ∈ Set.Icc x (x + w) →
        |s - x| < ηU →
        ‖h3AuditActualSpectralVelocityTotal hH3 s -
          h3AuditActualSpectralVelocityTotal hH3 x‖ < εU) ∧
      (∀ s : ℝ, s ∈ Set.Icc x (x + w) →
        |s - x| < ηR →
        ‖h3PathActualProjectedMomentumSource244 hH3 s -
          h3PathActualProjectedMomentumSource244 hH3 x‖ < εR) := by
  have hxw : x < x + w := by linarith only [hw]
  have hSourceCont : ContinuousOn
      (h3PathActualProjectedMomentumSource244 hH3)
      (Set.Icc x (x + w)) :=
    h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 hx hxw hEnd
  have hInside : Set.Icc x (x + w) ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_of_lt_of_le hx hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hStateCont : ContinuousOn
      (h3AuditActualSpectralVelocityTotal hH3)
      (Set.Icc x (x + w)) :=
    (h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hInside
  obtain ⟨ηU, hηU, hNearU⟩ :=
    h3Critical_continuousOn_anchor_has_positiveTemporalRadius
      (h3AuditActualSpectralVelocityTotal hH3) x w εU hw hεU hStateCont
  obtain ⟨ηR, hηR, hNearR⟩ :=
    h3Critical_continuousOn_anchor_has_positiveTemporalRadius
      (h3PathActualProjectedMomentumSource244 hH3) x w εR hw hεR hSourceCont
  exact ⟨ηU, ηR, hηU, hηR, hNearU, hNearR⟩

/-- The exact attained-maxima witnesses from the accepted cofinal theorem
carry a local, positive *necessary width* for either actual temporal
excursion. No extra PDE regularity or terminal-uniform modulus is assumed. -/
theorem h3Critical_noL2Trace_cofinalFivefold_excursionForcesLocalWidth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hq : ∀ n, 0 < q n) :
    ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
            (M (v k)) (q (v k))) * ENNReal.ofReal (δ k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ∧
      (∀ k : ℕ,
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        sSource k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        sState k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        0 < δ k ∧ δ k ≤ w (v k)) ∧
      (∀ k : ℕ, ∀ εU εR : ℝ, 0 < εU → 0 < εR →
        ∃ ηU ηR : ℝ, 0 < ηU ∧ 0 < ηR ∧
          (εU ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (sState k) -
              h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ →
            ηU ≤ w (v k)) ∧
          (εR ≤ ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k) -
              h3PathActualProjectedMomentumSource244 hH3 (t (v k))‖ →
            ηR ≤ w (v k)) ∧
          (w (v k) < ηU →
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k) -
              h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ < εU) ∧
          (w (v k) < ηR →
            ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k) -
              h3PathActualProjectedMomentumSource244 hH3 (t (v k))‖ < εR)) := by
  obtain ⟨_i, t, w, v, sSource, sState, _A, _B, δ,
      hv, hLimit, hSep, hCosts, hWindows⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_anchoredTemporalExcursionGate
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  refine ⟨t, w, v, sSource, sState, δ,
    hv, hLimit, hSep, hCosts, ?_, ?_⟩
  · intro k
    obtain ⟨_ht, hw, hEnd, hsSource, hsState, _hMax,
      _hA, _hB, hδ, hδw, _hWidth, _hFloor, _hAlt⟩ := hWindows k
    exact ⟨hw, hEnd, hsSource, hsState, hδ, hδw⟩
  · intro k εU εR hεU hεR
    obtain ⟨ht, hw, hEnd, hsSource, hsState, _hMax,
      _hA, _hB, _hδ, _hδw, _hWidth, _hFloor, _hAlt⟩ := hWindows k
    have hx : 0 < t (v k) :=
      lt_trans hClass.terminal_start.1
        (lt_trans hb.1 (lt_trans (hc (v k)).1 ht.1))
    obtain ⟨ηU, ηR, hηU, hηR, hNearU, hNearR⟩ :=
      h3Critical_actualSourceSpectral_positiveAnchorRadii
        hH3 (t (v k)) (w (v k)) εU εR hx hw hEnd hεU hεR
    refine ⟨ηU, ηR, hηU, hηR, ?_, ?_, ?_, ?_⟩
    · intro hExc
      exact h3Critical_anchorExcursion_forces_windowWidth
        (h3AuditActualSpectralVelocityTotal hH3)
        (t (v k)) (w (v k)) (sState k) εU ηU
        hsState hNearU hExc
    · intro hExc
      exact h3Critical_anchorExcursion_forces_windowWidth
        (h3PathActualProjectedMomentumSource244 hH3)
        (t (v k)) (w (v k)) (sSource k) εR ηR
        hsSource hNearR hExc
    · intro hShort
      have hLower : 0 ≤ sState k - t (v k) := sub_nonneg.mpr hsState.1
      have hUpper : sState k - t (v k) ≤ w (v k) := by
        linarith only [hsState.2]
      have hDist : |sState k - t (v k)| < ηU := by
        rw [abs_of_nonneg hLower]
        exact lt_of_le_of_lt hUpper hShort
      exact hNearU (sState k) hsState hDist
    · intro hShort
      have hLower : 0 ≤ sSource k - t (v k) := sub_nonneg.mpr hsSource.1
      have hUpper : sSource k - t (v k) ≤ w (v k) := by
        linarith only [hsSource.2]
      have hDist : |sSource k - t (v k)| < ηR := by
        rw [abs_of_nonneg hLower]
        exact lt_of_le_of_lt hUpper hShort
      exact hNearR (sSource k) hsSource hDist

end
end PrimeTensor.Bridge.Euclidean

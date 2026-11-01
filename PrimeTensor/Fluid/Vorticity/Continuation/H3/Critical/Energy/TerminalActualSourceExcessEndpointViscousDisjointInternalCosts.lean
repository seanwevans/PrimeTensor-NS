import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousFiniteBandPersistence
import Mathlib.Tactic

/-!
# Disjoint internal costs for actual attained H³ viscous endpoint spikes

The previous theorem turns a full-H³ viscous spike at an attained spectral
maximum into an integrated right-hand cost, but that window may cross the next
source peak. Here the new positive window is instead contained inside its
OWN original source window. If the maximizing time is near the right endpoint,
we use a LEFT-hand window. Finite-band continuity permits either orientation.

The original cofinal source construction already makes these full source
windows strictly separated, even though later summaries retained only
separation of the shorter quartic-calibrated windows. Thus endpoint windows
can be charged without overlap and without treating an instantaneous value
as an integral. No full H³ dissipation continuity or uniform persistence
width is assumed. Zero-width slots represent indices without a spike.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Any strict full-H³ viscous spike inside a strictly preterminal compact
source window has a positive *internal* subwindow, oriented right or left
according to the maximum's position, on which finite-band dissipation
and actual full dissipation exceed the prescribed height. -/
theorem h3Critical_fullViscousSpike_has_internalFiniteBandCost
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x w s H : ℝ) (hx : x ∈ Set.Ioo a T)
    (hw : 0 < w) (hEnd : x + w < T)
    (hs : s ∈ Set.Icc x (x + w))
    (hSpike : H < velocityH3DissipationAt u s) :
    ∃ (N : ℕ) (p η : ℝ), 0 < η ∧ x ≤ p ∧ p + η ≤ x + w ∧
      (∀ r : ℝ, r ∈ Set.Icc p (p + η) →
        H < h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) ∧
        H < velocityH3DissipationAt u r) ∧
      ENNReal.ofReal H * ENNReal.ofReal η ≤
        ∫⁻ r in Set.Ioc p (p + η),
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume := by
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  obtain ⟨N, hCapture⟩ :=
    h3Critical_fullViscousSpike_has_finiteRadialCapture
      hH3 hClass s H hsClass hSpike
  let B : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r)
  have hBCont : ContinuousOn B (Set.Ioo a T) := by
    dsimp only [B]
    exact h3Path_actualLowRadialDissipation_continuousOn_positiveTime244
      hH3 hClass ((N : ℝ) + 1) (by positivity)
  have hAt : H < B s := hCapture
  have hContinuous : ContinuousAt (fun r : ℝ => H - B r) s :=
    continuousAt_const.sub (hBCont.continuousAt (isOpen_Ioo.mem_nhds hsClass))
  have hNegative : H - B s < 0 := by linarith only [hAt]
  obtain ⟨η₀, hη₀, hNear⟩ :=
    h3Path_continuousStrictInequality_localWindow244 hContinuous hNegative
  let η : ℝ := min (η₀ / 2) (w / 4)
  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min (by linarith only [hη₀]) (by linarith only [hw])
  have hηNear : η ≤ η₀ / 2 := min_le_left _ _
  have hηWindow : η ≤ w / 4 := min_le_right _ _
  have hηSmall : η < η₀ := by linarith only [hηNear, hη₀]
  -- The nearer half of the original interval always leaves room for a
  -- positive one-sided subwindow; the maximum itself is included.
  let p : ℝ := if s ≤ x + w / 2 then s else s - η
  have hp : x ≤ p := by
    dsimp only [p]
    split_ifs with hLeft
    · exact hs.1
    · have hRight : x + w / 2 < s := lt_of_not_ge hLeft
      linarith only [hRight, hηWindow, hw]
  have hpEnd : p + η ≤ x + w := by
    dsimp only [p]
    split_ifs with hLeft
    · linarith only [hLeft, hηWindow, hw]
    · simpa only [sub_add_cancel] using hs.2
  have hNearForAll (r : ℝ) (hr : r ∈ Set.Icc p (p + η)) :
      H < B r := by
    have hDist : dist r s < η₀ := by
      rw [Real.dist_eq]
      apply abs_lt.mpr
      dsimp only [p] at hr
      split_ifs at hr with hLeft
      · constructor <;> linarith only [hr.1, hr.2, hηSmall, hη, hη₀]
      · constructor <;> linarith only [hr.1, hr.2, hηSmall, hη, hη₀]
    have hNear' := hNear r hDist
    linarith only [hNear']
  have hInside (r : ℝ) (hr : r ∈ Set.Icc p (p + η)) :
      r ∈ Set.Ioo a T := by
    exact ⟨lt_of_lt_of_le hx.1 (le_trans hp hr.1),
      lt_of_le_of_lt (le_trans hr.2 hpEnd) hEnd⟩
  have hFloor (r : ℝ) (hr : r ∈ Set.Icc p (p + η)) :
      H < B r ∧ H < velocityH3DissipationAt u r := by
    have hLow := hNearForAll r hr
    have hPart := h3Path_actualRadialDissipation_partition244
      hH3 hClass r (hInside r hr) ((N : ℝ) + 1)
    have hHigh : 0 ≤ h3PathActualHighRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r) := by
      unfold h3PathActualHighRadialDissipation244
      apply integral_nonneg
      intro ξ
      exact h3TerminalSpectralDissipationSingleDensity_nonneg
        (h3AuditActualSpectralVelocityTotal hH3 r) ξ
    dsimp only [B] at hLow ⊢
    exact ⟨hLow, by linarith only [hLow, hPart, hHigh]⟩
  refine ⟨N, p, η, hη, hp, hpEnd, ?_, ?_⟩
  · intro r hr
    exact hFloor r hr
  · have hIntegral :
        (∫⁻ _r in Set.Ioc p (p + η), ENNReal.ofReal H ∂volume) ≤
          ∫⁻ r in Set.Ioc p (p + η),
            ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume := by
          apply h3Critical_extendedWindowCost_of_pointwiseFloor
          intro r hr
          exact (hFloor r hr).2.le
    calc
      ENNReal.ofReal H * ENNReal.ofReal η =
          (∫⁻ _r in Set.Ioc p (p + η), ENNReal.ofReal H ∂volume) :=
        (h3Critical_extendedConstantWindow_eq_heightWidth p η H hη.le).symm
      _ ≤ ∫⁻ r in Set.Ioc p (p + η),
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume := hIntegral

/-- Every subwindow inside strictly separated original windows is itself
strictly separated, even if some of the subwindows have zero length. -/
theorem h3Critical_internalWindows_strictlySeparated
    (x w p η : ℕ → ℝ)
    (hSep : ∀ k l : ℕ, k < l → x k + w k < x l)
    (hInside : ∀ k, x k ≤ p k ∧ p k + η k ≤ x k + w k) :
    ∀ k l : ℕ, k < l → p k + η k < p l := by
  intro k l hkl
  exact lt_of_lt_of_le
    (lt_of_le_of_lt (hInside k).2 (hSep k l hkl))
    (hInside l).1

/-- Pointwise extended physical charges add over finite selections without
an unjustified integral bound on the entire terminal tail. -/
theorem h3Critical_internalWindows_finiteCostSum
    (H p η : ℕ → ℝ) (F : ℝ → ℝ)
    (hCost : ∀ k : ℕ,
      ENNReal.ofReal (H k) * ENNReal.ofReal (η k) ≤
        ∫⁻ r in Set.Ioc (p k) (p k + η k),
          ENNReal.ofReal (F r) ∂volume)
    (m : ℕ) :
    (∑ k ∈ Finset.range m,
      ENNReal.ofReal (H k) * ENNReal.ofReal (η k)) ≤
    ∑ k ∈ Finset.range m,
      ∫⁻ r in Set.Ioc (p k) (p k + η k),
        ENNReal.ofReal (F r) ∂volume := by
  apply Finset.sum_le_sum
  intro k _hk
  exact hCost k

/-- The original source construction supplies strictly separated FULL
windows. At each attained spectral maximum, select a positive internal
finite-band dissipation window if it exceeds a prescribed positive viscous
height, and a zero-width slot otherwise. Hence the positive endpoint costs
are simultaneously disjoint and satisfy a finite summed bound. Neither
full-dissipation continuity nor a common positive width is assumed. -/
theorem h3Critical_noL2Trace_cofinalAttainedMax_disjointConditionalViscousCosts
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
    (hq : ∀ n, 0 < q n)
    (R ε : ℕ → ℝ) (hR : ∀ k, 0 < R k) (hε : ∀ k, 0 < ε k) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + w (v k) < t (v l)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k) + (5 * q (v k)) /
            (3 * (3 + h3AuditInitialLerayEnergyCoefficient))) *
            ENNReal.ofReal (w (v k))) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ r in Set.Ioc (t (v k)) (t (v k) + w (v k)),
            ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ∧
      (∀ k, 0 < R k ^ 2 * ε k ^ 2 / 8) ∧
      (∀ k l : ℕ, k < l → p k + η k < p l) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) (σ (v k)) (M (v k)) +
              5 * q (v k) <
            ‖h3CriticalActualProjectedHighpassFourierSource hH3
              (ρ (v k)) i s‖ ∧
          M (v k) + (5 * q (v k)) /
              (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) <
            h3PathActualHighRadialDissipation244 (σ (v k))
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        sSource k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        sState k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
            ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖) ∧
        t (v k) ≤ p k ∧ 0 ≤ η k ∧ p k + η k ≤ t (v k) + w (v k) ∧
        (R k ^ 2 * ε k ^ 2 < 8 * velocityH3DissipationAt u (sState k) →
          0 < η k ∧
          (∀ r : ℝ, r ∈ Set.Icc (p k) (p k + η k) →
            R k ^ 2 * ε k ^ 2 / 8 <
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            R k ^ 2 * ε k ^ 2 / 8 < velocityH3DissipationAt u r)) ∧
        (¬ R k ^ 2 * ε k ^ 2 < 8 * velocityH3DissipationAt u (sState k) →
          η k = 0)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (R k ^ 2 * ε k ^ 2 / 8) * ENNReal.ofReal (η k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ r in Set.Ioc (p k) (p k + η k),
            ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) := by
  let fiveq : ℕ → ℝ := fun n => 5 * q n
  have hFive : ∀ n, 0 ≤ fiveq n := by
    intro n
    dsimp only [fiveq]
    exact mul_nonneg (by norm_num) (hq n).le
  obtain ⟨i, t, w, v, hv, hLimit, hSeparated, hWindows, hOldCost⟩ :=
    h3Critical_noL2Trace_sourceExcess_disjointEnhancedFullDissipationCosts
      hH3 hClass b hb hNoTrace c ρ σ M fiveq
      hc hcLimit hρ hσ hM hFive
  have hMaxSelected (k : ℕ) :
      ∃ sSource sState : ℝ,
        sSource ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        sState ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
            ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤
            ‖h3AuditActualSpectralVelocityTotal hH3 sState‖) := by
    have ht : t (v k) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans (hc (v k)).1 (hWindows k).1.1),
        (hWindows k).1.2⟩
    exact h3Critical_actualSourceSpectral_attainedCompactMaxima
      hH3 (t (v k)) (w (v k))
      (lt_trans hClass.terminal_start.1 ht.1)
      (hWindows k).2.1 (hWindows k).2.2.1
  choose sSource sState hsSource hsState hMax using hMaxSelected
  let H : ℕ → ℝ := fun k => R k ^ 2 * ε k ^ 2 / 8
  have hLocal (k : ℕ) :
      ∃ (N : ℕ) (p η : ℝ),
        t (v k) ≤ p ∧ 0 ≤ η ∧ p + η ≤ t (v k) + w (v k) ∧
        ENNReal.ofReal (H k) * ENNReal.ofReal η ≤
          ∫⁻ r in Set.Ioc p (p + η),
            ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume ∧
        (H k < velocityH3DissipationAt u (sState k) →
          0 < η ∧ ∀ r : ℝ, r ∈ Set.Icc p (p + η) →
            H k < h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            H k < velocityH3DissipationAt u r) ∧
        (¬ H k < velocityH3DissipationAt u (sState k) → η = 0) := by
    classical
    by_cases hSpike : H k < velocityH3DissipationAt u (sState k)
    · have ht : t (v k) ∈ Set.Ioo a T :=
        ⟨lt_trans hb.1 (lt_trans (hc (v k)).1 (hWindows k).1.1),
          (hWindows k).1.2⟩
      obtain ⟨N, p, η, hη, hp, hpEnd, hFloor, hCost⟩ :=
        h3Critical_fullViscousSpike_has_internalFiniteBandCost
          hH3 hClass (t (v k)) (w (v k)) (sState k) (H k)
          ht (hWindows k).2.1 (hWindows k).2.2.1 (hsState k) hSpike
      refine ⟨N, p, η, hp, hη.le, hpEnd, hCost, ?_, ?_⟩
      · intro _
        exact ⟨hη, hFloor⟩
      · intro hFalse
        exact False.elim (hFalse hSpike)
    · refine ⟨0, t (v k), 0, le_rfl, le_rfl, ?_, ?_, ?_, ?_⟩
      · simpa only [add_zero] using (le_add_of_nonneg_right (hWindows k).2.1.le)
      · simp
      · intro hContradiction
        exact False.elim (hSpike hContradiction)
      · intro _
        rfl
  choose N p η hp hη hpEnd hCost hFloor hZero using hLocal
  have hHeightPos (k : ℕ) : 0 < R k ^ 2 * ε k ^ 2 / 8 := by
    have hRk := hR k
    have hεk := hε k
    positivity
  have hSepInternal : ∀ k l : ℕ, k < l → p k + η k < p l :=
    h3Critical_internalWindows_strictlySeparated
      (fun k => t (v k)) (fun k => w (v k)) p η hSeparated
      (fun k => ⟨hp k, hpEnd k⟩)
  have hOldCost' : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        ENNReal.ofReal (M (v k) + (5 * q (v k)) /
          (3 * (3 + h3AuditInitialLerayEnergyCoefficient))) *
          ENNReal.ofReal (w (v k))) ≤
      ∑ k ∈ Finset.range m,
        ∫⁻ r in Set.Ioc (t (v k)) (t (v k) + w (v k)),
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume := by
    simpa only [fiveq] using hOldCost
  refine ⟨i, t, w, v, sSource, sState, p, η, N,
    hv, hLimit, hSeparated, hOldCost', hHeightPos, hSepInternal, ?_, ?_⟩
  · intro k
    have hShift (hk : R k ^ 2 * ε k ^ 2 <
        8 * velocityH3DissipationAt u (sState k)) :
        H k < velocityH3DissipationAt u (sState k) := by
      dsimp only [H]
      apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)).2
      nlinarith only [hk]
    have hReverse (hk : H k < velocityH3DissipationAt u (sState k)) :
        R k ^ 2 * ε k ^ 2 <
          8 * velocityH3DissipationAt u (sState k) := by
      dsimp only [H] at hk
      have := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)).mp hk
      nlinarith only [this]
    have hPhysical : ∀ s : ℝ,
        s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) (σ (v k)) (M (v k)) +
            5 * q (v k) <
          ‖h3CriticalActualProjectedHighpassFourierSource hH3
            (ρ (v k)) i s‖ ∧
        M (v k) + (5 * q (v k)) /
            (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) <
          h3PathActualHighRadialDissipation244 (σ (v k))
            (h3AuditActualSpectralVelocityTotal hH3 s) := by
      simpa only [fiveq] using (hWindows k).2.2.2
    refine ⟨(hWindows k).1, (hWindows k).2.1,
      (hWindows k).2.2.1, hPhysical, hsSource k, hsState k, hMax k,
      hp k, hη k, hpEnd k, ?_, ?_⟩
    · intro hk
      have h := hFloor k (hShift hk)
      simpa only [H] using h
    · intro hk
      apply hZero k
      intro hh
      exact hk (hReverse hh)
  · intro m
    simpa only [H] using
      (h3Critical_internalWindows_finiteCostSum
        H p η (velocityH3DissipationAt u) hCost m)

end
end PrimeTensor.Bridge.Euclidean

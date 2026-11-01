import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourcePeakCofinalConstructiveQuarticCosts
import Mathlib.Tactic

/-!
# Explicit quartic physical persistence radius and terminal cost compression

The existing automatic persistence proof chooses a frequency radius by an
explicit formula but hides it behind existential quantifiers. Here the same
physical PDE inequality is retained with its precise calibrated radius
R = max(1,sigma)+1+A^2 B/P^2 and width delta=min(w,R^-4).
This converts an individual finite dissipation cost into a quantitative
alternative: the available physical interval compresses or the required
frequency radius is large. Neither terminal bound is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeCalibratedWidth
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCalibratedWidth :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact constructive radius used in the physical PDE quartic clock. -/
noncomputable def h3CriticalSourcePeakCalibratedRadius
    (σ P A B : ℝ) : ℝ :=
  max 1 σ + 1 + (A ^ 2 * B) / P ^ 2

/-- Explicit source margin dominates all fixed local physical costs at the
calibrated radius; unlike a generic existence lemma it exposes that radius. -/
theorem h3Critical_positiveSourceMargin_explicitDominantQuarticRadius
    (P K σ : ℝ) (hP : 0 < P) (hK : 0 ≤ K) :
    1 ≤ max 1 σ + 1 + K / P ^ 2 ∧
    σ ≤ max 1 σ + 1 + K / P ^ 2 ∧
    K < (max 1 σ + 1 + K / P ^ 2) ^ 2 * P ^ 2 := by
  let Q : ℝ := max 1 σ
  let R : ℝ := Q + 1 + K / P ^ 2
  have hp : 0 < P ^ 2 := pow_pos hP 2
  have hQone : 1 ≤ Q := le_max_left _ _
  have hQsigma : σ ≤ Q := le_max_right _ _
  have hDiv : 0 ≤ K / P ^ 2 := div_nonneg hK hp.le
  have hQR : Q ≤ R := by
    dsimp only [R]
    linarith only [hDiv]
  have hRone : 1 ≤ R := le_trans hQone hQR
  have hRSigma : σ ≤ R := le_trans hQsigma hQR
  have hProduct : R * P ^ 2 = (Q + 1) * P ^ 2 + K := by
    dsimp only [R]
    field_simp [ne_of_gt hp]
  have hR2 : R ≤ R ^ 2 := by
    have hMul := mul_le_mul_of_nonneg_right hRone
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hRone)
    nlinarith only [hMul]
  have hPositive : 0 < (Q + 1) * P ^ 2 :=
    mul_pos (by linarith only [hQone]) hp
  have hStrict : K < R ^ 2 * P ^ 2 := by
    calc
      K < R * P ^ 2 := by rw [hProduct]; linarith only [hPositive]
      _ ≤ R ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_right hR2 hp.le
  exact ⟨hRone, hRSigma, hStrict⟩

/-- Actual source peak, local physical PDE ceilings and a strictly positive
margin yield a SPECIFIC radius and width, not just abstract witnesses. -/
theorem h3Critical_strictSourcePeak_explicitCalibratedQuarticPersistence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (M C E δ₀ : ℝ) (hM : 0 ≤ M)
    (hδ₀ : 0 < δ₀) (hEnd : t + δ₀ < T)
    (hCeil : ∀ s : ℝ, s ∈ Set.Icc t (t + δ₀) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C)
    (hState : ∀ s : ℝ, s ∈ Set.Icc t (t + δ₀) →
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖) :
    ∃ P A B R δ : ℝ,
      P = (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M) ∧
      A = (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ + E)) ∧
      B = (12 * C ^ 2 + 2 * (velocityH3DissipationAt u t + M)) ∧
      R = h3CriticalSourcePeakCalibratedRadius σ P A B ∧
      δ = min δ₀ (1 / R ^ 4) ∧
      1 ≤ R ∧ σ ≤ R ∧ 0 < δ ∧
      δ ≤ δ₀ ∧ R ^ 4 * δ ≤ 1 ∧
      ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        M < h3PathActualHighRadialDissipation244 σ
          (h3AuditActualSpectralVelocityTotal hH3 s) := by
  let P : ℝ :=
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
      h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M
  let A : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient *
    (‖h3AuditActualSpectralVelocityTotal hH3 t‖ + E)
  let D : ℝ := velocityH3DissipationAt u t
  let B : ℝ := 12 * C ^ 2 + 2 * (D + M)
  have hP : 0 < P := sub_pos.mpr hPeak
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hD : 0 ≤ D := velocityH3DissipationAt_nonneg u t
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hK : 0 ≤ A ^ 2 * B := mul_nonneg (sq_nonneg A) hB
  let R : ℝ := h3CriticalSourcePeakCalibratedRadius σ P A B
  have hRadius :=
    h3Critical_positiveSourceMargin_explicitDominantQuarticRadius
      P (A ^ 2 * B) σ hP hK
  have hR : 1 ≤ R := hRadius.1
  have hσR : σ ≤ R := hRadius.2.1
  have hGap : A ^ 2 * B < R ^ 2 * P ^ 2 := hRadius.2.2
  let δ : ℝ := min δ₀ (1 / R ^ 4)
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hRfour : 0 < R ^ 4 := pow_pos hRpos 4
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hδ₀ (one_div_pos.mpr hRfour)
  have hδBase : δ ≤ δ₀ := min_le_left _ _
  have hδFour : δ ≤ 1 / R ^ 4 := min_le_right _ _
  have hClockδ : R ^ 4 * δ ≤ 1 := by
    calc
      R ^ 4 * δ ≤ R ^ 4 * (1 / R ^ 4) :=
        mul_le_mul_of_nonneg_left hδFour hRfour.le
      _ = 1 := by field_simp [ne_of_gt hRfour]
  refine ⟨P, A, B, R, δ, rfl, rfl, rfl, rfl, rfl,
    hR, hσR, hδ, hδBase, hClockδ, ?_⟩
  intro s hs
  by_contra hNot
  have hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M :=
    le_of_not_gt hNot
  have hts : t ≤ s := hs.1
  have hElapsed : s - t ≤ δ := by linarith only [hs.2]
  have hClock : R ^ 4 * (s - t) ≤ 1 := by
    have hScaled := mul_le_mul_of_nonneg_left hElapsed hRfour.le
    exact le_trans hScaled hClockδ
  have hsWide : s ∈ Set.Icc t (t + δ₀) := by
    refine ⟨hs.1, ?_⟩
    linarith only [hs.2, hδBase]
  have hsTime : s ∈ Set.Ioo b T := by
    refine ⟨lt_of_lt_of_le ht.1 hs.1, ?_⟩
    exact lt_of_le_of_lt (le_trans hsWide.2 (le_refl _)) hEnd
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hsTime.1, hsTime.2⟩
  have hCeilShort : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C := by
    intro r hr
    exact hCeil r ⟨hr.1, le_trans hr.2 hsWide.2⟩
  let As : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient *
    (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
  have hCL : 0 ≤ h3AuditInitialLerayEnergyCoefficient :=
    h3AuditInitialLerayEnergyCoefficient_nonneg
  have hAcoeff : 0 ≤ As := by
    dsimp only [As]
    have hProd : 0 ≤ h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖) :=
      mul_nonneg hCL (add_nonneg (norm_nonneg _) (norm_nonneg _))
    linarith only [hProd]
  have hAs : As ≤ A := by
    have hSum := add_le_add_left (hState s hsWide)
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖
    have hMul := mul_le_mul_of_nonneg_left hSum hCL
    dsimp only [As, A]
    linarith only [hMul]
  have hAsSq : As ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ hAcoeff hAs 2
  have hInitTail : h3PathActualHighRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 t) ≤ D := by
    dsimp only [D]
    exact h3Critical_actualHighRadialDissipation_le_full
      hH3 hClass t htClass R
  have hInitial : R ^ 2 * P ^ 2 ≤ As ^ 2 *
      (12 * C ^ 2 +
        2 * (h3PathActualHighRadialDissipation244 R
          (h3AuditActualSpectralVelocityTotal hH3 t) + M)) := by
    dsimp only [P, As]
    exact h3Critical_quarticSourceDrop_initialTailDissipationBudget
      hH3 hClass b hb ρ σ R hσ hR hσR i
      t s ht hsTime hts M C hClock hCeilShort hPeak.le hDrop
  have hCost : 12 * C ^ 2 +
      2 * (h3PathActualHighRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 t) + M) ≤ B := by
    dsimp only [B]
    linarith only [hInitTail]
  have hBudget : R ^ 2 * P ^ 2 ≤ A ^ 2 * B := by
    calc
      R ^ 2 * P ^ 2 ≤ As ^ 2 *
          (12 * C ^ 2 +
            2 * (h3PathActualHighRadialDissipation244 R
              (h3AuditActualSpectralVelocityTotal hH3 t) + M)) := hInitial
      _ ≤ As ^ 2 * B :=
        mul_le_mul_of_nonneg_left hCost (sq_nonneg As)
      _ ≤ A ^ 2 * B :=
        mul_le_mul_of_nonneg_right hAsSq hB
  exact (not_lt_of_ge hBudget) hGap


/-- The no-terminal-L²-trace source peaks support a calibrated quartic radius
and a precisely identified lifetime at EVERY selected index. All local PDE
ceilings originate in the already proved compact-time continuity; no
terminal-uniform source or velocity bound is added.

The weighted physical viscous cost is retained on these newly calibrated,
pairwise separated subwindows. This is the quantitative input for comparing
source margins, Fourier scales and terminal dissipation budgets. -/
theorem h3Critical_noL2Trace_cofinalCalibratedQuarticWidths_and_fullCosts
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ C E P A B R δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        0 ≤ C k ∧ 0 ≤ E k ∧
        P k = (‖h3CriticalActualProjectedHighpassFourierSource hH3
            (ρ (v k)) i (t (v k))‖ -
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) (σ (v k)) (M (v k))) ∧
        A k = (3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ + E k)) ∧
        B k = (12 * (C k) ^ 2 + 2 *
          (velocityH3DissipationAt u (t (v k)) + M (v k))) ∧
        R k = h3CriticalSourcePeakCalibratedRadius
          (σ (v k)) (P k) (A k) (B k) ∧
        δ k = min (w (v k)) (1 / (R k) ^ 4) ∧
        1 ≤ R k ∧ σ (v k) ≤ R k ∧
        0 < δ k ∧ δ k ≤ w (v k) ∧ (R k) ^ 4 * δ k ≤ 1 ∧
        ∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) →
          M (v k) < h3PathActualHighRadialDissipation244 (σ (v k))
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k)) * ENNReal.ofReal (δ k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) := by
  -- Use the original source-driven windows, whose FULL widths are
  -- pairwise separated. The previously selected quartic subwindows need not
  -- contain a *new* recalibrated width, so their separation is insufficient.
  obtain ⟨i, t, w, v, hv, hLimit, hSeparated, hWindows, _hGate⟩ :=
    h3Critical_noL2Trace_cofinalSourceWindows_postDropGradientGate
      hH3 hClass b hb hNoTrace c ρ σ M hc hcLimit hρ hσ
  have hSelected (k : ℕ) :
      ∃ C E P A B R δ : ℝ,
        0 ≤ C ∧ 0 ≤ E ∧
        P = (‖h3CriticalActualProjectedHighpassFourierSource hH3
            (ρ (v k)) i (t (v k))‖ -
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) (σ (v k)) (M (v k))) ∧
        A = (3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ + E)) ∧
        B = (12 * C ^ 2 + 2 *
          (velocityH3DissipationAt u (t (v k)) + M (v k))) ∧
        R = h3CriticalSourcePeakCalibratedRadius (σ (v k)) P A B ∧
        δ = min (w (v k)) (1 / R ^ 4) ∧
        1 ≤ R ∧ σ (v k) ≤ R ∧ 0 < δ ∧ δ ≤ w (v k) ∧
        R ^ 4 * δ ≤ 1 ∧
        ∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ) →
          M (v k) < h3PathActualHighRadialDissipation244 (σ (v k))
            (h3AuditActualSpectralVelocityTotal hH3 s) := by
    have ht : t (v k) ∈ Set.Ioo b T :=
      ⟨lt_trans (hc (v k)).1 (hWindows k).1.1, (hWindows k).1.2⟩
    obtain ⟨C, E, _R0, _δ0, hC0, hE0, _hR0, _hσR0,
        _hδ0, _hδw0, _hClock0, hCeils, _hFloor0⟩ :=
      h3Critical_strictSourcePeak_automaticPersistence_withoutLocalCeilingAssumptions
        hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
        (t (v k)) ht (M (v k)) (w (v k)) (hM (v k))
        (hWindows k).2.1 (hWindows k).2.2.1 (hWindows k).2.2.2.1
    obtain ⟨P, A, B, R, δ, hP, hA, hB, hRcal, hδcal,
        hR, hσR, hδ, hδw, hClock, hFloor⟩ :=
      h3Critical_strictSourcePeak_explicitCalibratedQuarticPersistence
        hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
        (t (v k)) ht (M (v k)) C E (w (v k)) (hM (v k))
        (hWindows k).2.1 (hWindows k).2.2.1
        (fun s hs => (hCeils s hs).1)
        (fun s hs => (hCeils s hs).2) (hWindows k).2.2.2.1
    exact ⟨C, E, P, A, B, R, δ, hC0, hE0, hP, hA, hB,
      hRcal, hδcal, hR, hσR, hδ, hδw, hClock, hFloor⟩
  choose C E P A B R δ hC0 hE0 hP hA hB hRcal hδcal
    hR hσR hδ hδw hClock hFloor using hSelected
  refine ⟨i, t, w, v, C, E, P, A, B, R, δ, hv, hLimit, ?_, ?_, ?_⟩
  · intro k
    rcases hWindows k with
      ⟨hStart, hw, hEnd, _hPeak, _hOldFloor⟩
    exact ⟨hStart, hw, hEnd, hC0 k, hE0 k,
      hP k, hA k, hB k, hRcal k, hδcal k,
      hR k, hσR k, hδ k, hδw k, hClock k, hFloor k⟩
  · intro k l hkl
    have hShort : t (v k) + δ k ≤ t (v k) + w (v k) :=
      add_le_add_right (hδw k) (t (v k))
    exact lt_of_le_of_lt hShort (hSeparated k l hkl)
  · intro m
    apply Finset.sum_le_sum
    intro k _hk
    have hLower :
        (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (M (v k)) ∂volume) ≤
        ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := by
      apply h3Critical_extendedWindowCost_of_pointwiseFloor
      intro s hs
      have hTime : s ∈ Set.Ioo a T := by
        have hStart : a < t (v k) :=
          lt_trans hb.1 (lt_trans (hc (v k)).1 (hWindows k).1.1)
        have hShort : t (v k) + δ k ≤ t (v k) + w (v k) :=
          add_le_add_right (hδw k) (t (v k))
        exact ⟨lt_of_lt_of_le hStart hs.1,
          lt_of_le_of_lt (le_trans hs.2 hShort) (hWindows k).2.2.1⟩
      exact (hFloor k s hs).le.trans
        (h3Critical_actualHighRadialDissipation_le_full
          hH3 hClass s hTime (σ (v k)))
    calc
      ENNReal.ofReal (M (v k)) * ENNReal.ofReal (δ k) =
          (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (M (v k)) ∂volume) :=
        (h3Critical_extendedConstantWindow_eq_heightWidth
          (t (v k)) (δ k) (M (v k)) (hδ k).le).symm
      _ ≤ ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := hLower

/-- A finite local physical dissipation charge forces either geometric
compression of the original window, or a large calibrated Fourier radius.
The branch distinction uses the EXACT quartic width, not merely an upper
bound on its duration. -/
theorem h3Critical_calibratedQuarticWidth_finiteCharge_forces_compression
    (w R M C : ℝ) (hR : 0 < R) (hM : 0 < M) (hC : 0 < C)
    (hCharge : M * min w (1 / R ^ 4) ≤ C) :
    w ≤ C / M ∨ M / C ≤ R ^ 4 := by
  by_cases hw : w ≤ 1 / R ^ 4
  · left
    have hEq : min w (1 / R ^ 4) = w := min_eq_left hw
    rw [hEq] at hCharge
    exact (le_div_iff₀ hM).2 (by simpa only [mul_comm] using hCharge)
  · right
    have hLower : 1 / R ^ 4 ≤ w := (le_of_lt (lt_of_not_ge hw))
    have hEq : min w (1 / R ^ 4) = 1 / R ^ 4 := min_eq_right hLower
    rw [hEq] at hCharge
    have hR4 : 0 < R ^ 4 := pow_pos hR 4
    have hScaled := mul_le_mul_of_nonneg_right hCharge hR4.le
    have hNecessary : M ≤ C * R ^ 4 := by
      have hSimplify : M * (1 / R ^ 4) * R ^ 4 = M := by
        field_simp [ne_of_gt hR4]
      rw [hSimplify] at hScaled
      simpa only [mul_comm] using hScaled
    exact (div_le_iff₀ hC).2 (by simpa only [mul_comm] using hNecessary)

/-- Applied to the actual physical H³ dissipation, a finite budget on a
calibrated source-peak window forces either physical window compression or
large fourth-power frequency. This is not an assumed terminal estimate. -/
theorem h3Critical_calibratedPhysicalDissipationBudget_forces_width_or_radius
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t w R δ M C : ℝ)
    (hR : 0 < R) (hδ : 0 ≤ δ) (hM : 0 < M) (hC : 0 < C)
    (hCal : δ = min w (1 / R ^ 4))
    (hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      M ≤ velocityH3DissipationAt u s)
    (hBudget :
      (∫⁻ s in Set.Ioc t (t + δ),
        ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ≤
          ENNReal.ofReal C) :
    w ≤ C / M ∨ M / C ≤ R ^ 4 := by
  have hWidth : δ ≤ C / M :=
    h3Critical_extendedWindowBudget_width_le
      (velocityH3DissipationAt u) t δ M C hδ hM hC.le
      hFloor hBudget
  have hCharge : M * min w (1 / R ^ 4) ≤ C := by
    have hMul := (le_div_iff₀ hM).1 hWidth
    rw [hCal] at hMul
    simpa only [mul_comm] using hMul
  exact h3Critical_calibratedQuarticWidth_finiteCharge_forces_compression
    w R M C hR hM hC hCharge

end
end PrimeTensor.Bridge.Euclidean

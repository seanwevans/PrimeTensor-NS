import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessPhysicalSourceViscousFactorGate
import Mathlib.Tactic

/-!
# Exact attained physical source and spectral maxima on fivefold source windows

The previous cofinal theorem used arbitrary nonnegative upper bounds C and E
on a fixed compact strict-time interval. Such bounds can grow because of
slack, even if the physical fields do not. Strong positive-time continuity
of the actual projected momentum source and spectral state eliminates this
ambiguity: both least bounds are attained at real times in the SAME window.

The resulting cofinal obstruction is expressed in physical pointwise norms
of the projected PDE source and the H³ spectral velocity, with the original
fivefold highpass source, calibrated clock, Riccati and width alternatives,
and disjoint full-H³ dissipation charges unchanged.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- The actual projected PDE momentum source and H³-weighted spectral state
have genuine, *attained* norm maxima on every strictly preterminal compact
physical interval. Unlike an arbitrary local ceiling, neither maximum
can grow without a real physical observation realizing it. -/
theorem h3Critical_actualSourceSpectral_attainedCompactMaxima
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x w : ℝ) (hx : 0 < x) (hw : 0 < w) (hEnd : x + w < T) :
    ∃ sSource sState : ℝ,
      sSource ∈ Set.Icc x (x + w) ∧
      sState ∈ Set.Icc x (x + w) ∧
      (∀ s : ℝ, s ∈ Set.Icc x (x + w) →
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
          ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤
          ‖h3AuditActualSpectralVelocityTotal hH3 sState‖) := by
  have hxw : x < x + w := by linarith only [hw]
  have hNonempty : (Set.Icc x (x + w)).Nonempty :=
    Set.nonempty_Icc.mpr hxw.le
  have hSourceContinuous : ContinuousOn
      (fun s : ℝ => ‖h3PathActualProjectedMomentumSource244 hH3 s‖)
      (Set.Icc x (x + w)) :=
    (h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 hx hxw hEnd).norm
  have hSub : Set.Icc x (x + w) ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_of_lt_of_le hx hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hStateContinuous : ContinuousOn
      (fun s : ℝ => ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
      (Set.Icc x (x + w)) :=
    ((h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hSub).norm
  obtain ⟨sSource, hsSource, hMaxSource⟩ :=
    isCompact_Icc.exists_isMaxOn hNonempty hSourceContinuous
  obtain ⟨sState, hsState, hMaxState⟩ :=
    isCompact_Icc.exists_isMaxOn hNonempty hStateContinuous
  have hSourceBound := isMaxOn_iff.mp hMaxSource
  have hStateBound := isMaxOn_iff.mp hMaxState
  exact ⟨sSource, sState, hsSource, hsState, fun s hs =>
    ⟨hSourceBound s hs, hStateBound s hs⟩⟩

/-- A genuine fivefold Fourier source peak has a calibrated physical PDE
persistence window in which the local source and spectral ceilings are
*attained* norms, not existential slack variables. All four physical
outcomes retain the original cost scale and Riccati exception. -/
theorem h3Critical_fivefoldWindow_attainedPhysicalFourWay
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (M q w : ℝ) (hM : 0 ≤ M) (hq : 0 < q)
    (hw : 0 < w) (hEnd : x + w < T)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M + 5 * q <
      ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i x‖) :
    ∃ sSource sState A B δ : ℝ,
      sSource ∈ Set.Icc x (x + w) ∧
      sState ∈ Set.Icc x (x + w) ∧
      (∀ s : ℝ, s ∈ Set.Icc x (x + w) →
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
          ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤
          ‖h3AuditActualSpectralVelocityTotal hH3 sState‖) ∧
      A = 3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 x‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 sState‖) ∧
      B = 12 * ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ ^ 2 +
        2 * (velocityH3DissipationAt u x +
          h3CriticalSourceExcessEnhancedFloor M q) ∧
      0 < δ ∧ δ ≤ w ∧
      min w (1 / (h3CriticalSourcePeakSquareRootRadius σ (4 * q) A B) ^ 4)
        ≤ δ ∧
      (∀ s : ℝ, s ∈ Set.Icc x (x + δ) →
        h3CriticalSourceExcessEnhancedFloor M q <
          velocityH3DissipationAt u s) ∧
      ((∃ s : ℝ, s ∈ Set.Icc x (x + δ) ∧
        h3CriticalSourceExcessEnhancedFloor M q <
          h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        (w ≤ (velocityH3EnergyAt u x - 1) /
            h3CriticalSourceExcessEnhancedFloor M q ∨
         h3CriticalSourceExcessEnhancedFloor M q ≤
           16 * (velocityH3EnergyAt u x - 1) * (max 1 σ + 1) ^ 4 ∨
         max 1 σ + 1 <
           3 + 2 * h3AuditInitialLerayEnergyCoefficient *
             ‖h3AuditActualSpectralVelocityTotal hH3 sState‖ ∨
         (4 * q) ^ 2 < 24 *
           ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ ^ 2 ∨
         (4 * q) ^ 2 < 8 * velocityH3DissipationAt u x ∨
         (4 * q) ^ 2 < 8 * h3CriticalSourceExcessEnhancedFloor M q)) := by
  have hx0 : 0 < x :=
    lt_trans hClass.terminal_start.1 (lt_trans hb.1 hx.1)
  obtain ⟨sSource, sState, hsSource, hsState, hCeil⟩ :=
    h3Critical_actualSourceSpectral_attainedCompactMaxima
      hH3 x w hx0 hw hEnd
  let C : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖
  let E : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
  obtain ⟨A, B, _R, δ, hA, hB, _hR, hδ, hδw,
      hWidth, hFull, _hGate⟩ :=
    h3Critical_fivefoldActualSourcePeak_certifiesPhysicalQuinticGate
      hH3 hClass b hb ρ σ hσ i x hx M q C E w
      hM hq hw hEnd
      (fun s hs => (hCeil s hs).1)
      (fun s hs => (hCeil s hs).2) hPeak
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hAlternative := h3Critical_fivefoldWindow_exactPhysicalPDEFactorGate
    hH3 hClass x w δ σ M q C E A B hxClass hM hq
    (norm_nonneg _) hδ hδw hEnd hA hB hWidth hFull
  have hPointwise :
      (∃ s : ℝ, s ∈ Set.Icc x (x + δ) ∧
        h3CriticalSourceExcessEnhancedFloor M q <
          h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
      (w ≤ (velocityH3EnergyAt u x - 1) /
          h3CriticalSourceExcessEnhancedFloor M q ∨
       h3CriticalSourceExcessEnhancedFloor M q ≤
          16 * (velocityH3EnergyAt u x - 1) * (max 1 σ + 1) ^ 4 ∨
       max 1 σ + 1 < 3 + 2 * h3AuditInitialLerayEnergyCoefficient * E ∨
       (4 * q) ^ 2 < 24 * C ^ 2 ∨
       (4 * q) ^ 2 < 8 * velocityH3DissipationAt u x ∨
       (4 * q) ^ 2 < 8 * h3CriticalSourceExcessEnhancedFloor M q) := by
    rcases hAlternative with hLarge | hRest
    · exact Or.inl hLarge
    · obtain ⟨_hEnergy, hRest⟩ := hRest
      rcases hRest with hShort | hRest
      · exact Or.inr (Or.inl hShort)
      · rcases hRest with hCutoff | hPDE
        · exact Or.inr (Or.inr (Or.inl hCutoff))
        · obtain ⟨_hThreshold, _hCost, hFactors⟩ := hPDE
          rcases hFactors with hState | hSource
          · have hStart : x ∈ Set.Icc x (x + w) :=
              ⟨le_rfl, le_add_of_nonneg_right hw.le⟩
            have hU : ‖h3AuditActualSpectralVelocityTotal hH3 x‖ ≤ E :=
              (hCeil x hStart).2
            have hCL := h3AuditInitialLerayEnergyCoefficient_nonneg
            have hScaled := mul_le_mul_of_nonneg_left
              (show ‖h3AuditActualSpectralVelocityTotal hH3 x‖ + E ≤
                2 * E by linarith only [hU]) hCL
            have hState' : max 1 σ + 1 <
                3 + 2 * h3AuditInitialLerayEnergyCoefficient * E := by
              linarith only [hState, hScaled]
            exact Or.inr (Or.inr (Or.inr (Or.inl hState')))
          · have hSource' :
                (4 * q) ^ 2 < 24 * C ^ 2 ∨
                (4 * q) ^ 2 < 8 * velocityH3DissipationAt u x ∨
                (4 * q) ^ 2 < 8 * h3CriticalSourceExcessEnhancedFloor M q := by
              by_cases hC : (4 * q) ^ 2 < 24 * C ^ 2
              · exact Or.inl hC
              · by_cases hD : (4 * q) ^ 2 < 8 * velocityH3DissipationAt u x
                · exact Or.inr (Or.inl hD)
                · right
                  right
                  by_contra hH
                  have hCLe : 24 * C ^ 2 ≤ (4 * q) ^ 2 := le_of_not_gt hC
                  have hDLe : 8 * velocityH3DissipationAt u x ≤ (4 * q) ^ 2 :=
                    le_of_not_gt hD
                  have hHLe : 8 * h3CriticalSourceExcessEnhancedFloor M q ≤
                      (4 * q) ^ 2 := le_of_not_gt hH
                  change (4 * q) ^ 2 < 12 * C ^ 2 + 2 *
                    (velocityH3DissipationAt u x +
                      h3CriticalSourceExcessEnhancedFloor M q) at hSource
                  nlinarith only [hSource, hCLe, hDLe, hHLe]
            rcases hSource' with hSource | hDiss | hFloor
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSource))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hDiss)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hFloor)))))
  refine ⟨sSource, sState, A, B, δ, hsSource, hsState,
    hCeil, ?_, ?_, hδ, hδw, hWidth, hFull, ?_⟩
  · exact hA
  · exact hB
  · dsimp only [C, E] at hPointwise
    exact hPointwise

/-- The cofinal fivefold source windows possess genuine maximizing physical
observation times. The projected source and spectral ceiling factors in the
quartic clock are now *observed* source/state norms, not loose bounds.
Disjointness, the original calibrated clock and finite summed physical
viscous charge remain part of the conclusion. -/
theorem h3Critical_noL2Trace_cofinalFivefold_attainedPhysicalPDEFactorGate
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
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState A B δ : ℕ → ℝ,
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
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        sSource k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        sState k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
            ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖) ∧
        A k = 3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ +
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖) ∧
        B k = 12 * ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ^ 2 +
          2 * (velocityH3DissipationAt u (t (v k)) +
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))) ∧
        0 < δ k ∧ δ k ≤ w (v k) ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) →
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            velocityH3DissipationAt u s) ∧
        ((∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
         (w (v k) ≤ (velocityH3EnergyAt u (t (v k)) - 1) /
             h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ∨
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ≤
            16 * (velocityH3EnergyAt u (t (v k)) - 1) *
              (max 1 (σ (v k)) + 1) ^ 4 ∨
          max 1 (σ (v k)) + 1 <
            3 + 2 * h3AuditInitialLerayEnergyCoefficient *
              ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖ ∨
          (4 * q (v k)) ^ 2 < 24 *
            ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ^ 2 ∨
          (4 * q (v k)) ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
          (4 * q (v k)) ^ 2 < 8 *
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))))) := by
  let fiveq : ℕ → ℝ := fun n => 5 * q n
  have hFive : ∀ n, 0 ≤ fiveq n := by
    intro n
    dsimp only [fiveq]
    exact mul_nonneg (by norm_num) (hq n).le
  obtain ⟨i, t, w, v, hv, hLimit, hSeparated, hWindows, _hOldCost⟩ :=
    h3Critical_noL2Trace_sourceExcess_disjointEnhancedFullDissipationCosts
      hH3 hClass b hb hNoTrace c ρ σ M fiveq hc hcLimit hρ hσ hM hFive
  have hSelected (k : ℕ) :
      ∃ sSource sState A B δ : ℝ,
        sSource ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        sState ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
            ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤
            ‖h3AuditActualSpectralVelocityTotal hH3 sState‖) ∧
        A = 3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ +
            ‖h3AuditActualSpectralVelocityTotal hH3 sState‖) ∧
        B = 12 * ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ ^ 2 +
          2 * (velocityH3DissipationAt u (t (v k)) +
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))) ∧
        0 < δ ∧ δ ≤ w (v k) ∧
        min (w (v k)) (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) A B) ^ 4) ≤ δ ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ) →
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            velocityH3DissipationAt u s) ∧
        ((∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ) ∧
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
         (w (v k) ≤ (velocityH3EnergyAt u (t (v k)) - 1) /
             h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ∨
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ≤
            16 * (velocityH3EnergyAt u (t (v k)) - 1) *
              (max 1 (σ (v k)) + 1) ^ 4 ∨
          max 1 (σ (v k)) + 1 <
            3 + 2 * h3AuditInitialLerayEnergyCoefficient *
              ‖h3AuditActualSpectralVelocityTotal hH3 sState‖ ∨
          (4 * q (v k)) ^ 2 < 24 *
            ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ ^ 2 ∨
          (4 * q (v k)) ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
          (4 * q (v k)) ^ 2 < 8 *
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)))) := by
    have ht : t (v k) ∈ Set.Ioo b T :=
      ⟨lt_trans (hc (v k)).1 (hWindows k).1.1, (hWindows k).1.2⟩
    have hAtStart : t (v k) ∈ Set.Icc
        (t (v k)) (t (v k) + w (v k)) :=
      ⟨le_rfl, le_add_of_nonneg_right ((hWindows k).2.1).le⟩
    have hFivePeak :
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) (σ (v k)) (M (v k)) +
          5 * q (v k) <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3
          (ρ (v k)) i (t (v k))‖ := by
      exact ((hWindows k).2.2.2 (t (v k)) hAtStart).1
    exact h3Critical_fivefoldWindow_attainedPhysicalFourWay
      hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
      (t (v k)) ht (M (v k)) (q (v k)) (w (v k))
      (hM (v k)) (hq (v k)) (hWindows k).2.1
      (hWindows k).2.2.1 hFivePeak
  choose sSource sState A B δ hsSource hsState hCeil hA hB
    hδ hδw hWidth hFloor hAlternative using hSelected
  have hSep (k l : ℕ) (hkl : k < l) :
      t (v k) + δ k < t (v l) := by
    have hShort : t (v k) + δ k ≤ t (v k) + w (v k) :=
      add_le_add_right (hδw k) (t (v k))
    exact lt_of_le_of_lt hShort (hSeparated k l hkl)
  refine ⟨i, t, w, v, sSource, sState, A, B, δ,
    hv, hLimit, hSep, ?_, ?_⟩
  · intro m
    apply Finset.sum_le_sum
    intro k _hk
    have hLower :
        (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
            (M (v k)) (q (v k))) ∂volume) ≤
        ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := by
      apply h3Critical_extendedWindowCost_of_pointwiseFloor
      intro s hs
      exact (hFloor k s hs).le
    calc
      ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
          (M (v k)) (q (v k))) * ENNReal.ofReal (δ k) =
          (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
              (M (v k)) (q (v k))) ∂volume) :=
        (h3Critical_extendedConstantWindow_eq_heightWidth
          (t (v k)) (δ k)
          (h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)))
          (hδ k).le).symm
      _ ≤ ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := hLower
  · intro k
    exact ⟨(hWindows k).1, (hWindows k).2.1,
      (hWindows k).2.2.1, hsSource k, hsState k,
      hCeil k, hA k, hB k, hδ k, hδw k,
      hWidth k, hFloor k, hAlternative k⟩

end
end PrimeTensor.Bridge.Euclidean

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousDisjointInternalCosts
import Mathlib.Tactic

/-!
# Synchronize spectral PDE alternatives with disjoint physical endpoint costs

The previously accepted conditional internal-cost theorem chose its own
attained source and spectral maxima on the original, strictly separated
fivefold source windows. A separate cofinal spectral PDE gate used different
existential witnesses, so the latter could not be charged to the former.

Here the quartic source certificate is run with the *already chosen* attained
maxima as exact physical ceilings. This retains the original full-window
separation, source excess, integrated physical dissipation costs and internal
finite-band spike costs on precisely the SAME temporal observations. No
uniqueness of maximizing times or terminal-uniform continuity is claimed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Run the genuine calibrated fivefold physical PDE source clock against
PRESCRIBED attained maxima. Their norm ceilings are exactly observed values,
not freshly selected existential variables. This is what permits later
synchronization with the already chosen disjoint cost subwindows. -/
theorem h3Critical_fivefoldWindow_fixedMaximaPhysicalFourWay
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (M q w : ℝ) (hM : 0 ≤ M) (hq : 0 < q)
    (hw : 0 < w) (hEnd : x + w < T)
    (sSource sState : ℝ)
    (hSourceMax : ∀ s : ℝ, s ∈ Set.Icc x (x + w) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
        ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖)
    (hStateMax : ∀ s : ℝ, s ∈ Set.Icc x (x + w) →
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 sState‖)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M + 5 * q <
      ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i x‖) :
    ∃ A B δ : ℝ,
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
        w ≤ (velocityH3EnergyAt u x - 1) /
          h3CriticalSourceExcessEnhancedFloor M q ∨
        h3CriticalSourceExcessEnhancedFloor M q ≤
          16 * (velocityH3EnergyAt u x - 1) * (max 1 σ + 1) ^ 4 ∨
        max 1 σ + 1 <
          3 + 2 * h3AuditInitialLerayEnergyCoefficient *
            ‖h3AuditActualSpectralVelocityTotal hH3 sState‖ ∨
        (4 * q) ^ 2 < 24 *
          ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ ^ 2 ∨
        (4 * q) ^ 2 < 8 * velocityH3DissipationAt u x ∨
        (4 * q) ^ 2 < 8 * h3CriticalSourceExcessEnhancedFloor M q) := by
  let C : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖
  let E : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
  obtain ⟨A, B, _R, δ, hA, hB, _hR, hδ, hδw,
      hWidth, hFull, _hGate⟩ :=
    h3Critical_fivefoldActualSourcePeak_certifiesPhysicalQuinticGate
      hH3 hClass b hb ρ σ hσ i x hx M q C E w
      hM hq hw hEnd hSourceMax hStateMax hPeak
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
      w ≤ (velocityH3EnergyAt u x - 1) /
        h3CriticalSourceExcessEnhancedFloor M q ∨
      h3CriticalSourceExcessEnhancedFloor M q ≤
        16 * (velocityH3EnergyAt u x - 1) * (max 1 σ + 1) ^ 4 ∨
      max 1 σ + 1 < 3 + 2 * h3AuditInitialLerayEnergyCoefficient * E ∨
      (4 * q) ^ 2 < 24 * C ^ 2 ∨
      (4 * q) ^ 2 < 8 * velocityH3DissipationAt u x ∨
      (4 * q) ^ 2 < 8 * h3CriticalSourceExcessEnhancedFloor M q := by
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
              hStateMax x hStart
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
  refine ⟨A, B, δ, hA, hB, hδ, hδw, hWidth, hFull, ?_⟩
  dsimp only [C, E] at hPointwise
  exact hPointwise

/-- One and the SAME cofinal fivefold selection carries the exact calibrated
PDE-clock alternatives AND the disjoint finite-band integrated charges for
its attained spectral maximizers. A possible endpoint-dissipation branch is
not passed to the costs of a different existential maximizing sequence.

The extra internal intervals may overlap the *original* quartic short
intervals for the same index, so those two cost sums are not added. The
endpoint widths remain nonuniform near T. -/
theorem h3Critical_noL2Trace_cofinalFivefold_synchronizedEndpointViscousCosts
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
    ∃ sSource sState A B δ p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + w (v k) < t (v l)) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ k l : ℕ, k < l → p k + η k < p l) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k) + (5 * q (v k)) /
            (3 * (3 + h3AuditInitialLerayEnergyCoefficient))) *
            ENNReal.ofReal (w (v k))) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ r in Set.Ioc (t (v k)) (t (v k) + w (v k)),
            ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (R k ^ 2 * ε k ^ 2 / 8) *
            ENNReal.ofReal (η k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ r in Set.Ioc (p k) (p k + η k),
            ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ∧
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
        A k = 3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ +
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖) ∧
        B k = 12 * ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ^ 2 +
          2 * (velocityH3DissipationAt u (t (v k)) +
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))) ∧
        0 < δ k ∧ δ k ≤ w (v k) ∧
        min (w (v k)) (1 / (h3CriticalSourcePeakSquareRootRadius
          (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) →
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            velocityH3DissipationAt u s) ∧
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
      (∀ k : ℕ,
        3 + 4 * h3AuditInitialLerayEnergyCoefficient * ε k ≤
          max 1 (σ (v k)) + 1 →
        h3Critical_fivefold_nonSpectralExcursionAlternative hH3
          (t (v k)) (w (v k)) (δ k) (σ (v k))
          (M (v k)) (q (v k)) (sSource k) ∨
        ε k ^ 2 ≤ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling (R k)) *
          (‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
            w (v k)) ^ 2 ∨
        R k ^ 2 * ε k ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
        (0 < η k ∧
          ∀ r : ℝ, r ∈ Set.Icc (p k) (p k + η k) →
            R k ^ 2 * ε k ^ 2 / 8 <
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            R k ^ 2 * ε k ^ 2 / 8 < velocityH3DissipationAt u r)) := by
  obtain ⟨i, t, w, v, sSource, sState, p, η, N,
      hv, hLimit, hSep, hOldCost, _hHeightPos, hSepInternal, hWindows, hEndCosts⟩ :=
    h3Critical_noL2Trace_cofinalAttainedMax_disjointConditionalViscousCosts
      hH3 hClass b hb hNoTrace c ρ σ M q
      hc hcLimit hρ hσ hM hq R ε hR hε
  have hSelected (k : ℕ) :
      ∃ A B δ : ℝ,
        A = 3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ +
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖) ∧
        B = 12 * ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ^ 2 +
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
          w (v k) ≤ (velocityH3EnergyAt u (t (v k)) - 1) /
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
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))) := by
    obtain ⟨ht, hw, hEnd, hPeaks, _hsSource, _hsState, hMax,
      _hp, _hη, _hpEnd, _hFloor, _hZero⟩ := hWindows k
    have htTail : t (v k) ∈ Set.Ioo b T :=
      ⟨lt_trans (hc (v k)).1 ht.1, ht.2⟩
    have hStart : t (v k) ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) :=
      ⟨le_rfl, le_add_of_nonneg_right hw.le⟩
    have hPeak := (hPeaks (t (v k)) hStart).1
    exact h3Critical_fivefoldWindow_fixedMaximaPhysicalFourWay
      hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
      (t (v k)) htTail (M (v k)) (q (v k)) (w (v k))
      (hM (v k)) (hq (v k)) hw hEnd (sSource k) (sState k)
      (fun s hs => (hMax s hs).1)
      (fun s hs => (hMax s hs).2) hPeak
  choose A B δ hA hB hδ hδw hWidth hFloor hAlternative using hSelected
  have hSepShort : ∀ k l : ℕ, k < l → t (v k) + δ k < t (v l) := by
    intro k l hkl
    have hSmall : t (v k) + δ k ≤ t (v k) + w (v k) :=
      add_le_add_right (hδw k) _
    exact lt_of_le_of_lt hSmall (hSep k l hkl)
  refine ⟨i, t, w, v, sSource, sState, A, B, δ, p, η, N,
    hv, hLimit, hSep, hSepShort, hSepInternal,
    hOldCost, hEndCosts, ?_, ?_⟩
  · intro k
    obtain ⟨ht, hw, hEnd, hPeaks, hsSource, hsState, hMax,
      hp, hη, hpEnd, hSpike, hZero⟩ := hWindows k
    exact ⟨ht, hw, hEnd, hPeaks, hsSource, hsState, hMax,
      hA k, hB k, hδ k, hδw k, hWidth k, hFloor k,
      hp, hη, hpEnd, hSpike, hZero⟩
  · intro k hThreshold
    obtain ⟨ht, hw, hEnd, _hPeaks, _hsSource, hsState, hMax,
      _hp, _hη, _hpEnd, hSpike, _hZero⟩ := hWindows k
    have hx : 0 < t (v k) :=
      lt_trans hClass.terminal_start.1
        (lt_trans hb.1 (lt_trans (hc (v k)).1 ht.1))
    have htClass : t (v k) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans (hc (v k)).1 ht.1), ht.2⟩
    have hsClass : sState k ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le htClass.1 hsState.1,
        lt_of_le_of_lt hsState.2 hEnd⟩
    rcases hAlternative k with hRiccati | hCompression | hCutoff |
        hSpectral | hSource | hDiss | hSourceFloor
    · exact Or.inl (Or.inl hRiccati)
    · exact Or.inl (Or.inr (Or.inl hCompression))
    · exact Or.inl (Or.inr (Or.inr (Or.inl hCutoff)))
    · have hSplit := h3Critical_scalar_linearMax_anchorOrExcursion
        (max 1 (σ (v k)) + 1) h3AuditInitialLerayEnergyCoefficient
        ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖
        ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖
        ‖h3AuditActualSpectralVelocityTotal hH3 (sState k) -
          h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖
        h3AuditInitialLerayEnergyCoefficient_nonneg
        (h3Critical_norm_le_anchor_add_excursion _ _) hSpectral
      rcases hSplit with hAnchor | hExc
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hAnchor))))
      · have hNorm : ε k <
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k) -
              h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ :=
          h3Critical_scalar_spectralThreshold_forces_excursion
            (max 1 (σ (v k)) + 1) h3AuditInitialLerayEnergyCoefficient
            (ε k) _ h3AuditInitialLerayEnergyCoefficient_nonneg
            hThreshold hExc
        have hSourceBound : ∀ r : ℝ,
            r ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
              ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ := by
          intro r hr
          exact (hMax r hr).1
        have hClock := h3Critical_actualSpectralExcursion_PDEClockOrHighRadial
          hH3 (R k) (t (v k)) (w (v k)) (sState k)
          ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ (ε k)
          (hR k).le hx hw hEnd hsState (norm_nonneg _) (hε k).le
          hSourceBound hNorm.le
        rcases hClock with hLow | hHigh
        · exact Or.inr (Or.inl hLow)
        · rcases h3Critical_highTemporalMass_forces_onePhysicalDissipationSpike
            hH3 hClass (t (v k)) (sState k) (R k) (ε k)
            htClass hsClass (hR k) hHigh with hAtAnchor | hAtMax
          · exact Or.inr (Or.inr (Or.inl hAtAnchor))
          · exact Or.inr (Or.inr (Or.inr (hSpike hAtMax)))
    · have hSplit := h3Critical_scalar_quadraticMax_anchorOrExcursion
        (4 * q (v k))
        ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖
        ‖h3PathActualProjectedMomentumSource244 hH3 (t (v k))‖
        ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k) -
          h3PathActualProjectedMomentumSource244 hH3 (t (v k))‖
        (norm_nonneg _) (h3Critical_norm_le_anchor_add_excursion _ _)
        (norm_nonneg _) (norm_nonneg _) hSource
      rcases hSplit with hSrcAnchor | hSrcExc
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSrcAnchor)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSrcExc))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hDiss)))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hSourceFloor)))))))

end
end PrimeTensor.Bridge.Euclidean

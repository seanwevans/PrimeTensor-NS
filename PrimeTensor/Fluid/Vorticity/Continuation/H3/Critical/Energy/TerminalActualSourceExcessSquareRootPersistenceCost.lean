import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessDissipationSurplus
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourcePeakSquareRootQuarticCalibration
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourcePeakCofinalConstructiveQuarticCosts
import Mathlib.Tactic

/-!
# Calibrated physical persistence at the enhanced source-driven dissipation floor

A source peak above the original kinetic barrier by 2Q automatically peaks
above the barrier at the higher physical dissipation floor M+Q/κ by Q.
The existing square-root quartic PDE clock can consequently preserve the
ENHANCED high-H³ dissipation floor. The surviving source margin P'>Q also
gives an explicit lower bound for the selected time width in terms of Q and
the observed compact-window physical PDE costs.

The cofinal theorem selects a single actual Fourier component, originally
separated full windows, and a family of newly calibrated subwindows. Their
physical H³ dissipation pays the enhanced width cost; no terminal-uniform
cost ceiling or nonsummability is asserted.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeSourceExcessSqrtCost
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSourceExcessSqrtCost :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The exact physically enhanced dissipation threshold corresponding to
an additional source amplitude Q. -/
noncomputable def h3CriticalSourceExcessEnhancedFloor (M Q : ℝ) : ℝ :=
  M + Q / (3 * (3 + h3AuditInitialLerayEnergyCoefficient))

/-- Moving the physical high-radial dissipation floor upward by Q/κ
increases the established kinetic-anchored Fourier-source barrier by AT MOST
Q, including its `max _ 0` positive-part truncation. -/
theorem h3Critical_sourceExcess_enhancedBarrier_le_original_add_margin
    (E σ M Q : ℝ) (hQ : 0 ≤ Q) :
    h3CriticalSourceDrivenHighDissipationBarrier E σ
      (h3CriticalSourceExcessEnhancedFloor M Q) ≤
    h3CriticalSourceDrivenHighDissipationBarrier E σ M + Q := by
  let K : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let κ : ℝ := 3 * K
  let X : ℝ := K * (1 + 6 * E +
    3 * (σ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling σ * E) + M))
  have hCL : 0 ≤ h3AuditInitialLerayEnergyCoefficient :=
    h3AuditInitialLerayEnergyCoefficient_nonneg
  have hκ : 0 < κ := by
    dsimp only [κ, K]
    positivity
  have hCancel : κ * (Q / κ) = Q := by
    field_simp [ne_of_gt hκ]
  have hShift :
      K * (1 + 6 * E + 3 *
        (σ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling σ * E) +
          h3CriticalSourceExcessEnhancedFloor M Q)) = X + Q := by
    calc
      K * (1 + 6 * E + 3 *
        (σ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling σ * E) +
          h3CriticalSourceExcessEnhancedFloor M Q)) =
          X + κ * (Q / κ) := by
            dsimp only [h3CriticalSourceExcessEnhancedFloor, X, κ]
            ring
      _ = X + Q := by rw [hCancel]
  have hX : max (X + Q) 0 ≤ max X 0 + Q := by
    apply max_le
    · linarith only [le_max_left X 0]
    · linarith only [le_max_right X 0, hQ]
  dsimp only [h3CriticalSourceDrivenHighDissipationBarrier]
  rw [show K * (1 + 6 * E + 3 *
      (σ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling σ * E) +
        h3CriticalSourceExcessEnhancedFloor M Q)) = X + Q from hShift]
  exact hX

/-- An observed strict source peak with 2Q additional amplitude has at
least Q excess relative to the stronger dissipation floor M+Q/κ. -/
theorem h3Critical_sourceExcess_doublePeak_survives_enhancedBarrier
    (E σ M Q N : ℝ) (hQ : 0 ≤ Q)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier E σ M + 2 * Q < N) :
    h3CriticalSourceDrivenHighDissipationBarrier E σ
        (h3CriticalSourceExcessEnhancedFloor M Q) + Q < N := by
  have hBarrier := h3Critical_sourceExcess_enhancedBarrier_le_original_add_margin
    E σ M Q hQ
  linarith only [hBarrier, hPeak]

/-- A larger TRUE source excess makes the square-root radius smaller and
therefore gives a longer quartic time clock. -/
theorem h3Critical_squareRootRadius_antitone_in_sourceExcess
    (σ P Q A B : ℝ) (hQ : 0 < Q) (hQP : Q ≤ P) (hB : 0 ≤ B) :
    h3CriticalSourcePeakSquareRootRadius σ P A B ≤
      h3CriticalSourcePeakSquareRootRadius σ Q A B := by
  have hP : 0 < P := lt_of_lt_of_le hQ hQP
  have hK : 0 ≤ A ^ 2 * B := mul_nonneg (sq_nonneg A) hB
  have hS : 0 ≤ Real.sqrt (A ^ 2 * B) := Real.sqrt_nonneg _
  have hRatio : Real.sqrt (A ^ 2 * B) / P ≤
      Real.sqrt (A ^ 2 * B) / Q := by
    apply (div_le_div_iff₀ hP hQ).2
    exact mul_le_mul_of_nonneg_left hQP hS
  dsimp only [h3CriticalSourcePeakSquareRootRadius]
  linarith only [hRatio]

/-- In addition to a positive duration, a known source margin Q supplies
an explicit LOWER clock-width bound, with local physical PDE costs A and B.
It is a relative bound; those costs may grow on the terminal sequence. -/
theorem h3Critical_squareRootClock_width_lowerBound_from_sourceExcess
    (σ P Q A B w : ℝ) (hQ : 0 < Q) (hQP : Q ≤ P) (hB : 0 ≤ B) :
    min w (1 / (h3CriticalSourcePeakSquareRootRadius σ Q A B) ^ 4) ≤
      min w (1 / (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4) := by
  have hP : 0 < P := lt_of_lt_of_le hQ hQP
  have hRle := h3Critical_squareRootRadius_antitone_in_sourceExcess
    σ P Q A B hQ hQP hB
  have hK : 0 ≤ A ^ 2 * B := mul_nonneg (sq_nonneg A) hB
  have hRadius := h3Critical_positiveSourceMargin_squareRootDominantQuarticRadius
    P (A ^ 2 * B) σ hP hK
  have hR : 0 < h3CriticalSourcePeakSquareRootRadius σ P A B :=
    lt_of_lt_of_le (by norm_num) hRadius.1
  have hPow :
      (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4 ≤
      (h3CriticalSourcePeakSquareRootRadius σ Q A B) ^ 4 :=
    pow_le_pow_left₀ hR.le hRle 4
  have hRecip :
      1 / (h3CriticalSourcePeakSquareRootRadius σ Q A B) ^ 4 ≤
      1 / (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4 :=
    one_div_le_one_div_of_le (pow_pos hR 4) hPow
  exact min_le_min_left w hRecip

/-- The ACTUAL physical PDE persists the enhanced dissipation threshold
M+Q/κ on a calibrated quartic clock. Because the shifted peak margin P'>Q,
the clock is bounded below by one using the prescribed source excess Q,
not the unknown chosen strict peak margin. -/
theorem h3Critical_strictDoubleSourceExcess_enhancedSquareRootPersistence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (M Q C E w : ℝ) (hM : 0 ≤ M) (hQ : 0 < Q)
    (hw : 0 < w) (hEnd : t + w < T)
    (hCeil : ∀ s : ℝ, s ∈ Set.Icc t (t + w) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C)
    (hState : ∀ s : ℝ, s ∈ Set.Icc t (t + w) →
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M + 2 * Q <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖) :
    ∃ P A B R δ : ℝ,
      Q < P ∧
      P = (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ
          (h3CriticalSourceExcessEnhancedFloor M Q)) ∧
      A = (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ + E)) ∧
      B = (12 * C ^ 2 + 2 * (velocityH3DissipationAt u t +
        h3CriticalSourceExcessEnhancedFloor M Q)) ∧
      R = h3CriticalSourcePeakSquareRootRadius σ P A B ∧
      δ = min w (1 / R ^ 4) ∧
      1 ≤ R ∧ σ ≤ R ∧ 0 < δ ∧ δ ≤ w ∧ R ^ 4 * δ ≤ 1 ∧
      min w (1 / (h3CriticalSourcePeakSquareRootRadius σ Q A B) ^ 4) ≤ δ ∧
      ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        h3CriticalSourceExcessEnhancedFloor M Q <
          h3PathActualHighRadialDissipation244 σ
            (h3AuditActualSpectralVelocityTotal hH3 s) := by
  have hCL : 0 ≤ h3AuditInitialLerayEnergyCoefficient :=
    h3AuditInitialLerayEnergyCoefficient_nonneg
  have hκ : 0 < 3 * (3 + h3AuditInitialLerayEnergyCoefficient) := by
    positivity
  have hMQ : 0 ≤ h3CriticalSourceExcessEnhancedFloor M Q := by
    dsimp only [h3CriticalSourceExcessEnhancedFloor]
    exact add_nonneg hM (div_nonneg hQ.le hκ.le)
  have hShift := h3Critical_sourceExcess_doublePeak_survives_enhancedBarrier
    (velocityH3Energy0At u b) σ M Q
    (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    hQ.le hPeak
  have hPeakShift :
      h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ
        (h3CriticalSourceExcessEnhancedFloor M Q) <
          ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ := by
    linarith only [hShift, hQ]
  obtain ⟨P, A, B, R, δ, hP, hA, hB, hR, hδ,
      hRone, hσR, hδpos, hδw, hClock, hFloor⟩ :=
    h3Critical_strictSourcePeak_squareRootCalibratedQuarticPersistence
      hH3 hClass b hb ρ σ hσ i t ht
      (h3CriticalSourceExcessEnhancedFloor M Q) C E w hMQ
      hw hEnd hCeil hState hPeakShift
  have hPgt : Q < P := by
    rw [hP]
    linarith only [hShift]
  have hB0 : 0 ≤ B := by
    rw [hB]
    have hD := velocityH3DissipationAt_nonneg u t
    positivity
  have hWidth :
      min w (1 / (h3CriticalSourcePeakSquareRootRadius σ Q A B) ^ 4) ≤ δ := by
    calc
      _ ≤ min w (1 / (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4) :=
        h3Critical_squareRootClock_width_lowerBound_from_sourceExcess
          σ P Q A B w hQ hPgt.le hB0
      _ = δ := by rw [← hR, ← hδ]
  exact ⟨P, A, B, R, δ, hPgt, hP, hA, hB, hR, hδ,
    hRone, hσR, hδpos, hδw, hClock, hWidth, hFloor⟩


/-- Under no physical L² terminal trace, arbitrary positive additional source
margins Q_k produce SAME-WINDOW enhanced physical high-H³ dissipation floors
and certified square-root quartic durations. Each duration has an explicit
positive lower bound in terms of Q_k and the actual local PDE costs, and the
full H³ viscous integral absorbs its increased height-times-width cost.
The original source windows (not previously shortened windows) certify
pairwise disjointness. No terminal-uniform constant is requested. -/
theorem h3Critical_noL2Trace_cofinalEnhancedSquareRootWidths_and_fullCosts
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M Q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hQ : ∀ n, 0 < Q n) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ C E P A B R δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        0 ≤ C k ∧ 0 ≤ E k ∧ Q (v k) < P k ∧
        P k = (‖h3CriticalActualProjectedHighpassFourierSource hH3
            (ρ (v k)) i (t (v k))‖ -
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) (σ (v k))
            (h3CriticalSourceExcessEnhancedFloor (M (v k)) (Q (v k)))) ∧
        A k = (3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ + E k)) ∧
        B k = (12 * (C k) ^ 2 + 2 *
          (velocityH3DissipationAt u (t (v k)) +
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (Q (v k)))) ∧
        R k = h3CriticalSourcePeakSquareRootRadius
          (σ (v k)) (P k) (A k) (B k) ∧
        δ k = min (w (v k)) (1 / (R k) ^ 4) ∧
        1 ≤ R k ∧ σ (v k) ≤ R k ∧
        0 < δ k ∧ δ k ≤ w (v k) ∧ (R k) ^ 4 * δ k ≤ 1 ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (Q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        ∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) →
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (Q (v k)) <
            h3PathActualHighRadialDissipation244 (σ (v k))
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
              (M (v k)) (Q (v k))) * ENNReal.ofReal (δ k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) := by
  let Qdouble : ℕ → ℝ := fun n => 2 * Q n
  have hQdouble : ∀ n, 0 ≤ Qdouble n := by
    intro n
    dsimp only [Qdouble]
    exact mul_nonneg (by norm_num) (hQ n).le
  obtain ⟨i, t, w, v, hv, hLimit, hSeparated, hWindows, _hOldCost⟩ :=
    h3Critical_noL2Trace_sourceExcess_disjointEnhancedFullDissipationCosts
      hH3 hClass b hb hNoTrace c ρ σ M Qdouble hc hcLimit hρ hσ hM hQdouble
  have hSelected (k : ℕ) :
      ∃ C E P A B R δ : ℝ,
        0 ≤ C ∧ 0 ≤ E ∧ Q (v k) < P ∧
        P = (‖h3CriticalActualProjectedHighpassFourierSource hH3
            (ρ (v k)) i (t (v k))‖ -
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) (σ (v k))
            (h3CriticalSourceExcessEnhancedFloor (M (v k)) (Q (v k)))) ∧
        A = (3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ + E)) ∧
        B = (12 * C ^ 2 + 2 *
          (velocityH3DissipationAt u (t (v k)) +
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (Q (v k)))) ∧
        R = h3CriticalSourcePeakSquareRootRadius (σ (v k)) P A B ∧
        δ = min (w (v k)) (1 / R ^ 4) ∧
        1 ≤ R ∧ σ (v k) ≤ R ∧
        0 < δ ∧ δ ≤ w (v k) ∧ R ^ 4 * δ ≤ 1 ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (Q (v k)) A B) ^ 4) ≤ δ ∧
        ∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ) →
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (Q (v k)) <
            h3PathActualHighRadialDissipation244 (σ (v k))
              (h3AuditActualSpectralVelocityTotal hH3 s) := by
    have ht : t (v k) ∈ Set.Ioo b T :=
      ⟨lt_trans (hc (v k)).1 (hWindows k).1.1, (hWindows k).1.2⟩
    have hAtStart : t (v k) ∈ Set.Icc
        (t (v k)) (t (v k) + w (v k)) :=
      ⟨le_rfl, le_add_of_nonneg_right ((hWindows k).2.1).le⟩
    have hDoublePeak :
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) (σ (v k)) (M (v k)) +
          2 * Q (v k) <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3
          (ρ (v k)) i (t (v k))‖ := by
      exact ((hWindows k).2.2.2 (t (v k)) hAtStart).1
    have hPeak :
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) (σ (v k)) (M (v k)) <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3
          (ρ (v k)) i (t (v k))‖ := by
      have hQnonneg : 0 ≤ 2 * Q (v k) :=
        mul_nonneg (by norm_num) (hQ (v k)).le
      linarith only [hDoublePeak, hQnonneg]
    obtain ⟨C, E, _R0, _δ0, hC0, hE0, _hR0, _hσR0,
        _hδ0, _hδw0, _hClock0, hCeils, _hFloor0⟩ :=
      h3Critical_strictSourcePeak_automaticPersistence_withoutLocalCeilingAssumptions
        hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
        (t (v k)) ht (M (v k)) (w (v k)) (hM (v k))
        (hWindows k).2.1 (hWindows k).2.2.1 hPeak
    obtain ⟨P, A, B, R, δ, hExcess, hP, hA, hB, hRcal, hδcal,
        hR, hσR, hδ, hδw, hClock, hWidth, hFloor⟩ :=
      h3Critical_strictDoubleSourceExcess_enhancedSquareRootPersistence
        hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
        (t (v k)) ht (M (v k)) (Q (v k)) C E (w (v k))
        (hM (v k)) (hQ (v k)) (hWindows k).2.1 (hWindows k).2.2.1
        (fun s hs => (hCeils s hs).1)
        (fun s hs => (hCeils s hs).2) hDoublePeak
    exact ⟨C, E, P, A, B, R, δ, hC0, hE0, hExcess, hP, hA, hB,
      hRcal, hδcal, hR, hσR, hδ, hδw, hClock, hWidth, hFloor⟩
  choose C E P A B R δ hC0 hE0 hExcess hP hA hB hRcal hδcal
    hR hσR hδ hδw hClock hWidth hFloor using hSelected
  refine ⟨i, t, w, v, C, E, P, A, B, R, δ, hv, hLimit, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hWindows k).1, (hWindows k).2.1,
      (hWindows k).2.2.1, hC0 k, hE0 k, hExcess k,
      hP k, hA k, hB k, hRcal k, hδcal k,
      hR k, hσR k, hδ k, hδw k, hClock k, hWidth k, hFloor k⟩
  · intro k l hkl
    have hShort : t (v k) + δ k ≤ t (v k) + w (v k) :=
      add_le_add_right (hδw k) (t (v k))
    exact lt_of_le_of_lt hShort (hSeparated k l hkl)
  · intro m
    apply Finset.sum_le_sum
    intro k _hk
    have hLower :
        (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
            (M (v k)) (Q (v k))) ∂volume) ≤
        ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := by
      apply h3Critical_extendedWindowCost_of_pointwiseFloor
      intro s hs
      have hsClass : s ∈ Set.Ioo a T := by
        have hStart : a < t (v k) :=
          lt_trans hb.1 (lt_trans (hc (v k)).1 (hWindows k).1.1)
        have hShort : t (v k) + δ k ≤ t (v k) + w (v k) :=
          add_le_add_right (hδw k) (t (v k))
        exact ⟨lt_of_lt_of_le hStart hs.1,
          lt_of_le_of_lt (le_trans hs.2 hShort) (hWindows k).2.2.1⟩
      exact (hFloor k s hs).le.trans
        (h3Critical_actualHighRadialDissipation_le_full
          hH3 hClass s hsClass (σ (v k)))
    calc
      ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
          (M (v k)) (Q (v k))) * ENNReal.ofReal (δ k) =
          (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
              (M (v k)) (Q (v k))) ∂volume) :=
        (h3Critical_extendedConstantWindow_eq_heightWidth
          (t (v k)) (δ k)
          (h3CriticalSourceExcessEnhancedFloor (M (v k)) (Q (v k)))
          (hδ k).le).symm
      _ ≤ ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := hLower

end
end PrimeTensor.Bridge.Euclidean

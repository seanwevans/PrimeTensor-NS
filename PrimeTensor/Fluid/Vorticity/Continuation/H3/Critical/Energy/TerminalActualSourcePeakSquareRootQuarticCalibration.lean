import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourcePeakMarginPolynomialCharge
import Mathlib.Tactic

/-!
# Square-root quartic physical clock: stronger actual source-peak persistence

The physical source-drop estimate requires R² P² > A² B. The earlier
calibration chose R=max(1,σ)+1+A²B/P², squaring the required frequency
scale. Here choose R=max(1,σ)+1+sqrt(A²B)/P instead. On the true physical
PDE this yields a nonzero lifetime δ=min(w,R⁻⁴) and changes the polynomial
source-margin cost from eighth degree to FOURTH degree.

No global H³ regularity assertion or terminal-uniform source ceiling follows.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeSqrtQuartic
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSqrtQuartic :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Economical exact radius: no artificial quadratic loss in A²B/P². -/
noncomputable def h3CriticalSourcePeakSquareRootRadius
    (σ P A B : ℝ) : ℝ :=
  max 1 σ + 1 + Real.sqrt (A ^ 2 * B) / P

/-- The source peak forces exactly the squared budget, so a square-root
frequency increment suffices. Both positivity and the strict gap are
proved without assuming a terminal-uniform bound. -/
theorem h3Critical_positiveSourceMargin_squareRootDominantQuarticRadius
    (P K σ : ℝ) (hP : 0 < P) (hK : 0 ≤ K) :
    1 ≤ max 1 σ + 1 + Real.sqrt K / P ∧
    σ ≤ max 1 σ + 1 + Real.sqrt K / P ∧
    K < (max 1 σ + 1 + Real.sqrt K / P) ^ 2 * P ^ 2 := by
  let X : ℝ := (max 1 σ + 1) * P
  let Y : ℝ := Real.sqrt K
  let R : ℝ := max 1 σ + 1 + Y / P
  have hQone : 1 ≤ max 1 σ := le_max_left _ _
  have hQsigma : σ ≤ max 1 σ := le_max_right _ _
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hRatio : 0 ≤ Y / P := div_nonneg hY hP.le
  have hRone : 1 ≤ R := by
    dsimp only [R]
    linarith only [hQone, hRatio]
  have hRσ : σ ≤ R := by
    dsimp only [R]
    linarith only [hQsigma, hRatio]
  have hX : 0 < X := mul_pos (by linarith only [hQone]) hP
  have hXY : 0 ≤ X * Y := mul_nonneg hX.le hY
  have hXsq : 0 < X ^ 2 := pow_pos hX 2
  have hStrict : Y ^ 2 < (X + Y) ^ 2 := by
    nlinarith only [hXsq, hXY]
  have hProduct : R * P = X + Y := by
    dsimp only [R, X, Y]
    field_simp [ne_of_gt hP]
    <;> ring
  have hYsq : Y ^ 2 = K := Real.sq_sqrt hK
  have hGap : K < R ^ 2 * P ^ 2 := by
    calc
      K = Y ^ 2 := hYsq.symm
      _ < (X + Y) ^ 2 := hStrict
      _ = R ^ 2 * P ^ 2 := by rw [← hProduct]; ring
  exact ⟨hRone, hRσ, hGap⟩

/-- A fourth-power identity clears the square-root frequency denominator
using P⁴ rather than P⁸. -/
theorem h3Critical_squareRootRadius_exactFourthPowerIdentity
    (σ P A B : ℝ) (hP : 0 < P) :
    (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4 * P ^ 4 =
      ((max 1 σ + 1) * P + Real.sqrt (A ^ 2 * B)) ^ 4 := by
  have hProduct : h3CriticalSourcePeakSquareRootRadius σ P A B * P =
      (max 1 σ + 1) * P + Real.sqrt (A ^ 2 * B) := by
    dsimp only [h3CriticalSourcePeakSquareRootRadius]
    field_simp [ne_of_gt hP]
    <;> ring
  calc
    (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4 * P ^ 4 =
        (h3CriticalSourcePeakSquareRootRadius σ P A B * P) ^ 4 := by ring
    _ = ((max 1 σ + 1) * P + Real.sqrt (A ^ 2 * B)) ^ 4 := by
      rw [hProduct]

/-- Clear the radical itself by the sharp elementary inequality
(x+y)² ≤ 2(x²+y²), obtaining a denominator-free polynomial cost.
The resulting degree four replaces the old degree eight in P. -/
theorem h3Critical_squareRootRadius_fourthPowerPolynomialCeiling
    (σ P A B : ℝ) (hP : 0 < P) (hB : 0 ≤ B) :
    (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4 * P ^ 4 ≤
      4 * (((max 1 σ + 1) ^ 2 * P ^ 2 + A ^ 2 * B) ^ 2) := by
  let X : ℝ := (max 1 σ + 1) * P
  let Y : ℝ := Real.sqrt (A ^ 2 * B)
  have hK : 0 ≤ A ^ 2 * B := mul_nonneg (sq_nonneg A) hB
  have hYsq : Y ^ 2 = A ^ 2 * B := Real.sq_sqrt hK
  have hQuad : (X + Y) ^ 2 ≤ 2 * (X ^ 2 + Y ^ 2) := by
    nlinarith only [sq_nonneg (X - Y)]
  have hQuadSq : ((X + Y) ^ 2) ^ 2 ≤
      (2 * (X ^ 2 + Y ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) hQuad 2
  calc
    (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4 * P ^ 4 =
        (X + Y) ^ 4 := by
          dsimp only [X, Y]
          exact h3Critical_squareRootRadius_exactFourthPowerIdentity
            σ P A B hP
    _ = ((X + Y) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (X ^ 2 + Y ^ 2)) ^ 2 := hQuadSq
    _ = 4 * (((max 1 σ + 1) ^ 2 * P ^ 2 + A ^ 2 * B) ^ 2) := by
      dsimp only [X]
      rw [hYsq]
      ring


/-- The square-root calibration never exceeds the previous calibrated
radius when the PDE cost K=A²B already dominates P². This is precisely the
large-cost regime in which the old formula doubled the frequency exponent. -/
theorem h3Critical_squareRootRadius_le_old_of_costDominance
    (σ P A B : ℝ) (hP : 0 < P) (hB : 0 ≤ B)
    (hDom : P ^ 2 ≤ A ^ 2 * B) :
    h3CriticalSourcePeakSquareRootRadius σ P A B ≤
      h3CriticalSourcePeakCalibratedRadius σ P A B := by
  let K : ℝ := A ^ 2 * B
  let S : ℝ := Real.sqrt K
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg A) hB
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSquare : S ^ 2 = K := Real.sq_sqrt hK
  have hDomK : P ^ 2 ≤ K := hDom
  have hPS : P ≤ S := by
    nlinarith only [hDomK, hSquare, hP.le, hS]
  have hProduct : S * P ≤ K := by
    calc
      S * P ≤ S * S := mul_le_mul_of_nonneg_left hPS hS
      _ = K := by nlinarith only [hSquare]
  have hScaled := mul_le_mul_of_nonneg_right hProduct hP.le
  have hDiv : S / P ≤ K / P ^ 2 := by
    apply (div_le_div_iff₀ hP (pow_pos hP 2)).2
    nlinarith only [hScaled]
  dsimp only [h3CriticalSourcePeakSquareRootRadius,
    h3CriticalSourcePeakCalibratedRadius]
  change max 1 σ + 1 + S / P ≤ max 1 σ + 1 + K / P ^ 2
  linarith only [hDiv]

/-- In the same regime the improved quartic time width is at least the old
calibrated width, for any nonnegative or arbitrary available physical width. -/
theorem h3Critical_squareRootQuarticWidth_ge_old_of_costDominance
    (σ P A B w : ℝ) (hP : 0 < P) (hB : 0 ≤ B)
    (hDom : P ^ 2 ≤ A ^ 2 * B) :
    min w (1 / (h3CriticalSourcePeakCalibratedRadius σ P A B) ^ 4) ≤
      min w (1 / (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4) := by
  let R : ℝ := h3CriticalSourcePeakSquareRootRadius σ P A B
  let Q : ℝ := h3CriticalSourcePeakCalibratedRadius σ P A B
  have hK : 0 ≤ A ^ 2 * B := mul_nonneg (sq_nonneg A) hB
  have hQone : 1 ≤ max 1 σ := le_max_left _ _
  have hRatio : 0 ≤ Real.sqrt (A ^ 2 * B) / P :=
    div_nonneg (Real.sqrt_nonneg _) hP.le
  have hRpos : 0 < R := by
    dsimp only [R, h3CriticalSourcePeakSquareRootRadius]
    linarith only [hQone, hRatio]
  have hRQ : R ≤ Q :=
    h3Critical_squareRootRadius_le_old_of_costDominance σ P A B hP hB hDom
  have hPowers : R ^ 4 ≤ Q ^ 4 :=
    pow_le_pow_left₀ hRpos.le hRQ 4
  have hInverse : 1 / Q ^ 4 ≤ 1 / R ^ 4 :=
    one_div_le_one_div_of_le (pow_pos hRpos 4) hPowers
  exact min_le_min_left w hInverse

theorem h3Critical_strictSourcePeak_squareRootCalibratedQuarticPersistence
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
      R = h3CriticalSourcePeakSquareRootRadius σ P A B ∧
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
  let R : ℝ := h3CriticalSourcePeakSquareRootRadius σ P A B
  have hRadius :=
    h3Critical_positiveSourceMargin_squareRootDominantQuarticRadius
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



/-- Cofinal separated strict physical source peaks have the improved
square-root-frequency persistence windows and retain full H³ dissipation
charges. This is not a uniform lower bound on their time widths. -/
theorem h3Critical_noL2Trace_cofinalSquareRootQuarticWidths_and_fullCosts
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
        R k = h3CriticalSourcePeakSquareRootRadius
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
        R = h3CriticalSourcePeakSquareRootRadius (σ (v k)) P A B ∧
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
      h3Critical_strictSourcePeak_squareRootCalibratedQuarticPersistence
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


/-- A finite physical charge on the sqrt-calibrated quartic clock either
compresses the available original interval or forces a fourth-degree
polynomial constraint on the actual Fourier-source margin P. -/
theorem h3Critical_squareRootFiniteCharge_forces_width_or_quarticMargin
    (σ P A B w M J : ℝ)
    (hP : 0 < P) (hB : 0 ≤ B) (hM : 0 < M) (hJ : 0 < J)
    (hCharge :
      M * min w (1 / (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4) ≤ J) :
    w ≤ J / M ∨
      M * P ^ 4 ≤
        4 * J * (((max 1 σ + 1) ^ 2 * P ^ 2 + A ^ 2 * B) ^ 2) := by
  let R : ℝ := h3CriticalSourcePeakSquareRootRadius σ P A B
  have hK : 0 ≤ A ^ 2 * B := mul_nonneg (sq_nonneg A) hB
  have hRadius := h3Critical_positiveSourceMargin_squareRootDominantQuarticRadius
    P (A ^ 2 * B) σ hP hK
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) hRadius.1
  have hAlt := h3Critical_calibratedQuarticWidth_finiteCharge_forces_compression
    w R M J hR hM hJ hCharge
  rcases hAlt with hShort | hRadial
  · exact Or.inl hShort
  · right
    have hNecessary : M ≤ R ^ 4 * J :=
      (div_le_iff₀ hJ).mp hRadial
    have hP4 : 0 ≤ P ^ 4 := by positivity
    have hScaled := mul_le_mul_of_nonneg_right hNecessary hP4
    have hUpper := h3Critical_squareRootRadius_fourthPowerPolynomialCeiling
      σ P A B hP hB
    calc
      M * P ^ 4 ≤ (R ^ 4 * J) * P ^ 4 := hScaled
      _ = J * (R ^ 4 * P ^ 4) := by ring
      _ ≤ J * (4 * (((max 1 σ + 1) ^ 2 * P ^ 2 + A ^ 2 * B) ^ 2)) :=
        mul_le_mul_of_nonneg_left hUpper hJ.le
      _ = 4 * J * (((max 1 σ + 1) ^ 2 * P ^ 2 + A ^ 2 * B) ^ 2) := by
        ring

/-- The fourth-degree constraint is expressed against a genuine physical
viscous-dissipation integral rather than a hypothetical scalar cost. -/
theorem h3Critical_squareRootPhysicalCharge_forces_width_or_quarticMargin
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t w δ σ P A B M J : ℝ)
    (hP : 0 < P) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hM : 0 < M) (hJ : 0 < J)
    (hCal : δ = min w
      (1 / (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4))
    (hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      M ≤ velocityH3DissipationAt u s)
    (hBudget :
      (∫⁻ s in Set.Ioc t (t + δ),
        ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ≤
          ENNReal.ofReal J) :
    w ≤ J / M ∨
      M * P ^ 4 ≤
        4 * J * (((max 1 σ + 1) ^ 2 * P ^ 2 + A ^ 2 * B) ^ 2) := by
  have hWidth : δ ≤ J / M :=
    h3Critical_extendedWindowBudget_width_le
      (velocityH3DissipationAt u) t δ M J hδ hM hJ.le
      hFloor hBudget
  have hMul := (le_div_iff₀ hM).1 hWidth
  rw [hCal] at hMul
  have hCharge : M * min w
      (1 / (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4) ≤ J := by
    simpa only [mul_comm] using hMul
  exact h3Critical_squareRootFiniteCharge_forces_width_or_quarticMargin
    σ P A B w M J hP hB hM hJ hCharge

end
end PrimeTensor.Bridge.Euclidean

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessSquareRootPersistenceCost
import Mathlib.Tactic

/-!
# Quintic physical H³ cost from allocating an actual source excess

At a real physical time, a Fourier-source peak exceeding its kinetic-anchored
barrier by 5q can spend q on extra high-radial H³ dissipation and reserve 4q
for the physical square-root-frequency persistence clock. The physical PDE
then supplies a window of certified length, not just a strict-time point.

A finite full physical H³ dissipation charge J on that window forces either
compression of its original available duration w or the new quintic estimate

  64 q^5 <= κ J [16(max(1,σ)+1)^2 q^2 + A² B]^2,
  κ = 3(3+C_L),

where A and B retain their EXACT actual PDE and H³ endpoint meaning.
No uniform terminal source ceiling or global full-H³ dissipation budget is
assumed. The alternative is a necessary concentration constraint, not a
regularity or continuation theorem.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeQuinticPhysicalCharge
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceQuinticPhysicalCharge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- With 5q of physical Fourier source excess, spending q to raise the
high-radial dissipation floor leaves FOUR q of real source margin. This
uses the exact max-truncated kinetic barrier. -/
theorem h3Critical_fivefoldSourceExcess_survives_oneFifthDissipationShift
    (E σ M q N : ℝ) (hq : 0 ≤ q)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier E σ M + 5 * q < N) :
    h3CriticalSourceDrivenHighDissipationBarrier E σ
      (h3CriticalSourceExcessEnhancedFloor M q) + 4 * q < N := by
  have hShift := h3Critical_sourceExcess_enhancedBarrier_le_original_add_margin
    E σ M q hq
  linarith only [hShift, hPeak]

/-- A single actual source peak with five units of source excess pays both
an enhanced physical high-H³ dissipation floor and a quartic clock with
FOUR units of guaranteed remaining margin. A,B and the actual calibrated
radius are returned with their exact physical definitions. -/
theorem h3Critical_fivefoldSourceExcess_physicalOneFifthSquareRootPersistence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (M q C E w : ℝ) (hM : 0 ≤ M) (hq : 0 < q)
    (hw : 0 < w) (hEnd : t + w < T)
    (hCeil : ∀ s : ℝ, s ∈ Set.Icc t (t + w) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C)
    (hState : ∀ s : ℝ, s ∈ Set.Icc t (t + w) →
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M + 5 * q <
      ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖) :
    ∃ P A B R δ : ℝ,
      4 * q < P ∧
      P = (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ
          (h3CriticalSourceExcessEnhancedFloor M q)) ∧
      A = (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ + E)) ∧
      B = (12 * C ^ 2 + 2 * (velocityH3DissipationAt u t +
        h3CriticalSourceExcessEnhancedFloor M q)) ∧
      R = h3CriticalSourcePeakSquareRootRadius σ P A B ∧
      δ = min w (1 / R ^ 4) ∧
      1 ≤ R ∧ σ ≤ R ∧ 0 < δ ∧ δ ≤ w ∧ R ^ 4 * δ ≤ 1 ∧
      min w (1 / (h3CriticalSourcePeakSquareRootRadius σ (4 * q) A B) ^ 4)
        ≤ δ ∧
      ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        h3CriticalSourceExcessEnhancedFloor M q <
          h3PathActualHighRadialDissipation244 σ
            (h3AuditActualSpectralVelocityTotal hH3 s) := by
  have hShift := h3Critical_fivefoldSourceExcess_survives_oneFifthDissipationShift
    (velocityH3Energy0At u b) σ M q
    (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    hq.le hPeak
  have hPeakShift :
      h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ
        (h3CriticalSourceExcessEnhancedFloor M q) <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ := by
    linarith only [hShift, hq]
  have hκ : 0 < 3 * (3 + h3AuditInitialLerayEnergyCoefficient) := by
    have hC := h3AuditInitialLerayEnergyCoefficient_nonneg
    positivity
  have hFloorNonneg : 0 ≤ h3CriticalSourceExcessEnhancedFloor M q := by
    dsimp only [h3CriticalSourceExcessEnhancedFloor]
    exact add_nonneg hM (div_nonneg hq.le hκ.le)
  obtain ⟨P, A, B, R, δ, hP, hA, hB, hR, hδ,
      hRone, hσR, hδpos, hδw, hClock, hFloor⟩ :=
    h3Critical_strictSourcePeak_squareRootCalibratedQuarticPersistence
      hH3 hClass b hb ρ σ hσ i t ht
      (h3CriticalSourceExcessEnhancedFloor M q) C E w hFloorNonneg
      hw hEnd hCeil hState hPeakShift
  have hPgt : 4 * q < P := by
    rw [hP]
    linarith only [hShift]
  have hB0 : 0 ≤ B := by
    rw [hB]
    have hD := velocityH3DissipationAt_nonneg u t
    positivity
  have hFourQ : 0 < 4 * q := mul_pos (by norm_num) hq
  have hWidth :
      min w (1 / (h3CriticalSourcePeakSquareRootRadius σ (4 * q) A B) ^ 4)
        ≤ δ := by
    calc
      _ ≤ min w (1 / (h3CriticalSourcePeakSquareRootRadius σ P A B) ^ 4) :=
        h3Critical_squareRootClock_width_lowerBound_from_sourceExcess
          σ P (4 * q) A B w hFourQ hPgt.le hB0
      _ = δ := by rw [← hR, ← hδ]
  exact ⟨P, A, B, R, δ, hPgt, hP, hA, hB, hR, hδ,
    hRone, hσR, hδpos, hδw, hClock, hWidth, hFloor⟩

/-- Non-geometric compression of a ONE-FIFTH-enhanced source peak forces
fifth-degree concentration of the actual source amplitude q. The fourth-
degree bound for the remaining clock margin 4q is promoted to a quintic
bound because the enhanced physical dissipation floor already contains q/κ.
-/
theorem h3Critical_fivefoldSourceExcess_noncompressedCharge_forces_quintic
    (σ q A B w M J : ℝ)
    (hq : 0 < q) (hB : 0 ≤ B) (hM : 0 ≤ M) (hJ : 0 < J)
    (hNoncompressed :
      J / h3CriticalSourceExcessEnhancedFloor M q < w)
    (hCharge : h3CriticalSourceExcessEnhancedFloor M q *
        min w (1 / (h3CriticalSourcePeakSquareRootRadius
          σ (4 * q) A B) ^ 4) ≤ J) :
    64 * q ^ 5 ≤
      (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
        (16 * (max 1 σ + 1) ^ 2 * q ^ 2 + A ^ 2 * B) ^ 2 := by
  let κ : ℝ := 3 * (3 + h3AuditInitialLerayEnergyCoefficient)
  let M' : ℝ := h3CriticalSourceExcessEnhancedFloor M q
  have hκ : 0 < κ := by
    dsimp only [κ]
    have hC := h3AuditInitialLerayEnergyCoefficient_nonneg
    positivity
  have hMp : 0 < M' := by
    dsimp only [M', h3CriticalSourceExcessEnhancedFloor]
    have hDiv : 0 < q / κ := div_pos hq hκ
    linarith only [hM, hDiv]
  have hAlt := h3Critical_squareRootFiniteCharge_forces_width_or_quarticMargin
    σ (4 * q) A B w M' J (mul_pos (by norm_num) hq)
    hB hMp hJ hCharge
  have hPoly :
      M' * (4 * q) ^ 4 ≤
      4 * J * (((max 1 σ + 1) ^ 2 * (4 * q) ^ 2 + A ^ 2 * B) ^ 2) := by
    rcases hAlt with hShort | hPoly
    · exact False.elim ((not_le_of_gt hNoncompressed) hShort)
    · exact hPoly
  have hLower : q / κ ≤ M' := by
    dsimp only [M', h3CriticalSourceExcessEnhancedFloor]
    linarith only [hM]
  have hLowerScaled :
      (q / κ) * (4 * q) ^ 4 ≤
        M' * (4 * q) ^ 4 :=
    mul_le_mul_of_nonneg_right hLower (by positivity)
  have hReduced :
      (q / κ) * (4 * q) ^ 4 ≤
        4 * J * (((max 1 σ + 1) ^ 2 * (4 * q) ^ 2 + A ^ 2 * B) ^ 2) :=
    hLowerScaled.trans hPoly
  have hScaled := mul_le_mul_of_nonneg_left hReduced (show 0 ≤ κ / 4 by positivity)
  change 64 * q ^ 5 ≤ κ * J *
    (16 * (max 1 σ + 1) ^ 2 * q ^ 2 + A ^ 2 * B) ^ 2
  calc
    64 * q ^ 5 = (κ / 4) * ((q / κ) * (4 * q) ^ 4) := by
      field_simp [ne_of_gt hκ]
      <;> ring
    _ ≤ (κ / 4) * (4 * J *
        (((max 1 σ + 1) ^ 2 * (4 * q) ^ 2 + A ^ 2 * B) ^ 2)) := hScaled
    _ = κ * J *
        (16 * (max 1 σ + 1) ^ 2 * q ^ 2 + A ^ 2 * B) ^ 2 := by ring

/-- No hypothetical scalar cost: the real H³ viscous-dissipation extended
integral on the certified physical window yields the same quintic source-
amplitude obstruction unless the available time window itself compresses. -/
theorem h3Critical_fivefoldSourceExcess_physicalDissipationBudget_forces_quintic
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t w δ σ q A B M J : ℝ)
    (hq : 0 < q) (hB : 0 ≤ B) (hM : 0 ≤ M) (hJ : 0 < J)
    (hδ : 0 ≤ δ)
    (hCal : δ = min w (1 / (h3CriticalSourcePeakSquareRootRadius
      σ (4 * q) A B) ^ 4))
    (hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      h3CriticalSourceExcessEnhancedFloor M q ≤ velocityH3DissipationAt u s)
    (hBudget :
      (∫⁻ s in Set.Ioc t (t + δ),
        ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ≤
          ENNReal.ofReal J) :
    w ≤ J / h3CriticalSourceExcessEnhancedFloor M q ∨
      64 * q ^ 5 ≤
        (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
          (16 * (max 1 σ + 1) ^ 2 * q ^ 2 + A ^ 2 * B) ^ 2 := by
  have hκ : 0 < 3 * (3 + h3AuditInitialLerayEnergyCoefficient) := by
    have hC := h3AuditInitialLerayEnergyCoefficient_nonneg
    positivity
  have hMp : 0 < h3CriticalSourceExcessEnhancedFloor M q := by
    dsimp only [h3CriticalSourceExcessEnhancedFloor]
    have hDiv := div_pos hq hκ
    linarith only [hM, hDiv]
  have hWidth : δ ≤ J / h3CriticalSourceExcessEnhancedFloor M q :=
    h3Critical_extendedWindowBudget_width_le
      (velocityH3DissipationAt u) t δ
      (h3CriticalSourceExcessEnhancedFloor M q) J
      hδ hMp hJ.le hFloor hBudget
  have hMul := (le_div_iff₀ hMp).1 hWidth
  rw [hCal] at hMul
  have hCharge : h3CriticalSourceExcessEnhancedFloor M q *
      min w (1 / (h3CriticalSourcePeakSquareRootRadius
        σ (4 * q) A B) ^ 4) ≤ J := by
    simpa only [mul_comm] using hMul
  by_cases hShort : w ≤ J / h3CriticalSourceExcessEnhancedFloor M q
  · exact Or.inl hShort
  · right
    exact h3Critical_fivefoldSourceExcess_noncompressedCharge_forces_quintic
      σ q A B w M J hq hB hM hJ (lt_of_not_ge hShort) hCharge


/-- The same quintic alternative is certified by an ACTUAL highpass source
peak and the exact physical H³ PDE, with no independent width calibration
hypothesis. The returned window carries its enhanced full-H³ dissipation
floor, an explicit lower quartic width, and a local-integral budget gate. -/
theorem h3Critical_fivefoldActualSourcePeak_certifiesPhysicalQuinticGate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (M q C E w : ℝ) (hM : 0 ≤ M) (hq : 0 < q)
    (hw : 0 < w) (hEnd : t + w < T)
    (hCeil : ∀ s : ℝ, s ∈ Set.Icc t (t + w) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C)
    (hState : ∀ s : ℝ, s ∈ Set.Icc t (t + w) →
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M + 5 * q <
      ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖) :
    ∃ A B R δ : ℝ,
      A = (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ + E)) ∧
      B = (12 * C ^ 2 + 2 * (velocityH3DissipationAt u t +
        h3CriticalSourceExcessEnhancedFloor M q)) ∧
      1 ≤ R ∧ 0 < δ ∧ δ ≤ w ∧
      min w (1 / (h3CriticalSourcePeakSquareRootRadius σ (4 * q) A B) ^ 4)
        ≤ δ ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        h3CriticalSourceExcessEnhancedFloor M q <
          velocityH3DissipationAt u s) ∧
      (∀ J : ℝ, 0 < J →
        (∫⁻ s in Set.Ioc t (t + δ),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ≤
            ENNReal.ofReal J →
        w ≤ J / h3CriticalSourceExcessEnhancedFloor M q ∨
          64 * q ^ 5 ≤
            (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
              (16 * (max 1 σ + 1) ^ 2 * q ^ 2 + A ^ 2 * B) ^ 2) := by
  obtain ⟨P, A, B, R, δ, _hPgt, _hP, hA, hB, _hRcal, _hδcal,
      hR, _hσR, hδ, hδw, _hClock, hWidth, hFloor⟩ :=
    h3Critical_fivefoldSourceExcess_physicalOneFifthSquareRootPersistence
      hH3 hClass b hb ρ σ hσ i t ht M q C E w
      hM hq hw hEnd hCeil hState hPeak
  have hκ : 0 < 3 * (3 + h3AuditInitialLerayEnergyCoefficient) := by
    have hC := h3AuditInitialLerayEnergyCoefficient_nonneg
    positivity
  have hMp : 0 < h3CriticalSourceExcessEnhancedFloor M q := by
    dsimp only [h3CriticalSourceExcessEnhancedFloor]
    have hDiv := div_pos hq hκ
    linarith only [hM, hDiv]
  have hBnonneg : 0 ≤ B := by
    rw [hB]
    have hD := velocityH3DissipationAt_nonneg u t
    positivity
  have hFull (s : ℝ) (hs : s ∈ Set.Icc t (t + δ)) :
      h3CriticalSourceExcessEnhancedFloor M q <
        velocityH3DissipationAt u s := by
    have hShort : t + δ ≤ t + w := add_le_add_right hδw t
    have hsClass : s ∈ Set.Ioo a T := by
      exact ⟨lt_trans hb.1 (lt_of_lt_of_le ht.1 hs.1),
        lt_of_le_of_lt (le_trans hs.2 hShort) hEnd⟩
    exact lt_of_lt_of_le (hFloor s hs)
      (h3Critical_actualHighRadialDissipation_le_full
        hH3 hClass s hsClass σ)
  refine ⟨A, B, R, δ, hA, hB, hR, hδ, hδw,
    hWidth, hFull, ?_⟩
  intro J hJ hBudget
  have hWidthBudget :
      δ ≤ J / h3CriticalSourceExcessEnhancedFloor M q :=
    h3Critical_extendedWindowBudget_width_le
      (velocityH3DissipationAt u) t δ
      (h3CriticalSourceExcessEnhancedFloor M q) J
      hδ.le hMp hJ.le (fun s hs => (hFull s hs).le) hBudget
  have hBound :
      min w (1 / (h3CriticalSourcePeakSquareRootRadius σ (4 * q) A B) ^ 4)
        ≤ J / h3CriticalSourceExcessEnhancedFloor M q :=
    hWidth.trans hWidthBudget
  have hCharge : h3CriticalSourceExcessEnhancedFloor M q *
      min w (1 / (h3CriticalSourcePeakSquareRootRadius
        σ (4 * q) A B) ^ 4) ≤ J := by
    have hMul := (le_div_iff₀ hMp).1 hBound
    simpa only [mul_comm] using hMul
  by_cases hShort : w ≤ J / h3CriticalSourceExcessEnhancedFloor M q
  · exact Or.inl hShort
  · right
    exact h3Critical_fivefoldSourceExcess_noncompressedCharge_forces_quintic
      σ q A B w M J hq hBnonneg hM hJ (lt_of_not_ge hShort) hCharge

end
end PrimeTensor.Bridge.Euclidean

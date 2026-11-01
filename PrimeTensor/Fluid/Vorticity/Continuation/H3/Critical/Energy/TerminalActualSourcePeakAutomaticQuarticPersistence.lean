import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceDropQuarticPhysicalClock
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralAbsoluteHighSubcutoffEscape244
import Mathlib.Tactic

/-!
# Automatic local high-H³ dissipation persistence from an actual source peak

The preceding quartic physical momentum estimate had a remaining numerical
source-gap hypothesis. At a FIXED genuine physical time with a strictly positive
highpass source margin, that gap can be forced by an auxiliary Fourier radius R:
its left side grows as R², while the physical source ceiling and the two
endpoint viscous costs have an R-independent bound. The pre-existing
antitonicity theorem transfers a hypothetical dissipation drop at the original
cutoff σ to any selected R ≥ σ.

The result is a *positive, quantitative local persistence width* for high-H³
viscous dissipation at any strict-time peak, using only local bounds on the
actual momentum source and the actual H³ spectral state. It does NOT provide a
terminal-uniform width: the chosen radius depends on the source margin, the
starting full H³ dissipation, the local PDE source ceiling and spectral norm.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeSourcePeakPersistence
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSourcePeakPersistence :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- An explicit positive Fourier radius makes every fixed finite cost
strictly smaller than R² times a strictly positive source margin squared.
The lower cutoff σ is arbitrary; no asymptotic or choice axiom is needed. -/
theorem h3Critical_positiveSourceMargin_selectsDominantQuarticRadius
    (P K σ : ℝ) (hP : 0 < P) (hK : 0 ≤ K) :
    ∃ R : ℝ, 1 ≤ R ∧ σ ≤ R ∧ K < R ^ 2 * P ^ 2 := by
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
  exact ⟨R, hRone, hRSigma, hStrict⟩

/-- On a quartic physical clock, if high-radial dissipation drops below M
at the ORIGINAL cutoff σ, then the later endpoint cost at the higher
auxiliary radius R≥σ is already bounded by M. Only the first endpoint's
actual high-radial dissipation remains in this quantitative budget. -/
theorem h3Critical_quarticSourceDrop_initialTailDissipationBudget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 1 ≤ R)
    (hσR : σ ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C : ℝ)
    (hClock : R ^ 4 * (s - t) ≤ 1)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M) :
    R ^ 2 *
      (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M) ^ 2 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (12 * C ^ 2 +
          2 * (h3PathActualHighRadialDissipation244 R
            (h3AuditActualSpectralVelocityTotal hH3 t) + M)) := by
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have hAntitone := h3Path_actualHighRadialDissipation_antitone_radius244
    hH3 hClass s hsClass hσR
  have hLater : h3PathActualHighRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M :=
    hAntitone.trans hDrop
  have hOriginal := h3Critical_sourceDrop_quarticClock_endpointDissipationBudget
    hH3 hClass b hb ρ σ R hσ i t s ht hs hts M C hR
    hClock hCeil hPeak hDrop
  have hSum := add_le_add_right hLater
    (h3PathActualHighRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 t))
  have hDouble := mul_le_mul_of_nonneg_left hSum
    (by norm_num : 0 ≤ (2 : ℝ))
  have hInner := add_le_add_right hDouble (12 * C ^ 2)
  have hA : 0 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 := sq_nonneg _
  exact hOriginal.trans (mul_le_mul_of_nonneg_left hInner hA)

/-- A strict real highpass Fourier source peak forces a strictly positive
physical interval on which high-radial H³ dissipation cannot fall to M.

The source ceiling and H³ spectral-state norm ceiling are assumed only on ONE
fixed compact strict-time interval. They can be obtained locally from the
already-proved physical source and spectral-state continuity; no terminal-
uniform estimates, numerical gap, or high-band temporal derivative are assumed.

A constructive auxiliary cutoff R ≥ max(1,σ) and the duration
δ=min(δ₀, 1/R⁴)>0 are returned with the persistence statement. -/
theorem h3Critical_strictSourcePeak_automaticLocalHighDissipationPersistence
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
    ∃ R δ : ℝ, 1 ≤ R ∧ σ ≤ R ∧ 0 < δ ∧
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
  obtain ⟨R, hR, hσR, hGap⟩ :=
    h3Critical_positiveSourceMargin_selectsDominantQuarticRadius
      P (A ^ 2 * B) σ hP hK
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
  refine ⟨R, δ, hR, hσR, hδ, hδBase, hClockδ, ?_⟩
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

end
end PrimeTensor.Bridge.Euclidean

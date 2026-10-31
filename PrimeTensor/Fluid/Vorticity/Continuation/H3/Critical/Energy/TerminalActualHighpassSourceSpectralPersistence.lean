import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDrivenExtendedWidthBudget
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourcePhysicalDifference244
import Mathlib.Tactic

/-!
# A quantitative physical PDE route to source-driven persistence widths

The previous source-driven common windows used continuity of the actual Fourier
highpass source. This module transports the *already-proved* Lipschitz estimate
for the physical projected PDE source through the exact Fourier highpass.
A bounded actual weighted H³ spectral state and an explicit temporal spectral
increment bound control how quickly that source can fall below the kinetic-
anchored high-dissipation barrier. These data give an explicit, positive
persistence width, rather than merely an existential continuity neighborhood.

The required spectral time-increment bound and amplitude ceiling are EXPLICIT
additional local assumptions. The PDE has not yet supplied them uniformly on
cofinal terminal windows. Consequently this is a quantitative conditional
noncompression mechanism, not global Navier--Stokes regularity.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3SourceSpectralPersistence
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SourceSpectralPersistence :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The physical projected PDE source difference estimate also controls the
actual complex Fourier HIGH-PASS source difference, with no cutoff-dependent
loss. This is the exact Fourier/Plancherel bridge, not a formal frequency
projection of an unrelated PDE source. -/
theorem h3Critical_actualHighpassSource_temporalSub_norm_le_spectral
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (i : Fin 3) (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i s -
        h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 s‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 t‖)) *
        ‖h3AuditActualSpectralVelocityTotal hH3 s -
          h3AuditActualSpectralVelocityTotal hH3 t‖ := by
  let F : ℝ → H3FourierComplexL2 :=
    h3CriticalActualProjectedFourierSource hH3 i
  let R : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hHighSub :
      h3CriticalActualProjectedHighpassFourierSource hH3 ρ i s -
          h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t =
        (F s - F t) - h3CriticalFourierSharpLowCutoffCLM ρ (F s - F t) := by
    dsimp only [h3CriticalActualProjectedHighpassFourierSource, F]
    rw [map_sub]
    abel
  have hFourierSub : F s - F t =
      h3ScalarFourierL2 ((R s - R t).ofLp i) := by
    change h3ScalarFourierL2 ((R s).ofLp i) -
      h3ScalarFourierL2 ((R t).ofLp i) =
        h3ScalarFourierL2 ((R s - R t).ofLp i)
    rw [PiLp.sub_apply, h3ScalarFourierL2_sub]
  calc
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i s -
        h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ =
        ‖(F s - F t) - h3CriticalFourierSharpLowCutoffCLM ρ (F s - F t)‖ := by
          rw [hHighSub]
    _ ≤ ‖F s - F t‖ :=
      h3Critical_fourierSharpHighpass_norm_le ρ (F s - F t)
    _ = ‖(R s - R t).ofLp i‖ := by
      rw [hFourierSub, norm_h3ScalarFourierL2]
    _ ≤ ‖R s - R t‖ := PiLp.norm_apply_le (R s - R t) i
    _ ≤ (3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 s‖ +
            ‖h3AuditActualSpectralVelocityTotal hH3 t‖)) *
          ‖h3AuditActualSpectralVelocityTotal hH3 s -
            h3AuditActualSpectralVelocityTotal hH3 t‖ :=
      h3Path_actualProjectedSource_temporalSub_norm_le_spectral244
        hH3 s t hs ht

/-- Spectral H³ amplitude and temporal displacement control the *same*
physical Fourier-source and high-H³ dissipation channel at every point of
a prescribed window. The positive source margin must exceed the calculated
spectral-rate cost over its entire width. There is no dissipation-continuity
hypothesis and no terminal-uniform spectral time modulus is inferred. -/
theorem h3Critical_sourceDriven_spectralClock_persists_highDissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t δ E L M : ℝ)
    (ht : t ∈ Set.Ioo b T) (hδ : 0 ≤ δ) (hEnd : t + δ < T)
    (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hState : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E)
    (hMotion : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ‖h3AuditActualSpectralVelocityTotal hH3 s -
        h3AuditActualSpectralVelocityTotal hH3 t‖ ≤ L * (s - t))
    (hMargin :
      h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M +
        (3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) * L * δ <
          ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖) :
    ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      M < h3PathActualHighRadialDissipation244 σ
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
  let H : ℝ → H3FourierComplexL2 := fun r =>
    h3CriticalActualProjectedHighpassFourierSource hH3 ρ i r
  let B : ℝ := h3CriticalSourceDrivenHighDissipationBarrier
    (velocityH3Energy0At u b) σ M
  let Q : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)
  have hCL : 0 ≤ h3AuditInitialLerayEnergyCoefficient :=
    h3AuditInitialLerayEnergyCoefficient_nonneg
  have h2E : 0 ≤ 2 * E := mul_nonneg (by norm_num) hE
  have hProductCoeff :
      0 ≤ h3AuditInitialLerayEnergyCoefficient * (2 * E) :=
    mul_nonneg hCL h2E
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    linarith only [hProductCoeff]
  have hB : 0 ≤ B := le_max_right _ _
  intro s hs
  have hTInside : t ∈ Set.Icc t (t + δ) :=
    ⟨le_rfl, le_add_of_nonneg_right hδ⟩
  have hTime : s ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hs0 : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 hTime.1), hTime.2⟩
  have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 ht.1), ht.2⟩
  have hUs : ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E :=
    hState s hs
  have hUt : ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ≤ E :=
    hState t hTInside
  have hCoeff :
      3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 s‖ +
            ‖h3AuditActualSpectralVelocityTotal hH3 t‖) ≤ Q := by
    dsimp only [Q]
    have hSum := add_le_add hUs hUt
    have hMul := mul_le_mul_of_nonneg_left hSum hCL
    linarith only [hMul]
  have hDist : s - t ≤ δ := by linarith only [hs.2]
  have hIncrement :
      ‖H s - H t‖ ≤ Q * L * δ := by
    calc
      ‖H s - H t‖ ≤
          (3 + h3AuditInitialLerayEnergyCoefficient *
            (‖h3AuditActualSpectralVelocityTotal hH3 s‖ +
              ‖h3AuditActualSpectralVelocityTotal hH3 t‖)) *
            ‖h3AuditActualSpectralVelocityTotal hH3 s -
              h3AuditActualSpectralVelocityTotal hH3 t‖ :=
        h3Critical_actualHighpassSource_temporalSub_norm_le_spectral
          hH3 ρ i s t hs0 ht0
      _ ≤ Q * ‖h3AuditActualSpectralVelocityTotal hH3 s -
          h3AuditActualSpectralVelocityTotal hH3 t‖ :=
        mul_le_mul_of_nonneg_right hCoeff (norm_nonneg _)
      _ ≤ Q * (L * (s - t)) :=
        mul_le_mul_of_nonneg_left (hMotion s hs) hQ
      _ ≤ Q * L * δ := by
        have hLBound := mul_le_mul_of_nonneg_left hDist hL
        have hQB := mul_le_mul_of_nonneg_left hLBound hQ
        nlinarith only [hQB]
  have hReverse : ‖H t‖ ≤ ‖H s‖ + ‖H s - H t‖ := by
    calc
      ‖H t‖ = ‖H s - (H s - H t)‖ := by
        congr 1
        abel
      _ ≤ ‖H s‖ + ‖H s - H t‖ := norm_sub_le _ _
  have hHigh : B < ‖H s‖ := by
    dsimp only [H, B, Q] at hReverse hIncrement ⊢
    linarith only [hMargin, hReverse, hIncrement]
  have hNorm : 0 ≤ ‖H s‖ := norm_nonneg _
  have hPositive : 0 < ‖H s‖ := lt_of_le_of_lt hB hHigh
  have hSquare : B ^ 2 < ‖H s‖ ^ 2 := by
    have hProduct : 0 < (‖H s‖ - B) * (‖H s‖ + B) :=
      mul_pos (sub_pos.mpr hHigh) (add_pos_of_pos_of_nonneg hPositive hB)
    nlinarith only [hProduct]
  have hMass : ‖H s‖ ^ 2 =
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume :=
    h3Critical_fourierSharpHighpass_norm_sq_eq_integral ρ _
  have hAbove :
      (h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M) ^ 2 <
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume := by
    change B ^ 2 < _
    rw [← hMass]
    exact hSquare
  exact h3Critical_sourceMass_above_barrier_forces_highDissipation
    hH3 hClass b hb ρ σ hσ i s hTime M hAbove

/-- A positive source margin V-B and nonnegative spectral rate Q give an
explicit positive half-margin persistence width. -/
theorem h3Critical_positiveHalfMargin_width
    (V B Q Δ : ℝ) (hGap : B < V) (hQ : 0 ≤ Q) (hΔ : 0 < Δ) :
    let δ := min (Δ / 2) ((V - B) / (2 * (Q + 1)))
    0 < δ ∧ δ ≤ Δ ∧ B + Q * δ < V := by
  let δ : ℝ := min (Δ / 2) ((V - B) / (2 * (Q + 1)))
  have hQpos : 0 < Q + 1 := by linarith only [hQ]
  have hDen : 0 < 2 * (Q + 1) := by positivity
  have hDiff : 0 < V - B := sub_pos.mpr hGap
  have hRatio : 0 < (V - B) / (2 * (Q + 1)) := div_pos hDiff hDen
  have hδpos : 0 < δ :=
    lt_min (by linarith only [hΔ]) hRatio
  have hδle : δ ≤ Δ := by
    dsimp only [δ]
    have hmin := min_le_left (Δ / 2) ((V - B) / (2 * (Q + 1)))
    linarith only [hmin, hΔ]
  have hδratio : δ ≤ (V - B) / (2 * (Q + 1)) :=
    min_le_right _ _
  have hFrac : (Q + 1) * ((V - B) / (2 * (Q + 1))) =
      (V - B) / 2 := by
    field_simp [ne_of_gt hQpos]
  have hBound : Q * δ ≤ (V - B) / 2 := by
    calc
      Q * δ ≤ Q * ((V - B) / (2 * (Q + 1))) :=
        mul_le_mul_of_nonneg_left hδratio hQ
      _ ≤ (Q + 1) * ((V - B) / (2 * (Q + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith only [hQ]) hRatio.le
      _ = (V - B) / 2 := hFrac
  have hMargin : B + Q * δ < V := by
    linarith only [hBound, hDiff]
  exact ⟨hδpos, hδle, hMargin⟩

/-- An explicit, *nonzero* persistence width supplied by a local bounded H³
spectral amplitude and an H³ spectral-time increment bound. Unlike the
preceding purely topological common-window existence theorem, the selected
width is the exact minimum of a time slack and a source-margin/rate scale.
The spectral amplitude and time-increment estimates remain premises. -/
theorem h3Critical_sourceDriven_spectralClock_explicitPositiveWindow
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t Δ E L M : ℝ)
    (ht : t ∈ Set.Ioo b T) (hΔ : 0 < Δ) (hEnd : t + Δ < T)
    (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hState : ∀ s : ℝ, s ∈ Set.Icc t (t + Δ) →
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E)
    (hMotion : ∀ s : ℝ, s ∈ Set.Icc t (t + Δ) →
      ‖h3AuditActualSpectralVelocityTotal hH3 s -
        h3AuditActualSpectralVelocityTotal hH3 t‖ ≤ L * (s - t))
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖) :
    let Q := (3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) * L
    let δ := min (Δ / 2)
      ((‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) σ M) / (2 * (Q + 1)))
    0 < δ ∧ t + δ < T ∧
      ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        M < h3PathActualHighRadialDissipation244 σ
          (h3AuditActualSpectralVelocityTotal hH3 s) := by
  let B : ℝ := h3CriticalSourceDrivenHighDissipationBarrier
    (velocityH3Energy0At u b) σ M
  let Q : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) * L
  let V : ℝ := ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖
  let δ : ℝ := min (Δ / 2) ((V - B) / (2 * (Q + 1)))
  have hCL : 0 ≤ h3AuditInitialLerayEnergyCoefficient :=
    h3AuditInitialLerayEnergyCoefficient_nonneg
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    have h2E : 0 ≤ 2 * E := mul_nonneg (by norm_num) hE
    have hProductCoeff :
        0 ≤ h3AuditInitialLerayEnergyCoefficient * (2 * E) :=
      mul_nonneg hCL h2E
    have hCoeff : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient * (2 * E) := by
      linarith only [hProductCoeff]
    exact mul_nonneg hCoeff hL
  have hPeak' : B < V := hPeak
  obtain ⟨hδ, hδLe, hMargin⟩ :=
    h3Critical_positiveHalfMargin_width V B Q Δ hPeak' hQ hΔ
  have hEnd' : t + δ < T := by
    linarith only [hEnd, hδLe]
  have hSubset : Set.Icc t (t + δ) ⊆ Set.Icc t (t + Δ) := by
    intro s hs
    exact ⟨hs.1, le_trans hs.2 (add_le_add_right hδLe t)⟩
  have hLocalMargin :
      h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M +
        (3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) * L * δ <
          ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ := by
    change B + Q * δ < V
    exact hMargin
  have hPersistent :=
    h3Critical_sourceDriven_spectralClock_persists_highDissipation
      hH3 hClass b hb ρ σ hσ i t δ E L M ht hδ.le hEnd'
      hE hL (fun s hs => hState s (hSubset hs))
      (fun s hs => hMotion s (hSubset hs)) hLocalMargin
  exact ⟨hδ, hEnd', hPersistent⟩

end
end PrimeTensor.Bridge.Euclidean

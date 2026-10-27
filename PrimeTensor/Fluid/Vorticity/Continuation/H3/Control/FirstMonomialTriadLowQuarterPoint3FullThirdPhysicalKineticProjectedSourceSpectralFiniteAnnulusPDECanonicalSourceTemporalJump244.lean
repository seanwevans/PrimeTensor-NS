import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalCriticalWidthJointH3State244
import Mathlib.Tactic

/-!
# Canonical projected-source peaks: anchor versus temporal displacement

Canonical source maxima on the half-terminal window do not necessarily lie
inside the shorter disjoint quadratic-sharp dissipation window. This module
isolates the exact physical obstruction to transferring the source growth
back to the *anchor* of each window.

The elementary norm triangle inequality says that a large source at its
canonical maximizing time must be large already at the anchor, or undergo
a large temporal Hilbert-L² increment between these two physical times.
If those temporal increments admit one fixed eventual bound, then BOTH
H³ energy and weighted H³ spectral-state norms diverge at the original
anchors, which do belong to the disjoint persistence windows.

Such a uniform terminal modulus is not provided by continuity on individual
strict interior compact intervals. All critical-width and no-terminal-L²
trace assumptions remain explicitly conditional.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A physical source maximum is bounded by the source at the original
clock anchor plus its Hilbert-L² temporal increment. -/
theorem h3Path_sourcePeak_le_anchor_add_temporalJump244
    (peak anchor : H3PhysicalRealFinVectorL2Hilbert) :
    ‖peak‖ ≤ ‖anchor‖ + ‖peak - anchor‖ := by
  calc
    ‖peak‖ = ‖anchor + (peak - anchor)‖ := by
      congr 1
      abel
    _ ≤ ‖anchor‖ + ‖peak - anchor‖ := norm_add_le _ _

/-- Forced growth at physical maximizing times produces an unconditional
pointwise-in-index alternative: either the original anchor source is
already large, or the physical source makes a large temporal jump. -/
theorem h3Path_sourcePeakEscape_forces_anchorOrJump244
    (peak anchor : ℕ → H3PhysicalRealFinVectorL2Hilbert)
    (hPeak : Tendsto (fun k : ℕ => ‖peak k‖) atTop atTop) :
    ∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
      M ≤ ‖anchor k‖ ∨ M ≤ ‖peak k - anchor k‖ := by
  intro M
  have hLarge : ∀ᶠ k : ℕ in atTop, 2 * M ≤ ‖peak k‖ :=
    hPeak.eventually (eventually_ge_atTop (2 * M))
  filter_upwards [hLarge] with k hk
  have hTriangle := h3Path_sourcePeak_le_anchor_add_temporalJump244
    (peak k) (anchor k)
  by_cases ha : M ≤ ‖anchor k‖
  · exact Or.inl ha
  · right
    have hLess : ‖anchor k‖ < M := lt_of_not_ge ha
    linarith only [hk, hTriangle, hLess]

/-- A *fixed eventual bound* on the source displacement from anchor to
half-terminal maximizer forces the physical source at the anchor itself
to diverge. This is an explicit additional assumption. -/
theorem h3Path_boundedSourceTemporalJump_forces_anchorEscape244
    (peak anchor : ℕ → H3PhysicalRealFinVectorL2Hilbert)
    (hPeak : Tendsto (fun k : ℕ => ‖peak k‖) atTop atTop)
    (E : ℝ)
    (hJump : ∀ᶠ k : ℕ in atTop, ‖peak k - anchor k‖ ≤ E) :
    Tendsto (fun k : ℕ => ‖anchor k‖) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  have hLarge : ∀ᶠ k : ℕ in atTop, M + E ≤ ‖peak k‖ :=
    hPeak.eventually (eventually_ge_atTop (M + E))
  filter_upwards [hLarge, hJump] with k hk hj
  have ht := h3Path_sourcePeak_le_anchor_add_temporalJump244
    (peak k) (anchor k)
  linarith only [hk, hj, ht]

/-- If the original anchors stay bounded, the temporal excursion toward
canonical source maxima, rather than the anchor source, must diverge. -/
theorem h3Path_boundedAnchorSource_forces_temporalJumpEscape244
    (peak anchor : ℕ → H3PhysicalRealFinVectorL2Hilbert)
    (hPeak : Tendsto (fun k : ℕ => ‖peak k‖) atTop atTop)
    (E : ℝ)
    (hAnchor : ∀ᶠ k : ℕ in atTop, ‖anchor k‖ ≤ E) :
    Tendsto (fun k : ℕ => ‖peak k - anchor k‖) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  have hLarge : ∀ᶠ k : ℕ in atTop, M + E ≤ ‖peak k‖ :=
    hPeak.eventually (eventually_ge_atTop (M + E))
  filter_upwards [hLarge, hAnchor] with k hk ha
  have ht := h3Path_sourcePeak_le_anchor_add_temporalJump244
    (peak k) (anchor k)
  linarith only [hk, ha, ht]

/-- Escape of the actual projected Hilbert-L² source at *one fixed sequence*
of strict physical times forces both H³ energy and H³ spectral norm escape
at those SAME times, using the already proved physical source estimates. -/
theorem h3Path_sourceNormEscape_forces_jointH3SpectralAtSameTimes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℕ → ℝ)
    (ht : ∀ k, t k ∈ Set.Ioo (0 : ℝ) T)
    (hSource : Tendsto (fun k : ℕ =>
      ‖h3PathActualProjectedMomentumSource244 hH3 (t k)‖)
      atTop atTop) :
    Tendsto (fun k : ℕ => velocityH3EnergyAt u (t k)) atTop atTop ∧
      Tendsto (fun k : ℕ =>
        ‖h3AuditActualSpectralVelocityTotal hH3 (t k)‖)
        atTop atTop := by
  have hLarge (M : ℝ) : ∀ᶠ k : ℕ in atTop,
      M ≤ velocityH3EnergyAt u (t k) ∧
        M ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (t k)‖ := by
    let A : ℝ := max M 0
    let CL : ℝ := h3AuditInitialLerayEnergyCoefficient
    let H : ℝ := (3 + CL) * A + (3 * A + CL * A ^ 2) + 1
    have hA : 0 ≤ A := le_max_right M 0
    have hMA : M ≤ A := le_max_left M 0
    have hHigh : ∀ᶠ k : ℕ in atTop,
        H ≤ ‖h3PathActualProjectedMomentumSource244 hH3 (t k)‖ :=
      hSource.eventually (eventually_ge_atTop H)
    filter_upwards [hHigh] with k hk
    have hPoint :
        (3 + h3AuditInitialLerayEnergyCoefficient) * A +
            (3 * A + h3AuditInitialLerayEnergyCoefficient * A ^ 2) + 1 ≤
          ‖h3PathActualProjectedMomentumSource244 hH3 (t k)‖ := by
      change H ≤ ‖h3PathActualProjectedMomentumSource244 hH3 (t k)‖
      exact hk
    obtain ⟨hE, hS⟩ :=
      h3Path_projectedSourceThreshold_forces_jointH3Spectral244
        hH3 (t k) (ht k) A hA hPoint
    exact ⟨(hMA.trans hE.le), (hMA.trans hS.le)⟩
  constructor
  · apply Filter.tendsto_atTop.2
    intro M
    filter_upwards [hLarge M] with k hk
    exact hk.1
  · apply Filter.tendsto_atTop.2
    intro M
    filter_upwards [hLarge M] with k hk
    exact hk.2

/-- Canonical physical source-maximizing times, chosen BEFORE the regime
parameters, yield an exact anchor-versus-jump obstruction on the SAME
disjoint finite-dissipation windows.

Under an additional *bounded temporal source increment* assumption, both
physical H³ energy and actual weighted spectral norm escape at the ORIGINAL
window anchors. If instead their source norms are eventually bounded, the
Hilbert-L² source increments necessarily tend to infinity.

No terminal uniform modulus or H³ continuation is asserted. -/
theorem h3Path_noL2Trace_canonicalWidth_anchorOrTemporalJump244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ) (s : ℕ → ℝ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ k, s k ∈ Set.Icc (τ (v k))
          (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ = C (v k)) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        (∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
          M ≤ ‖h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖ ∨
          M ≤ ‖h3PathActualProjectedMomentumSource244 hH3 (s k) -
            h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖) ∧
        (∀ E : ℝ,
          (∀ᶠ k : ℕ in atTop,
            ‖h3PathActualProjectedMomentumSource244 hH3 (s k) -
              h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖ ≤ E) →
          Tendsto (fun k : ℕ =>
            ‖h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖)
            atTop atTop ∧
          Tendsto (fun k : ℕ => velocityH3EnergyAt u (τ (v k)))
            atTop atTop ∧
          Tendsto (fun k : ℕ =>
            ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)
            atTop atTop) ∧
        (∀ E : ℝ,
          (∀ᶠ k : ℕ in atTop,
            ‖h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖ ≤ E) →
          Tendsto (fun k : ℕ =>
            ‖h3PathActualProjectedMomentumSource244 hH3 (s k) -
              h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖)
            atTop atTop)) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hEscape⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalCriticalWidth_physicalSourcePeaks244
      hH3 hClass hMass hNoTrace hDInt
  classical
  have hChoice (k : ℕ) : ∃ s : ℝ,
      s ∈ Set.Icc (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k) :=
    (hCanonical k).2.2
  choose s hs hPeak using hChoice
  let peak : ℕ → H3PhysicalRealFinVectorL2Hilbert := fun k =>
    h3PathActualProjectedMomentumSource244 hH3 (s k)
  let anchor : ℕ → H3PhysicalRealFinVectorL2Hilbert := fun k =>
    h3PathActualProjectedMomentumSource244 hH3 (τ (v k))
  have hAnchorAbs (k : ℕ) : τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (hTime (v k)).1,
      (hTime (v k)).2⟩
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hCanonical k).1, (hCanonical k).2.1⟩
  · intro k
    exact ⟨hs k, hPeak k⟩
  · intro η B D hη hB hD hRegime
    have hSquare := (hEscape η B D hη hB hD hRegime).1
    have hAbs := h3Path_sourceCeilingSquareEscape_forces_absEscape244
      (fun k => C (v k)) hSquare
    have hCNonneg (k : ℕ) : 0 ≤ C (v k) := by
      rw [← hPeak k]
      exact norm_nonneg _
    have hEq : (fun k : ℕ => ‖peak k‖) =
        (fun k : ℕ => |C (v k)|) := by
      funext k
      change ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ =
        |C (v k)|
      rw [hPeak k]
      exact (abs_of_nonneg (hCNonneg k)).symm
    have hPeakEscape : Tendsto (fun k : ℕ => ‖peak k‖)
        atTop atTop := by
      rw [hEq]
      exact hAbs
    refine ⟨?_, ?_, ?_⟩
    · simpa only [peak, anchor] using
        (h3Path_sourcePeakEscape_forces_anchorOrJump244
          peak anchor hPeakEscape)
    · intro E hJump
      have hJump' : ∀ᶠ k : ℕ in atTop, ‖peak k - anchor k‖ ≤ E := by
        simpa only [peak, anchor] using hJump
      have hAnchorEscape : Tendsto (fun k : ℕ => ‖anchor k‖)
          atTop atTop :=
        h3Path_boundedSourceTemporalJump_forces_anchorEscape244
          peak anchor hPeakEscape E hJump'
      have hJoint := h3Path_sourceNormEscape_forces_jointH3SpectralAtSameTimes244
        hH3 (fun k => τ (v k)) hAnchorAbs
        (by simpa only [anchor] using hAnchorEscape)
      exact ⟨by simpa only [anchor] using hAnchorEscape,
        hJoint.1, hJoint.2⟩
    · intro E hAnchor
      have hAnchor' : ∀ᶠ k : ℕ in atTop, ‖anchor k‖ ≤ E := by
        simpa only [anchor] using hAnchor
      have hJumpEscape :=
        h3Path_boundedAnchorSource_forces_temporalJumpEscape244
          peak anchor hPeakEscape E hAnchor'
      simpa only [peak, anchor] using hJumpEscape

end
end PrimeTensor.FirstMonomialTriad

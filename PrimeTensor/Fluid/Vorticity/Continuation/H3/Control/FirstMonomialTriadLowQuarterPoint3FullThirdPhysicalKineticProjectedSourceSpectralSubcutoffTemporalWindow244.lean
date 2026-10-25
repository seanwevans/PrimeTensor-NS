import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFixedFrequencyDissipationEvacuation244
import Mathlib.Tactic

/-!
# Uniform growing-subcutoff evacuation and the temporal-window frontier

The committed four-channel witness has true physical H³ dissipation above
R_n = n+1 exceeding R_n times that below R_n. Monotonicity of the genuine
radial set integral upgrades fixed-frequency evacuation to ANY sequence of
cutoffs rho_n <= n+1 eventually, with a quantitative O(1/n) low share.
All profiles share the very SAME terminal witness.

A second theorem isolates the exact positive-time regularity obligation for
time-window persistence. If the genuine low-radial dissipation and the full
physical H³ dissipation are continuous at those selected times, the strict
low-share inequality persists on some open time window about each time.
No lower bound on the window widths is asserted; in particular no terminal
time-integral lower bound or global regularity claim follows.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3SubcutoffWindow244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SubcutoffWindow244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Any (even varying) radial cutoff below n+1 inherits the quantitative
low-dissipation-share estimate of the actual moving-cutoff witness. -/
theorem h3Path_subcutoff_dissipationShare_bound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (n : ℕ) (ρ : ℝ) (hρ : ρ ≤ (n : ℝ) + 1)
    (hDom : ((n : ℝ) + 1) *
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    0 ≤ h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) /
          velocityH3DissipationAt u t ∧
    h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) /
          velocityH3DissipationAt u t < 1 / ((n : ℝ) + 2) := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let L : ℝ := h3PathActualLowRadialDissipation244 ((n : ℝ) + 1) G
  let H : ℝ := h3PathActualHighRadialDissipation244 ((n : ℝ) + 1) G
  let F : ℝ := h3PathActualLowRadialDissipation244 ρ G
  let D : ℝ := velocityH3DissipationAt u t
  have hL : 0 ≤ L := by
    dsimp only [L, h3PathActualLowRadialDissipation244]
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ
  have hF : 0 ≤ F := by
    dsimp only [F, h3PathActualLowRadialDissipation244]
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ
  have hPartition : L + H = D := by
    dsimp only [L, H, D, G]
    exact h3Path_actualRadialDissipation_partition244
      hH3 hClass t ht ((n : ℝ) + 1)
  have hShare := h3Path_highDissipationDominance_lowShare_bound244
    ((n : ℝ) + 1) L H (by positivity) hL (by
      simpa only [L, H, G] using hDom)
  have hDPos : 0 < D := by
    rw [← hPartition]
    exact hShare.1
  have hMono : F ≤ L := by
    dsimp only [F, L, G]
    exact h3Path_actualLowRadialDissipation_mono_radius244
      hH3 hClass t ht hρ
  have hRatioLe : F / D ≤ L / D :=
    (div_le_div_iff₀ hDPos hDPos).2
      (mul_le_mul_of_nonneg_right hMono hDPos.le)
  have hUpper : L / D < 1 / ((n : ℝ) + 2) := by
    rw [← hPartition]
    simpa only [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
      using hShare.2.2
  exact ⟨by simpa only [F, D, G] using (div_nonneg hF hDPos.le),
    by simpa only [F, D, G] using (lt_of_le_of_lt hRatioLe hUpper)⟩

/-- A single selected physical terminal sequence evacuates dissipation from
EVERY sequence of cutoffs dominated eventually by n+1. This quantifier is
stronger than evacuation separately at each fixed finite radius. -/
theorem h3Path_movingDominance_forces_allSubcutoffProfiles_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hDom : ∀ n : ℕ,
      ((n : ℝ) + 1) *
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) <
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n))) :
    ∀ ρ : ℕ → ℝ,
      (∀ᶠ n : ℕ in atTop, ρ n ≤ (n : ℝ) + 1) →
      Tendsto (fun n : ℕ =>
        h3PathActualLowRadialDissipation244 (ρ n)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) /
        velocityH3DissipationAt u (τ n)) atTop (𝓝 0) := by
  intro ρ hCutoff
  let F : ℕ → ℝ := fun n =>
    h3PathActualLowRadialDissipation244 (ρ n)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n)) /
      velocityH3DissipationAt u (τ n)
  have hBound : ∀ᶠ n : ℕ in atTop,
      ‖F n‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    filter_upwards [hCutoff] with n hn
    have hShare := h3Path_subcutoff_dissipationShare_bound244
      hH3 hClass (τ n) (hτ n) n (ρ n) hn (hDom n)
    have hR : 0 < (n : ℝ) + 1 := by positivity
    have hRLe : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
    have hInv : (1 : ℝ) / ((n : ℝ) + 2) ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hR hRLe
    change ‖h3PathActualLowRadialDissipation244 (ρ n)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n)) /
        velocityH3DissipationAt u (τ n)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg hShare.1]
    exact (le_of_lt hShare.2).trans hInv
  have hInv : Tendsto (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto F atTop (𝓝 0)
  exact (tendsto_iff_norm_sub_tendsto_zero).2
    (by simpa only [sub_zero] using
      (squeeze_zero'
        (Filter.Eventually.of_forall (fun n => norm_nonneg (F n)))
        hBound hInv))

/-- Positive-time continuity of BOTH actual scalar dissipation components
implies continuity of the normalized low-frequency share, provided total
physical H³ dissipation is strictly positive at the anchor time. -/
theorem h3Path_lowDissipationShare_continuousAt_of_parts244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ t : ℝ)
    (hLow : ContinuousAt (fun s =>
      h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 s)) t)
    (hTotal : ContinuousAt (velocityH3DissipationAt u) t)
    (hD : 0 < velocityH3DissipationAt u t) :
    ContinuousAt (fun s =>
      h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 s) /
      velocityH3DissipationAt u s) t := by
  exact hLow.div hTotal (ne_of_gt hD)

/-- A strict scalar inequality at a continuous time point persists on an
open time interval. Width is positive but is NOT controlled uniformly. -/
theorem h3Path_continuousStrictInequality_localWindow244
    {f : ℝ → ℝ} {t q : ℝ}
    (hf : ContinuousAt f t) (hSmall : f t < q) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, dist s t < δ → f s < q := by
  have hEvent : {s : ℝ | f s < q} ∈ 𝓝 t :=
    hf (isOpen_Iio.mem_nhds hSmall)
  obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.mp hEvent
  exact ⟨δ, hδ, fun s hs =>
    hBall (by simpa only [Metric.mem_ball] using hs)⟩

/-- Conditional positive-width persistence on EVERY selected snapshot.
The missing hypothesis is time-continuity of the genuine physical H³
spectral LOW dissipation and TOTAL dissipation. This theorem does NOT
supply a uniform lower bound on the positive window widths. -/
theorem h3Path_movingDominance_forces_localDissipationWindows244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hDom : ∀ n : ℕ,
      ((n : ℝ) + 1) *
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) <
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)))
    (hLowCont : ∀ n : ℕ, ContinuousAt (fun s =>
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s)) (τ n))
    (hDCont : ∀ n : ℕ,
      ContinuousAt (velocityH3DissipationAt u) (τ n)) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧
      ∀ n : ℕ, ∀ s : ℝ, dist s (τ n) < δ n →
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) /
        velocityH3DissipationAt u s < 1 / ((n : ℝ) + 2) := by
  have hWindow (n : ℕ) :
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, dist s (τ n) < δ →
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) /
        velocityH3DissipationAt u s < 1 / ((n : ℝ) + 2) := by
    have hPoint := h3Path_subcutoff_dissipationShare_bound244
      hH3 hClass (τ n) (hτ n) n ((n : ℝ) + 1)
      (le_refl _) (hDom n)
    have hDPos : 0 < velocityH3DissipationAt u (τ n) := by
      let G : H3SpectralVelocityState :=
        h3AuditActualSpectralVelocityTotal hH3 (τ n)
      let L : ℝ := h3PathActualLowRadialDissipation244 ((n : ℝ) + 1) G
      let H : ℝ := h3PathActualHighRadialDissipation244 ((n : ℝ) + 1) G
      have hLNonneg : 0 ≤ L := by
        dsimp only [L, h3PathActualLowRadialDissipation244]
        apply integral_nonneg
        intro ξ
        exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ
      have hShare := h3Path_highDissipationDominance_lowShare_bound244
        ((n : ℝ) + 1) L H (by positivity) hLNonneg
        (by simpa only [L, H, G] using hDom n)
      have hPartition : L + H = velocityH3DissipationAt u (τ n) := by
        dsimp only [L, H, G]
        exact h3Path_actualRadialDissipation_partition244
          hH3 hClass (τ n) (hτ n) ((n : ℝ) + 1)
      rw [← hPartition]
      exact hShare.1
    have hCont := h3Path_lowDissipationShare_continuousAt_of_parts244
      hH3 ((n : ℝ) + 1) (τ n) (hLowCont n) (hDCont n) hDPos
    exact h3Path_continuousStrictInequality_localWindow244
      hCont hPoint.2
  choose δ hδ using hWindow
  exact ⟨δ, (fun n => (hδ n).1), (fun n s hs => (hδ n).2 s hs)⟩

/-- Under the original no-kinetic-trace obstruction, the SAME four-channel
physical sequence evacuates all subcutoff profiles. The conditional
local-time theorem above identifies the unresolved regularity hypothesis. -/
theorem h3Path_physicalNoL2Trace_forces_subcutoffProfileEvacuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ ρ : ℕ → ℝ,
        (∀ᶠ n : ℕ in atTop, ρ n ≤ (n : ℝ) + 1) →
        Tendsto (fun n : ℕ =>
          h3PathActualLowRadialDissipation244 (ρ n)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) /
          velocityH3DissipationAt u (τ n)) atTop (𝓝 0)) := by
  obtain ⟨τ, hτ, hNear, hLimit, hDom, _⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialDissipationLocalization244
      hH3 hClass hL hNoTrace
  exact ⟨τ, hτ, hNear, hLimit,
    fun ρ hρ =>
      h3Path_movingDominance_forces_allSubcutoffProfiles_zero244
        hH3 hClass τ hτ hDom ρ hρ⟩

end
end PrimeTensor.FirstMonomialTriad

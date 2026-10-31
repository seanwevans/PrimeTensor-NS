import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDissipationDisjointWindows
import Mathlib.Tactic

/-!
# Arbitrary-profile common windows for actual source and H³ dissipation

The moving diagonal already handles arbitrary independently prescribed source
and dissipation frequency radii and heights. The intermediate common-window
and disjoint-window statements chose the special radii n+1 and heights n.

This module transports the full arbitrary-profile quantifier strength through
positive-width physical time persistence and strictly separated subsequence
extraction. Both source and dissipation lower bounds hold at the SAME points
of the SAME windows, and both finite sums dominate the corresponding
prescribed height-times-width sums.

The only extra assumption is the explicit continuity of full physical H³
dissipation on the open physical time interval, as in the preceding common
window theorem. No lower bound on selected widths or noncompression statement
is obtained. The missing-terminal-L²-trace hypothesis remains conditional.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3ActualHighpassProfiles
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ActualHighpassProfiles :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every previously prescribed pair of moving radii and threshold profiles
persists on a common positive-width physical time window. One projected
source coordinate serves every index of the prescribed profiles. -/
theorem h3Critical_noL2Trace_actualHighpassSourceDissipation_profileWindows
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ K M : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hDCont : ContinuousOn (velocityH3DissipationAt u) (Set.Ioo a T)) :
    ∃ i : Fin 3, ∃ t δ : ℕ → ℝ,
      Tendsto t atTop (𝓝 T) ∧
      ∀ n : ℕ,
        t n ∈ Set.Ioo (c n) T ∧
        0 < δ n ∧ t n + δ n < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (t n) (t n + δ n) →
          K n < ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
            ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume ∧
          M n < h3PathActualHighRadialDissipation244 (σ n)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        δ n * K n ≤ ∫ s in t n..(t n + δ n),
          (∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
            ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume) ∧
        δ n * M n ≤ ∫ s in t n..(t n + δ n),
          h3PathActualHighRadialDissipation244 (σ n)
            (h3AuditActualSpectralVelocityTotal hH3 s) := by
  obtain ⟨i, t, htLimit, hSpike⟩ :=
    h3Critical_noL2Trace_actualHighpassSourceDissipation_movingDiagonal
      hH3 hClass b hb hNoTrace c ρ σ K M hc hcLimit hρ hσ
  have hSub : Set.Ioo a T ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have hWindow (n : ℕ) : ∃ δ : ℝ, 0 < δ ∧ t n + δ < T ∧
      (∀ s : ℝ, s ∈ Set.Icc (t n) (t n + δ) →
        K n < ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume ∧
        M n < h3PathActualHighRadialDissipation244 (σ n)
          (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      δ * K n ≤ ∫ s in t n..(t n + δ),
        (∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume) ∧
      δ * M n ≤ ∫ s in t n..(t n + δ),
        h3PathActualHighRadialDissipation244 (σ n)
          (h3AuditActualSpectralVelocityTotal hH3 s) := by
    let F : ℝ → ℝ := fun s =>
      ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume
    let G : ℝ → ℝ := fun s =>
      h3PathActualHighRadialDissipation244 (σ n)
        (h3AuditActualSpectralVelocityTotal hH3 s)
    have hFCont : ContinuousOn F (Set.Ioo a T) :=
      (h3Critical_actualHighpassSourceMass_continuousOn
        hH3 (ρ n) i).mono hSub
    have hGCont : ContinuousOn G (Set.Ioo a T) :=
      h3Path_actualHighRadialDissipation_continuousOn_of_parts244
        hH3 hClass (σ n) hDCont
        (h3Path_actualLowRadialDissipation_continuousOn_positiveTime244
          hH3 hClass (σ n) (hσ n))
    have ht : t n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans (hc n).1 ((hSpike n).1).1),
        ((hSpike n).1).2⟩
    simpa only [F, G] using
      (h3Critical_twoContinuousSpikes_integratedWindow F G
        ht hFCont hGCont (hSpike n).2.1 (hSpike n).2.2)
  choose δ hδ using hWindow
  refine ⟨i, t, δ, htLimit, ?_⟩
  intro n
  exact ⟨(hSpike n).1, (hδ n).1, (hδ n).2.1,
    (hδ n).2.2.1, (hδ n).2.2.2.1, (hδ n).2.2.2.2⟩

/-- The full arbitrary-profile joint witness survives disjoint extraction.
Both moving spectral source and dissipation costs are summed over identical,
strictly separated physical-time intervals. Heights may be any real sequences,
not merely n or polynomial profiles. -/
theorem h3Critical_noL2Trace_actualHighpassSourceDissipation_profileDisjointWindows
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ K M : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hDCont : ContinuousOn (velocityH3DissipationAt u) (Set.Ioo a T)) :
    ∃ i : Fin 3, ∃ t δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < δ (v k) ∧ t (v k) + δ (v k) < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) →
          K (v k) < ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ (v k)))ᶜ,
            ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume ∧
          M (v k) < h3PathActualHighRadialDissipation244 (σ (v k))
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        δ (v k) * K (v k) ≤ ∫ s in t (v k)..(t (v k) + δ (v k)),
          (∫ ξ in (h3TerminalRadialFrequencyBelow (ρ (v k)))ᶜ,
            ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume) ∧
        δ (v k) * M (v k) ≤ ∫ s in t (v k)..(t (v k) + δ (v k)),
          h3PathActualHighRadialDissipation244 (σ (v k))
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m, δ (v k) * K (v k)) ≤
          ∑ k ∈ Finset.range m,
            ∫ s in t (v k)..(t (v k) + δ (v k)),
              (∫ ξ in (h3TerminalRadialFrequencyBelow (ρ (v k)))ᶜ,
                ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume) ∧
        (∑ k ∈ Finset.range m, δ (v k) * M (v k)) ≤
          ∑ k ∈ Finset.range m,
            ∫ s in t (v k)..(t (v k) + δ (v k)),
              h3PathActualHighRadialDissipation244 (σ (v k))
                (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  obtain ⟨i, t, δ, htLimit, hWindow⟩ :=
    h3Critical_noL2Trace_actualHighpassSourceDissipation_profileWindows
      hH3 hClass b hb hNoTrace c ρ σ K M hc hcLimit hρ hσ hDCont
  have hWidth (n : ℕ) : 0 < δ n := (hWindow n).2.1
  have hEnd (n : ℕ) : t n + δ n < T := (hWindow n).2.2.1
  obtain ⟨v, hMono, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      t δ T htLimit hWidth hEnd
  refine ⟨i, t, δ, v, hMono, hCofinal, hSeparated, ?_, ?_⟩
  · intro k
    exact hWindow (v k)
  · intro m
    constructor
    · exact Finset.sum_le_sum (fun k _ => (hWindow (v k)).2.2.2.2.1)
    · exact Finset.sum_le_sum (fun k _ => (hWindow (v k)).2.2.2.2.2)

end
end PrimeTensor.Bridge.Euclidean

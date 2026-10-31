import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDissipationMovingDiagonal
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralCubicDissipationIntegratedWindows244
import Mathlib.Tactic

/-!
# Common physical-time windows for actual highpass source and H³ dissipation

The moving-cutoff diagonal provides one coordinate and common terminal times
with both actual highpass projected-source square mass and high-radial H³
dissipation exceeding n. The physical projected source is already continuous
at positive times; its Fourier highpass L² square mass is consequently
continuous without an additional hypothesis.

With the explicitly stated continuity of full physical H³ dissipation, the
previously proved continuity of low-radial dissipation and exact partition
make the high-radial channel continuous as well. Each simultaneous spike then
persists on ONE common positive right-hand window. Both channel integrals
exceed the width times the prescribed pointwise threshold.

No width lower bound, terminal noncompression estimate, nonlinear transport
control, or proof that the no-trace branch actually occurs is supplied.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3ActualHighpassWindows
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ActualHighpassWindows :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The actual Fourier highpass source square mass is continuous on the
positive-time physical interval, with no continuity hypothesis on H³
dissipation. This uses the genuine physical projected source and the exact
real Plancherel highpass norm identity. -/
theorem h3Critical_actualHighpassSourceMass_continuousOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (i : Fin 3) :
    ContinuousOn (fun t : ℝ =>
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume)
      (Set.Ioo (0 : ℝ) T) := by
  let R : ℝ → H3ScalarL2 := fun t =>
    (h3PathActualProjectedMomentumSource244 hH3 t).ofLp i -
      h3CriticalPhysicalSharpLowCutoffApply ρ
        ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i)
  have hSource : ContinuousOn
      (h3PathActualProjectedMomentumSource244 hH3)
      (Set.Ioo (0 : ℝ) T) := by
    change ContinuousOn
      (fun t : ℝ => h3AuditInitialActualSpectralLaplacianTotal hH3 t -
        h3AuditInitialActualSpectralLerayTotal hH3 t)
      (Set.Ioo (0 : ℝ) T)
    exact h3Audit_initialActualProjectedRHS_continuousOn_positiveTime hH3
  have hEval : Continuous
      (fun V : H3PhysicalRealFinVectorL2Hilbert => V.ofLp i) :=
    PiLp.continuous_apply
      (2 : ENNReal) (fun _ : Fin 3 => H3ScalarL2) i
  have hComponent : ContinuousOn
      (fun t : ℝ => (h3PathActualProjectedMomentumSource244 hH3 t).ofLp i)
      (Set.Ioo (0 : ℝ) T) :=
    hEval.comp_continuousOn hSource
  have hR : ContinuousOn R (Set.Ioo (0 : ℝ) T) :=
    hComponent.sub
      ((h3Critical_physicalSharpLowCutoff_continuous ρ).comp_continuousOn
        hComponent)
  have hSquare : ContinuousOn (fun t : ℝ => ‖R t‖ ^ 2)
      (Set.Ioo (0 : ℝ) T) := hR.norm.pow 2
  apply hSquare.congr
  intro t _ht
  change (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume) =
    ‖R t‖ ^ 2
  calc
    (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume) =
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ ^ 2 :=
      (h3Critical_fourierSharpHighpass_norm_sq_eq_integral ρ _).symm
    _ = ‖R t‖ ^ 2 := by
      rw [h3Critical_actualProjectedHighpassFourier_norm_eq_physical]

/-- Two continuous scalar spikes at the same strict physical time persist
on one common right-hand interval, and both interval integrals have the
corresponding height-times-width costs. No uniform width is claimed. -/
theorem h3Critical_twoContinuousSpikes_integratedWindow
    {a T t K M : ℝ} (F G : ℝ → ℝ)
    (ht : t ∈ Set.Ioo a T)
    (hF : ContinuousOn F (Set.Ioo a T))
    (hG : ContinuousOn G (Set.Ioo a T))
    (hFK : K < F t) (hGM : M < G t) :
    ∃ δ : ℝ, 0 < δ ∧ t + δ < T ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) → K < F s ∧ M < G s) ∧
      δ * K ≤ ∫ s in t..(t + δ), F s ∧
      δ * M ≤ ∫ s in t..(t + δ), G s := by
  have hFAt : ContinuousAt F t :=
    hF.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hGAt : ContinuousAt G t :=
    hG.continuousAt (isOpen_Ioo.mem_nhds ht)
  obtain ⟨ηF, hηF, hNearF⟩ :=
    h3Path_continuousStrictInequality_localWindow244
      (f := fun s => K - F s) (t := t) (q := 0)
      (continuousAt_const.sub hFAt) (by linarith only [hFK])
  obtain ⟨ηG, hηG, hNearG⟩ :=
    h3Path_continuousStrictInequality_localWindow244
      (f := fun s => M - G s) (t := t) (q := 0)
      (continuousAt_const.sub hGAt) (by linarith only [hGM])
  let δ : ℝ := min (ηF / 2) (min (ηG / 2) ((T - t) / 2))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by linarith only [hηF])
      (lt_min (by linarith only [hηG]) (by linarith only [ht.2]))
  have hδF : δ ≤ ηF / 2 := min_le_left _ _
  have hδG : δ ≤ ηG / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδT : δ ≤ (T - t) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hEnd : t + δ < T := by linarith only [hδT, ht.2]
  have hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      K < F s ∧ M < G s := by
    intro s hs
    have hDistF : dist s t < ηF := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      linarith only [hs.2, hδF, hηF]
    have hDistG : dist s t < ηG := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      linarith only [hs.2, hδG, hηG]
    constructor
    · have hNear := hNearF s hDistF
      linarith only [hNear]
    · have hNear := hNearG s hDistG
      linarith only [hNear]
  have hSub : Set.Icc t (t + δ) ⊆ Set.Ioo a T := by
    intro s hs
    exact ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hIntF : IntervalIntegrable F volume t (t + δ) :=
    (hF.mono hSub).intervalIntegrable_of_Icc (by linarith only [hδ])
  have hIntG : IntervalIntegrable G volume t (t + δ) :=
    (hG.mono hSub).intervalIntegrable_of_Icc (by linarith only [hδ])
  have hCostF : ((t + δ) - t) * K ≤ ∫ s in t..(t + δ), F s :=
    h3Path_localPositiveHeight_forces_integratedCost244
      F t (t + δ) K (by linarith only [hδ]) hIntF
      (fun s hs => (hFloor s hs).1.le)
  have hCostG : ((t + δ) - t) * M ≤ ∫ s in t..(t + δ), G s :=
    h3Path_localPositiveHeight_forces_integratedCost244
      G t (t + δ) M (by linarith only [hδ]) hIntG
      (fun s hs => (hFloor s hs).2.le)
  refine ⟨δ, hδ, hEnd, hFloor, ?_, ?_⟩
  · calc
      δ * K = ((t + δ) - t) * K := by ring
      _ ≤ ∫ s in t..(t + δ), F s := hCostF
  · calc
      δ * M = ((t + δ) - t) * M := by ring
      _ ≤ ∫ s in t..(t + δ), G s := hCostG

/-- On the SAME moving-frequency terminal diagonal, both the actual highpass
source mass and high-radial physical H³ dissipation persist on each common
positive physical-time window. Their integrated costs are at least n times
the window width; no lower bound on that width is assumed. -/
theorem h3Critical_noL2Trace_actualHighpassSourceDissipation_integratedWindows
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hDCont : ContinuousOn (velocityH3DissipationAt u) (Set.Ioo a T)) :
    ∃ i : Fin 3, ∃ t δ : ℕ → ℝ,
      Tendsto t atTop (𝓝 T) ∧
      ∀ n : ℕ,
        t n ∈ Set.Ioo (c n) T ∧
        0 < δ n ∧ t n + δ n < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (t n) (t n + δ n) →
          (n : ℝ) < ∫ ξ in
              (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
              ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume ∧
          (n : ℝ) < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        δ n * (n : ℝ) ≤ ∫ s in t n..(t n + δ n),
          (∫ ξ in (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
            ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume) ∧
        δ n * (n : ℝ) ≤ ∫ s in t n..(t n + δ n),
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) := by
  obtain ⟨i, t, htLimit, hSpike⟩ :=
    h3Critical_noL2Trace_actualHighpassSourceDissipation_natDiagonal
      hH3 hClass b hb hNoTrace c hc hcLimit
  have hSub : Set.Ioo a T ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have hWindow (n : ℕ) : ∃ δ : ℝ, 0 < δ ∧ t n + δ < T ∧
      (∀ s : ℝ, s ∈ Set.Icc (t n) (t n + δ) →
        (n : ℝ) < ∫ ξ in
            (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
            ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume ∧
        (n : ℝ) < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      δ * (n : ℝ) ≤ ∫ s in t n..(t n + δ),
        (∫ ξ in (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume) ∧
      δ * (n : ℝ) ≤ ∫ s in t n..(t n + δ),
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) := by
    let F : ℝ → ℝ := fun s =>
      ∫ ξ in (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume
    let G : ℝ → ℝ := fun s =>
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s)
    have hFCont : ContinuousOn F (Set.Ioo a T) :=
      (h3Critical_actualHighpassSourceMass_continuousOn
        hH3 ((n : ℝ) + 1) i).mono hSub
    have hGCont : ContinuousOn G (Set.Ioo a T) :=
      h3Path_actualHighRadialDissipation_continuousOn_of_parts244
        hH3 hClass ((n : ℝ) + 1) hDCont
        (h3Path_actualLowRadialDissipation_continuousOn_positiveTime244
          hH3 hClass ((n : ℝ) + 1) (by positivity))
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

end
end PrimeTensor.Bridge.Euclidean

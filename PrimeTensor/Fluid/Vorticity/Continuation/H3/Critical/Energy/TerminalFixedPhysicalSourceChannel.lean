import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalCofinalSourceDissipationSplit
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# A fixed nonintegrable physical source channel at terminal time

The preceding cofinal obstruction shows that, under failure of the physical
L² terminal trace, on each positive terminal interval at least one physical
source (Fourier-reconstructed Laplacian or Leray transport) is not Bochner L¹.

The choice can be made ONCE for every terminal interval: if both sources were
L¹ on some (possibly different) tails, restricting both to a common later
tail would make their difference L¹, contradicting the previous obstruction.
Positive-time continuity turns the chosen channel's persistent non-L¹ into
cofinal norm spikes for that SAME channel.

No positive terminal kinetic mass, finite dissipation, or global regularity
claim is used or established.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped Topology Interval

noncomputable section
set_option maxHeartbeats 800000

/-- Bochner interval integrability persists under restriction to a later
terminal subinterval. No temporal continuity assumption is required. -/
theorem h3Critical_physicalSource_integrable_mono_terminal_tail
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    {b c T : ℝ}
    (hb : b < T) (hc : c < T) (hbc : b ≤ c)
    (hF : IntervalIntegrable F volume b T) :
    IntervalIntegrable F volume c T := by
  apply hF.mono_set
  intro s hs
  have hsNew : s ∈ Set.Icc c T := by
    simpa only [Set.uIcc_of_le hc.le] using hs
  have hsOld : s ∈ Set.Icc b T := ⟨hbc.trans hsNew.1, hsNew.2⟩
  simpa only [Set.uIcc_of_le hb.le] using hsOld

/-- The Laplacian/Leray nonintegrability alternative has a fixed choice
of physical Hilbert source, independent of the terminal starting time. -/
theorem h3Critical_noL2Trace_fixed_physicalSource_nonintegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      ¬ IntervalIntegrable
        (h3AuditInitialActualSpectralLaplacianTotal hH3) volume b T) ∨
    (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      ¬ IntervalIntegrable
        (h3AuditInitialActualSpectralLerayTotal hH3) volume b T) := by
  classical
  by_contra hNeither
  have hDExists : ∃ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T ∧
      IntervalIntegrable
        (h3AuditInitialActualSpectralLaplacianTotal hH3) volume b T := by
    by_contra hAbsent
    apply hNeither
    left
    intro b hb hD
    exact hAbsent ⟨b, hb, hD⟩
  have hNExists : ∃ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T ∧
      IntervalIntegrable
        (h3AuditInitialActualSpectralLerayTotal hH3) volume b T := by
    by_contra hAbsent
    apply hNeither
    right
    intro b hb hN
    exact hAbsent ⟨b, hb, hN⟩
  obtain ⟨bD, hbD, hD⟩ := hDExists
  obtain ⟨bN, hbN, hN⟩ := hNExists
  let b : ℝ := max bD bN
  have hb : b ∈ Set.Ioo (0 : ℝ) T := by
    dsimp only [b]
    exact ⟨lt_of_lt_of_le hbD.1 (le_max_left bD bN),
      max_lt hbD.2 hbN.2⟩
  have hDTail : IntervalIntegrable
      (h3AuditInitialActualSpectralLaplacianTotal hH3) volume b T :=
    h3Critical_physicalSource_integrable_mono_terminal_tail
      _ hbD.2 hb.2 (le_max_left bD bN) hD
  have hNTail : IntervalIntegrable
      (h3AuditInitialActualSpectralLerayTotal hH3) volume b T :=
    h3Critical_physicalSource_integrable_mono_terminal_tail
      _ hbN.2 hb.2 (le_max_right bD bN) hN
  rcases
      h3Critical_noL2Trace_laplacian_or_leray_nonintegrable_on_every_tail
        hH3 hNoTrace b hb with hDBad | hNBad
  · exact hDBad hDTail
  · exact hNBad hNTail

/-- Positive-time continuity of each of the two actual Fourier-reconstructed
physical sources, separately, not just continuity of their difference. -/
theorem h3Critical_physicalSource_terms_continuousOn_positiveTime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    ContinuousOn (h3AuditInitialActualSpectralLaplacianTotal hH3)
      (Set.Ioo (0 : ℝ) T) ∧
    ContinuousOn (h3AuditInitialActualSpectralLerayTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
  have hU : ContinuousOn
      (h3AuditActualSpectralVelocityTotal hH3)
      (Set.Ioo (0 : ℝ) T) :=
    h3Audit_initialActualSpectralVelocity_continuousOn hH3
  constructor
  · have hComp :=
      continuous_h3AuditSpectralPhysicalLaplacian.comp_continuousOn hU
    apply hComp.congr
    intro s hs
    simp only [h3AuditInitialActualSpectralLaplacianTotal,
      dite_eq_left hs, Function.comp_apply]
  · have hComp :=
      continuous_h3AuditSpectralPhysicalLerayForcing.comp_continuousOn hU
    apply hComp.congr
    intro s hs
    simp only [h3AuditInitialActualSpectralLerayTotal,
      dite_eq_left hs, Function.comp_apply]

/-- A continuously varying, uniformly bounded physical Hilbert source is
Bochner L¹ on a finite positive terminal interval. -/
theorem h3Critical_continuous_physicalSource_integrable_of_terminal_ceiling
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    {T : ℝ}
    (hCont : ContinuousOn F (Set.Ioo (0 : ℝ) T))
    (b : ℝ) (hb : b ∈ Set.Ioo (0 : ℝ) T)
    (M : ℝ)
    (hBound : ∀ t : ℝ, t ∈ Set.Ioo b T → ‖F t‖ ≤ M) :
    IntervalIntegrable F volume b T := by
  have hConst : IntervalIntegrable (fun _ : ℝ => M) volume b T :=
    continuousOn_const.intervalIntegrable_of_Icc hb.2.le
  have hMajor : IntegrableOn (fun _ : ℝ => M) (Set.Ioo b T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).1 hConst
  have hSub : Set.Ioo b T ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hMeas : AEStronglyMeasurable F
      ((volume : Measure ℝ).restrict (Set.Ioo b T)) :=
    (hCont.mono hSub).aestronglyMeasurable measurableSet_Ioo
  have hDom : ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioo b T)),
      ‖F t‖ ≤ M :=
    ae_restrict_of_forall_mem measurableSet_Ioo (by
      intro t ht
      exact hBound t ht)
  have hF : IntegrableOn F (Set.Ioo b T) volume :=
    Integrable.mono' hMajor hMeas hDom
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).2 hF

/-- Failure of L¹ on every terminal tail of a continuous source forces
cofinal, arbitrarily large physical Hilbert norms of the SAME source. -/
theorem h3Critical_continuous_physicalSource_nonintegrable_forces_spikes
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    {T : ℝ}
    (hCont : ContinuousOn F (Set.Ioo (0 : ℝ) T))
    (hNonInt : ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      ¬ IntervalIntegrable F volume b T) :
    ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ M < ‖F t‖ := by
  intro b hb M
  by_contra hNone
  have hBound : ∀ t : ℝ, t ∈ Set.Ioo b T → ‖F t‖ ≤ M := by
    intro t ht
    exact le_of_not_gt (by
      intro hLarge
      exact hNone ⟨t, ht, hLarge⟩)
  exact (hNonInt b hb)
    (h3Critical_continuous_physicalSource_integrable_of_terminal_ceiling
      F hCont b hb M hBound)

/-- One fixed physical source term, either the reconstructed Laplacian or
Leray forcing, is BOTH non-L¹ on every terminal tail and cofinally unbounded.
The choice no longer depends on time, tail, or requested amplitude. -/
theorem h3Critical_noL2Trace_fixed_physicalSource_nonintegrable_and_spikes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ((∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
        ¬ IntervalIntegrable
          (h3AuditInitialActualSpectralLaplacianTotal hH3) volume b T) ∧
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧
          M < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 t‖)) ∨
    ((∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
        ¬ IntervalIntegrable
          (h3AuditInitialActualSpectralLerayTotal hH3) volume b T) ∧
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧
          M < ‖h3AuditInitialActualSpectralLerayTotal hH3 t‖)) := by
  obtain ⟨hDCont, hNCont⟩ :=
    h3Critical_physicalSource_terms_continuousOn_positiveTime hH3
  rcases h3Critical_noL2Trace_fixed_physicalSource_nonintegrable
    hH3 hNoTrace with hD | hN
  · exact Or.inl ⟨hD,
      h3Critical_continuous_physicalSource_nonintegrable_forces_spikes
        _ hDCont hD⟩
  · exact Or.inr ⟨hN,
      h3Critical_continuous_physicalSource_nonintegrable_forces_spikes
        _ hNCont hN⟩

end
end PrimeTensor.Bridge.Euclidean

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedSpatialComponentSpikes
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# A single fixed physical coordinate bears the full terminal L¹ obstruction

For the *actual* three-component real physical Hilbert source, mathlib's
`integrable_piLp_iff` says Bochner integrability on a measurable time set
is equivalent to integrability of every scalar-L² coordinate.

If the vector source is non-L¹ on every terminal subinterval, and each of
three coordinates were L¹ on some (possibly different) subinterval, their
common later subinterval would make the vector integrable. Thus one single
coordinate is non-L¹ on ALL terminal subintervals.

Positive-time continuity upgrades the non-L¹ result to cofinal pointwise
spikes for the SAME coordinate, not an independently chosen one. The same
argument applies to the fixed physical Laplacian/Leray source alternative.

No assumption of positive terminal kinetic mass or finite H³ dissipation;
no unconditional regularity or smooth-continuation claim.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped Topology Interval

noncomputable section
set_option maxHeartbeats 800000

/-- Bochner integrability of a scalar physical L² source persists when the
left endpoint of a terminal interval moves forward. -/
theorem h3Critical_scalarL2_source_integrable_mono_terminal_tail
    (F : ℝ → H3ScalarL2)
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

/-- Exact Bochner-L¹ equivalence between the actual physical three-vector
and its three scalar-L² coordinate paths, on any ordered finite interval. -/
theorem h3Critical_fin3_hilbert_intervalIntegrable_iff_components
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b T : ℝ) (hbT : b < T) :
    IntervalIntegrable F volume b T ↔
      ∀ j : Fin 3,
        IntervalIntegrable (fun t : ℝ => (F t).ofLp j) volume b T := by
  constructor
  · intro hF j
    have hFIoo : IntegrableOn F (Set.Ioo b T) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hbT.le).mp hF
    have hCoord : IntegrableOn (fun t : ℝ => (F t).ofLp j)
        (Set.Ioo b T) volume :=
      (integrable_piLp_iff.mp hFIoo) j
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hbT.le).mpr hCoord
  · intro hComponents
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hbT.le).mpr
    apply integrable_piLp_iff.mpr
    intro j
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hbT.le).mp
      (hComponents j)

/-- A persistent finite-vector L¹ obstruction has one FIXED coordinate
which is non-L¹ on every terminal subinterval. Different coordinates
cannot each become integrable on their own later tail. -/
theorem h3Critical_fin3_fixed_component_nonintegrable_of_vector_nonintegrable
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (T : ℝ)
    (hNonInt : ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      ¬ IntervalIntegrable F volume b T) :
    ∃ j : Fin 3,
      ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
        ¬ IntervalIntegrable (fun t : ℝ => (F t).ofLp j) volume b T := by
  classical
  by_contra hMissing
  have hEach (j : Fin 3) :
      ∃ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T ∧
        IntervalIntegrable (fun t : ℝ => (F t).ofLp j) volume b T := by
    by_contra hAbsent
    apply hMissing
    refine ⟨j, ?_⟩
    intro b hb hFj
    exact hAbsent ⟨b, hb, hFj⟩
  obtain ⟨b0, hb0, h0⟩ := hEach 0
  obtain ⟨b1, hb1, h1⟩ := hEach 1
  obtain ⟨b2, hb2, h2⟩ := hEach 2
  let b : ℝ := max b0 (max b1 b2)
  have hb : b ∈ Set.Ioo (0 : ℝ) T := by
    dsimp only [b]
    exact ⟨lt_of_lt_of_le hb0.1 (le_max_left _ _),
      max_lt hb0.2 (max_lt hb1.2 hb2.2)⟩
  have hAll : ∀ j : Fin 3,
      IntervalIntegrable (fun t : ℝ => (F t).ofLp j) volume b T := by
    intro j
    fin_cases j
    · exact h3Critical_scalarL2_source_integrable_mono_terminal_tail
        _ hb0.2 hb.2 (le_max_left b0 (max b1 b2)) h0
    · exact h3Critical_scalarL2_source_integrable_mono_terminal_tail
        _ hb1.2 hb.2
        ((le_max_left b1 b2).trans (le_max_right b0 (max b1 b2))) h1
    · exact h3Critical_scalarL2_source_integrable_mono_terminal_tail
        _ hb2.2 hb.2
        ((le_max_right b1 b2).trans (le_max_right b0 (max b1 b2))) h2
  exact (hNonInt b hb)
    ((h3Critical_fin3_hilbert_intervalIntegrable_iff_components F b T hb.2).mpr hAll)

/-- For a continuous scalar-L² source, a terminal norm ceiling produces
Bochner integrability over that finite terminal interval. -/
theorem h3Critical_continuous_scalarL2_integrable_of_terminal_ceiling
    (F : ℝ → H3ScalarL2)
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

/-- Nonintegrability on every terminal interval forces cofinal L²-norm
spikes in the very SAME scalar source component. -/
theorem h3Critical_continuous_scalarL2_nonintegrable_forces_spikes
    (F : ℝ → H3ScalarL2)
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
    exact le_of_not_gt (fun hLarge => hNone ⟨t, ht, hLarge⟩)
  exact (hNonInt b hb)
    (h3Critical_continuous_scalarL2_integrable_of_terminal_ceiling
      F hCont b hb M hBound)

/-- A persistent three-component Bochner non-L¹ source selects ONE fixed
coordinate with both persistent non-L¹ and cofinal spikes. -/
theorem h3Critical_fin3_fixed_component_nonintegrability_and_spikes
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    {T : ℝ}
    (hCont : ContinuousOn F (Set.Ioo (0 : ℝ) T))
    (hNonInt : ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      ¬ IntervalIntegrable F volume b T) :
    ∃ j : Fin 3,
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
        ¬ IntervalIntegrable (fun t : ℝ => (F t).ofLp j) volume b T) ∧
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧ M < ‖(F t).ofLp j‖) := by
  obtain ⟨j, hj⟩ :=
    h3Critical_fin3_fixed_component_nonintegrable_of_vector_nonintegrable
      F T hNonInt
  have hEval : Continuous
      (fun V : H3PhysicalRealFinVectorL2Hilbert => V.ofLp j) :=
    PiLp.continuous_apply
      (2 : ENNReal) (fun _ : Fin 3 => H3ScalarL2) j
  have hCoordCont : ContinuousOn (fun t : ℝ => (F t).ofLp j)
      (Set.Ioo (0 : ℝ) T) :=
    hEval.comp_continuousOn hCont
  exact ⟨j, hj,
    h3Critical_continuous_scalarL2_nonintegrable_forces_spikes
      _ hCoordCont hj⟩

/-- The actual projected physical momentum source has ONE fixed component
which is non-L¹ on every terminal tail, and has cofinal norm spikes there.
The source and component are not selected anew for each threshold. -/
theorem h3Critical_noL2Trace_fixed_projected_coordinate_nonintegrable_and_spikes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ j : Fin 3,
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
        ¬ IntervalIntegrable
          (fun t : ℝ => (h3PathActualProjectedMomentumSource244 hH3 t).ofLp j)
          volume b T) ∧
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧
          M < ‖(h3PathActualProjectedMomentumSource244 hH3 t).ofLp j‖) := by
  have hCont : ContinuousOn (h3PathActualProjectedMomentumSource244 hH3)
      (Set.Ioo (0 : ℝ) T) := by
    change ContinuousOn
      (fun t : ℝ => h3AuditInitialActualSpectralLaplacianTotal hH3 t -
        h3AuditInitialActualSpectralLerayTotal hH3 t)
      (Set.Ioo (0 : ℝ) T)
    exact h3Audit_initialActualProjectedRHS_continuousOn_positiveTime hH3
  exact h3Critical_fin3_fixed_component_nonintegrability_and_spikes
    _ hCont
    (h3Critical_noL2Trace_forces_projected_source_nonintegrable_on_every_tail
      hH3 hNoTrace)

/-- One fixed source (physical Fourier Laplacian or Leray advection), and
one fixed spatial coordinate, are non-L¹ on every terminal subinterval AND
have cofinal L² spikes. Neither choice may depend on the tail or threshold. -/
theorem h3Critical_noL2Trace_fixed_laplacian_or_leray_coordinate_nonintegrable_and_spikes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    (∃ j : Fin 3,
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
        ¬ IntervalIntegrable
          (fun t : ℝ => (h3AuditInitialActualSpectralLaplacianTotal hH3 t).ofLp j)
          volume b T) ∧
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧
          M < ‖(h3AuditInitialActualSpectralLaplacianTotal hH3 t).ofLp j‖)) ∨
    (∃ j : Fin 3,
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
        ¬ IntervalIntegrable
          (fun t : ℝ => (h3AuditInitialActualSpectralLerayTotal hH3 t).ofLp j)
          volume b T) ∧
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧
          M < ‖(h3AuditInitialActualSpectralLerayTotal hH3 t).ofLp j‖)) := by
  obtain ⟨hDCont, hNCont⟩ :=
    h3Critical_physicalSource_terms_continuousOn_positiveTime hH3
  rcases h3Critical_noL2Trace_fixed_physicalSource_nonintegrable
    hH3 hNoTrace with hD | hN
  · exact Or.inl
      (h3Critical_fin3_fixed_component_nonintegrability_and_spikes
        _ hDCont hD)
  · exact Or.inr
      (h3Critical_fin3_fixed_component_nonintegrability_and_spikes
        _ hNCont hN)

end
end PrimeTensor.Bridge.Euclidean

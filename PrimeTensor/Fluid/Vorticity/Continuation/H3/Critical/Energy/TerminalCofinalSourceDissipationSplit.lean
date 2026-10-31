import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalDissipationObstruction
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# Terminal source and dissipation cofinal spikes without kinetic mass hypotheses

The verified terminal obstruction gives non-L¹ actual projected momentum
source on every terminal tail whenever the actual physical L² terminal trace
fails. A continuous source on the finite open interval would be L¹ if it were
bounded. Therefore its physical Hilbert norm is cofinally unbounded.

The pre-existing exact source-to-H³-energy bound then forces cofinally large
full H³ energy, without needing positive terminal kinetic mass. The anchored
interpolation estimate forces cofinally large full H³ dissipation.

Separately, since the actual source is the physical Fourier Laplacian minus
the Fourier-reconstructed Leray forcing, at least one of those two terms must
fail to be L¹ on each terminal interval; at arbitrarily late times, one term
must have arbitrarily large norm.

These are necessary conditions under failure of an L² terminal trace, not a
proof of failure of the trace or of unconditional Navier--Stokes regularity.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped Topology Interval

noncomputable section
set_option maxHeartbeats 800000

/-- A bounded actual projected source on a finite positive terminal interval
is Bochner L¹. This uses positive-time source continuity, not an extra
measurability hypothesis. -/
theorem h3Critical_projected_source_integrable_of_terminal_norm_ceiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : b ∈ Set.Ioo (0 : ℝ) T)
    (M : ℝ)
    (hBound : ∀ t : ℝ, t ∈ Set.Ioo b T →
      ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ≤ M) :
    IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
      volume b T := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hConst : IntervalIntegrable (fun _ : ℝ => M) volume b T :=
    continuousOn_const.intervalIntegrable_of_Icc hb.2.le
  have hMajor : IntegrableOn (fun _ : ℝ => M) (Set.Ioo b T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).1 hConst
  have hSub : Set.Ioo b T ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hCont : ContinuousOn G (Set.Ioo b T) := by
    have hFull := h3Audit_initialActualProjectedRHS_continuousOn_positiveTime hH3
    change ContinuousOn
      (fun t : ℝ => h3AuditInitialActualSpectralLaplacianTotal hH3 t -
        h3AuditInitialActualSpectralLerayTotal hH3 t) (Set.Ioo b T)
    exact hFull.mono hSub
  have hMeas : AEStronglyMeasurable G
      ((volume : Measure ℝ).restrict (Set.Ioo b T)) :=
    hCont.aestronglyMeasurable measurableSet_Ioo
  have hDom : ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioo b T)),
      ‖G t‖ ≤ M :=
    ae_restrict_of_forall_mem measurableSet_Ioo (by
      intro t ht
      exact hBound t ht)
  have hG : IntegrableOn G (Set.Ioo b T) volume :=
    Integrable.mono' hMajor hMeas hDom
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).2 hG

/-- Absence of a physical L² terminal trace forces the actual projected
physical Hilbert source to exceed every amplitude on every terminal tail. -/
theorem h3Critical_noL2Trace_projected_source_cofinally_unbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        M < ‖h3PathActualProjectedMomentumSource244 hH3 t‖ := by
  intro b hb M
  by_contra hNone
  have hBound : ∀ t : ℝ, t ∈ Set.Ioo b T →
      ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ≤ M := by
    intro t ht
    exact le_of_not_gt (by
      intro hLarge
      exact hNone ⟨t, ht, hLarge⟩)
  exact
    (h3Critical_noL2Trace_forces_projected_source_nonintegrable_on_every_tail
      hH3 hNoTrace b hb)
    (h3Critical_projected_source_integrable_of_terminal_norm_ceiling
      hH3 b hb M hBound)

/-- The source spike transfers to cofinal full H³ energy escape even without
assuming strictly positive terminal kinetic mass. -/
theorem h3Critical_noL2Trace_fullEnergy_cofinally_unbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ M < velocityH3EnergyAt u t := by
  intro b hb M
  have hb0 : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  let K : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  have hK : 0 ≤ K := by
    dsimp only [K]
    have h := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [h]
  obtain ⟨t, ht, hLarge⟩ :=
    h3Critical_noL2Trace_projected_source_cofinally_unbounded
      hH3 hNoTrace b hb0 (K * M)
  refine ⟨t, ht, ?_⟩
  have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hb0.1 ht.1, ht.2⟩
  have hSource := h3Path_physicalProjectedSource_norm_le_H3Energy244
    hH3 t ht0
  by_contra hNot
  have hEM : velocityH3EnergyAt u t ≤ M := le_of_not_gt hNot
  have hUpper :
      ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ≤ K * M := by
    exact hSource.trans (mul_le_mul_of_nonneg_left hEM hK)
  exact (not_le_of_gt hLarge) hUpper

/-- No physical L² terminal trace forces arbitrarily high full H³ viscous
dissipation on every terminal tail. This is stronger in form than merely
asserting nonintegrability, and uses no terminal kinetic-mass premise. -/
theorem h3Critical_noL2Trace_fullDissipation_cofinally_unbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        M < velocityH3DissipationAt u t := by
  intro b hb M
  obtain ⟨t, ht, hLarge⟩ :=
    h3Critical_noL2Trace_fullEnergy_cofinally_unbounded
      hH3 hClass hNoTrace b hb
      (1 + 6 * velocityH3Energy0At u b + 3 * M)
  refine ⟨t, ht, ?_⟩
  have hEnergy := h3Critical_energy_le_kinetic_anchor_add_dissipation
    hH3 hClass hb ht
  by_contra hNot
  have hDle : velocityH3DissipationAt u t ≤ M := le_of_not_gt hNot
  linarith only [hLarge, hEnergy, hDle]

/-- At least one of the two actual physical source terms fails Bochner L¹
on each terminal interval, since their difference is the non-L¹ source. -/
theorem h3Critical_noL2Trace_laplacian_or_leray_nonintegrable_on_every_tail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      (¬ IntervalIntegrable
        (h3AuditInitialActualSpectralLaplacianTotal hH3) volume b T) ∨
      (¬ IntervalIntegrable
        (h3AuditInitialActualSpectralLerayTotal hH3) volume b T) := by
  intro b hb
  by_contra hNeither
  have hD : IntervalIntegrable
      (h3AuditInitialActualSpectralLaplacianTotal hH3) volume b T := by
    by_contra hNot
    exact hNeither (Or.inl hNot)
  have hN : IntervalIntegrable
      (h3AuditInitialActualSpectralLerayTotal hH3) volume b T := by
    by_contra hNot
    exact hNeither (Or.inr hNot)
  have hSource : IntervalIntegrable
      (h3PathActualProjectedMomentumSource244 hH3) volume b T := by
    change IntervalIntegrable
      (fun t : ℝ => h3AuditInitialActualSpectralLaplacianTotal hH3 t -
        h3AuditInitialActualSpectralLerayTotal hH3 t) volume b T
    exact hD.sub hN
  exact
    (h3Critical_noL2Trace_forces_projected_source_nonintegrable_on_every_tail
      hH3 hNoTrace b hb) hSource

/-- On every strict terminal tail, either the physical Laplacian or the
Leray-transport source has an arbitrarily large norm at some later time.
The alternative may switch with the tail and threshold. -/
theorem h3Critical_noL2Trace_laplacian_or_leray_cofinal_norm_spike
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        (M < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 t‖ ∨
         M < ‖h3AuditInitialActualSpectralLerayTotal hH3 t‖) := by
  intro b hb M
  obtain ⟨t, ht, hLarge⟩ :=
    h3Critical_noL2Trace_projected_source_cofinally_unbounded
      hH3 hNoTrace b hb (2 * M)
  refine ⟨t, ht, ?_⟩
  by_contra hNeither
  have hDle : ‖h3AuditInitialActualSpectralLaplacianTotal hH3 t‖ ≤ M :=
    le_of_not_gt (by
      intro hBig
      exact hNeither (Or.inl hBig))
  have hNle : ‖h3AuditInitialActualSpectralLerayTotal hH3 t‖ ≤ M :=
    le_of_not_gt (by
      intro hBig
      exact hNeither (Or.inr hBig))
  have hTriangle := norm_sub_le
    (h3AuditInitialActualSpectralLaplacianTotal hH3 t)
    (h3AuditInitialActualSpectralLerayTotal hH3 t)
  change 2 * M < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 t -
    h3AuditInitialActualSpectralLerayTotal hH3 t‖ at hLarge
  linarith only [hTriangle, hDle, hNle, hLarge]

end
end PrimeTensor.Bridge.Euclidean

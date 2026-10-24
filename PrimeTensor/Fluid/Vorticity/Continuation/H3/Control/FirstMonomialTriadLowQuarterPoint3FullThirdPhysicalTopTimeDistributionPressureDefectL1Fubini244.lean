import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionOldTemporalL1L2Fubini244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Temporal.Pressure.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Temporal.Pressure.Family
import Mathlib.Tactic

/-!
# Reduce the actual physical momentum distribution to pressure-defect L¹ mass

The endpoint-independent old temporal mass decomposes, for each compact test,
into an already uniformly H³-bounded projected-RHS mass and the canonical-vs-old
pressure-gradient defect mass. Unlike the previous temporal L¹L² criterion,
the pressure defect is NOT required to have a global spatial L² representative.

A time-integrable scalar majorant of its compact-tested spatial L¹ mass suffices.
The prior joint measurability theorem supplies measurability of the actual old
temporal mass; the projected RHS bound and Integrable.mono' then give time
integrability. The repository's old Fubini theorem yields the genuine physical
Hilbert derivative and distributional momentum on straddling restart windows.

This does not prove the pressure-defect majorant from H³ admissibility: the
remaining analytic question is precisely a pressure gauge / pressure-defect
estimate, rather than a new condition on the full temporal derivative.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators ENNReal InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3PressureDefectL1Fubini244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PressureDefectL1Fubini244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- For every compact solenoidal spatial test and coordinate, the OLD-minus-
canonical pressure-gradient defect has an integrable temporal upper profile
for its compact-tested spatial absolute mass. The pressure defect itself need
not be spatial L²; no uniform temporal bound is requested. -/
def h3PreterminalPressureDefectL1MassOnElapsed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ i : Fin 3,
      ∃ g : ℝ → ℝ,
        Integrable g
          ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) τ)) ∧
        ∀ r : ℝ, (hr : r ∈ Set.Ioo (0 : ℝ) τ) →
          h3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassOnElapsed
              hNS ht hEnd hTail
              (⟨r, hr.1.le, hr.2.le⟩ : Set.Icc (0 : ℝ) τ)
              i (φ i) ≤ g r

/-- An integrable pressure-defect mass profile and the previously proved
uniform projected-RHS mass estimate imply integrability in elapsed time of
the ACTUAL old temporal mass, for every compact test coordinate and prefix.
The only measurability input is the old temporal joint-measurability theorem. -/
theorem h3Preterminal_oldTemporalMassIntegrable_of_pressureDefectL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure : h3PreterminalPressureDefectL1MassOnElapsed244
      hNS ht hEnd hTail)
    (φ : H3WeakTestVector) (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) τ) :
    H3PreterminalLoggedVelocityTemporalSpatialNormMassIntegrableTo
      hNS t (q : ℝ) φ := by
  intro i
  obtain ⟨g, hg, hPressureBound⟩ := hPressure φ hφ i
  let μq : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (q : ℝ))
  let M : ℝ → ℝ :=
    h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed
      hNS t i (φ i)
  let C : ℝ := h3UnitViscosityZeroProjectedRHSWeakTestMassBound E φ
  have hSubset : Set.Ioo (0 : ℝ) (q : ℝ) ⊆ Set.Ioo (0 : ℝ) τ := by
    intro r hr
    exact ⟨hr.1, lt_of_lt_of_le hr.2 q.property.2⟩
  have hgq : Integrable g μq := by
    exact hg.mono_measure (Measure.restrict_mono hSubset le_rfl)
  have hConst : Integrable (fun _ : ℝ => C) μq := by
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
      q.property.1).1 intervalIntegrable_const
  have hMajor : Integrable (fun r : ℝ => C + g r) μq :=
    hConst.add hgq
  have hMeas : AEStronglyMeasurable M μq := by
    exact
      (h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed_aestronglyMeasurable
        hNS i (φ i)).mono_measure Measure.restrict_le_self
  have hDom : ∀ᵐ r ∂μq, ‖M r‖ ≤ C + g r := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo]
      with r hr
    have hrτ : r ∈ Set.Ioo (0 : ℝ) τ := hSubset hr
    let rSub : Set.Icc (0 : ℝ) τ :=
      ⟨r, hrτ.1.le, hrτ.2.le⟩
    have hSplit :=
      h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed_le_projectedRHS_add_pressureDefect
        hNS ht hEnd hTail rSub i (φ i)
    have hProjected :=
      h3PreterminalTailCanonicalZeroProjectedRHSSpatialNormMassOnElapsed_le_aggregate
        hNS ht hEnd hE hTail φ rSub i
    have hDefect :
        h3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassOnElapsed
          hNS ht hEnd hTail rSub i (φ i) ≤ g r :=
      hPressureBound r hrτ
    have hMassBound : M r ≤ C + g r := by
      exact hSplit.trans (add_le_add hProjected hDefect)
    have hNonneg : 0 ≤ M r :=
      h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed_nonneg
        hNS i (φ i) r
    calc
      ‖M r‖ = M r := Real.norm_of_nonneg hNonneg
      _ ≤ C + g r := hMassBound
  exact Integrable.mono' hMajor hMeas hDom

/-- Pressure-defect temporal L¹ mass closes the endpoint-independent OLD
physical weak Fubini condition, without old temporal L¹L² membership. -/
theorem h3Preterminal_oldTemporalProductFubini_of_pressureDefectL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure : h3PreterminalPressureDefectL1MassOnElapsed244
      hNS ht hEnd hTail) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
      hNS ht hEnd hTail := by
  intro φ hφ q
  apply H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_spatialNormMassIntegrable
    hNS t (q : ℝ) φ
  exact h3Preterminal_oldTemporalMassIntegrable_of_pressureDefectL1Mass244
    hNS ht hEnd hE hTail hPressure φ hφ q

/-- The older uniform pressure-defect mass criterion is a special case of
the new, strictly weaker temporal L¹-majorant criterion. -/
theorem h3Preterminal_pressureDefectL1Mass_of_uniformPressureDefectMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hτ : 0 ≤ τ)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail) :
    h3PreterminalPressureDefectL1MassOnElapsed244 hNS ht hEnd hTail := by
  intro φ hφ i
  obtain ⟨C, hC⟩ := hPressure φ hφ
  refine ⟨fun _ => C, ?_, ?_⟩
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hτ).1
      intervalIntegrable_const
  · intro r hr
    exact hC i ⟨r, hr.1.le, hr.2.le⟩

/-- A straddling H³ restart whose only extra PDE-side input is an L¹-in-time
compact-test mass profile of the old-vs-canonical pressure gradient. -/
def h3PathInteriorTimePressureDefectL1MassAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) : Prop :=
  ∃ (t₀ S E τ : ℝ)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (_hST : S < T)
    (_hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ S E)
    (_hτ : 0 < τ)
    (hEnd : t₀ + τ < S)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S),
      s ∈ Set.Ioo t₀ (t₀ + τ) ∧
      h3PreterminalPressureDefectL1MassOnElapsed244
        hNSShort ht₀ hEnd hTail

/-- The pressure-defect L¹ mass gives the already proved interior OLD Fubini
hypothesis on the very same straddling restart geometry. -/
theorem h3Path_interiorOldTemporalProductFubini_of_pressureDefectL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hPressure : h3PathInteriorTimePressureDefectL1MassAt244 hH3 s) :
    h3PathInteriorTimeOldTemporalProductIntegrabilityAt244 hH3 s := by
  rcases hPressure with
    ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
      hNSShort, hs, hPress⟩
  refine ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
    hNSShort, hs, ?_⟩
  exact h3Preterminal_oldTemporalProductFubini_of_pressureDefectL1Mass244
    hNSShort ht₀ hEnd hE hTail hPress

/-- Old physical Hilbert derivative from the isolated L¹ pressure-defect
mass criterion and the already closed H³ projected-RHS norm ceiling. -/
theorem h3Path_physicalHilbertHasDerivAt_of_pressureDefectL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hPressure : h3PathInteriorTimePressureDefectL1MassAt244 hH3 s) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3 s) s := by
  exact h3Path_physicalHilbertHasDerivAt_of_oldTemporalProductFubini244
    hH3 (h3Path_interiorOldTemporalProductFubini_of_pressureDefectL1Mass244
      hH3 hPressure)

/-- Genuine physical time-distributional momentum from a pressure-only
L¹ temporal compact-test hypothesis, with no temporal L¹L² assumption. -/
theorem h3Path_distributionalMomentum_of_pressureDefectL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hPressure : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimePressureDefectL1MassAt244 hH3 s) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply h3Path_distributionalMomentum_of_oldTemporalProductFubini244
    hH3 ha hab hb
  intro s hs
  exact h3Path_interiorOldTemporalProductFubini_of_pressureDefectL1Mass244
    hH3 (hPressure s hs)

/-- The literal compact smooth temporal-test identity for momentum follows
from the pressure-defect L¹ mass criterion. -/
theorem h3Path_timeTestMomentum_of_pressureDefectL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hPressure : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimePressureDefectL1MassAt244 hH3 s) :
    h3PathSolenoidalTimeTestMomentumOn244 hH3 a b := by
  exact (h3Path_distributionalMomentum_iff_timeTestMomentum244
    hH3 ha hab hb).mp
    (h3Path_distributionalMomentum_of_pressureDefectL1Mass244
      hH3 ha hab hb hPressure)

/-- Any nonzero actual physical Hilbert FTC defect forces failure of the
pressure-defect L¹ profile condition on some interior straddling restart. -/
theorem h3Path_nonzeroPhysicalFTCDefect_forces_pressureDefectL1Failure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ s : ℝ, s ∈ Set.Ioo a b ∧
      ¬ h3PathInteriorTimePressureDefectL1MassAt244 hH3 s := by
  obtain ⟨s, hs, hFail⟩ :=
    h3Path_nonzeroPhysicalFTCDefect_forces_oldTemporalProductFubiniFailure244
      hH3 ha hab hb hNonzero
  refine ⟨s, hs, ?_⟩
  intro hPressure
  exact hFail (h3Path_interiorOldTemporalProductFubini_of_pressureDefectL1Mass244
    hH3 hPressure)

end
end PrimeTensor.FirstMonomialTriad

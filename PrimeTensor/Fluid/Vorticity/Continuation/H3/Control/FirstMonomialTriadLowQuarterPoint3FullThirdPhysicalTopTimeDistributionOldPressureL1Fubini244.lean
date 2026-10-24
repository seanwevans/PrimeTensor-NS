import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionPressureDefectL1Fubini244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Temporal.Pressure.Canonical.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Temporal.Pressure.Witness
import Mathlib.Tactic

/-!
# Old pressure L¹ test mass, canonical pressure bound, and physical momentum

The prior endpoint-independent physical momentum criterion asks for an integrable
elapsed-time envelope of the compact-tested old-minus-canonical pressure-gradient
mass. The canonical pressure-gradient term is already bounded uniformly from
the H³ snapshot, independently of the old pressure witness. Thus the only
remaining quantitative input in this route is local temporal integrability of
the compact-tested OLD pressure gradient.

We also transport that condition through the previously proved uniqueness of
the pressure gradient for two pressure witnesses of the same preterminal velocity.
The condition is not a choice-of-pressure artifact. This file does NOT infer
old-pressure temporal integrability merely from separate spacetime continuity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators ENNReal InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3OldPressureL1Fubini244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3OldPressureL1Fubini244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A time-integrable compact-test absolute-mass profile of the OLD pressure
spatial gradient. No bound on the canonical pressure, pressure difference, or
raw old temporal velocity derivative is included in this premise. -/
def h3PreterminalOldPressureL1MassOnElapsed244
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
          h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed
              hNS ht hEnd hTail
              (⟨r, hr.1.le, hr.2.le⟩ : Set.Icc (0 : ℝ) τ)
              i (φ i) ≤ g r

/-- The canonical H³ pressure gradient is already uniformly bounded. Its
compact-tested mass contributes only an integrable constant to the old-pressure
profile. Thus OLD pressure L¹ mass yields the actual pressure-defect L¹ mass. -/
theorem h3Preterminal_pressureDefectL1Mass_of_oldPressureL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hτ : 0 ≤ τ)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hOld : h3PreterminalOldPressureL1MassOnElapsed244 hNS ht hEnd hTail) :
    h3PreterminalPressureDefectL1MassOnElapsed244 hNS ht hEnd hTail := by
  intro φ hφ i
  obtain ⟨g, hg, hgBound⟩ := hOld φ hφ i
  let C : ℝ :=
    h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound E *
      h3WeakTestFunctionL1Mass (φ i)
  have hConst : Integrable (fun _ : ℝ => C)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) τ)) := by
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hτ).1
      intervalIntegrable_const
  refine ⟨fun r => g r + C, hg.add hConst, ?_⟩
  intro r hr
  let q : Set.Icc (0 : ℝ) τ := ⟨r, hr.1.le, hr.2.le⟩
  have hSplit :=
    h3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassOnElapsed_le_old_add_canonical
      hNS ht hEnd hTail q i (φ i)
  have hOldBound :
      h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i (φ i) ≤ g r := hgBound r hr
  have hCanonical :
      h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i (φ i) ≤ C := by
    dsimp only [C]
    exact h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed_le
      hNS ht hEnd hE hTail q i (φ i)
  exact hSplit.trans (add_le_add hOldBound hCanonical)

/-- A temporal mass profile of the chosen old pressure witness may equivalently
be verified on ANY pressure solving the same preterminal Navier--Stokes PDE;
spatial pressure gradients are witness-independent. -/
def h3PreterminalPressureWitnessL1MassOnElapsed244
    {t τ : ℝ}
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ i : Fin 3,
      ∃ g : ℝ → ℝ,
        Integrable g
          ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) τ)) ∧
        ∀ r : ℝ, (hr : r ∈ Set.Ioo (0 : ℝ) τ) →
          h3PressureWitnessGradientSpatialNormMassOnElapsed
            (t := t) p
            (⟨r, hr.1.le, hr.2.le⟩ : Set.Icc (0 : ℝ) τ)
            i (φ i) ≤ g r

/-- Pressure-witness independence of the temporal compact-test L¹ condition. -/
theorem h3Preterminal_oldPressureL1Mass_of_pressureWitnessL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hPDE : PreterminalNavierStokes3 (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T)
    (hWitness : h3PreterminalPressureWitnessL1MassOnElapsed244
      (t := t) (τ := τ) p) :
    h3PreterminalOldPressureL1MassOnElapsed244 hNS ht hEnd hTail := by
  intro φ hφ i
  obtain ⟨g, hg, hBound⟩ := hWitness φ hφ i
  refine ⟨g, hg, ?_⟩
  intro r hr
  let q : Set.Icc (0 : ℝ) τ := ⟨r, hr.1.le, hr.2.le⟩
  calc
    h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i (φ i) =
      h3PressureWitnessGradientSpatialNormMassOnElapsed
        (t := t) p q i (φ i) :=
          h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed_eq_pressureWitness
            hNS ht hEnd hTail p hPDE q i (φ i)
    _ ≤ g r := hBound r hr

/-- Old-pressure L¹ mass closes the Fubini hypothesis through the proven
canonical-pressure bound and the preceding pressure-defect L¹ bridge. -/
theorem h3Preterminal_oldTemporalProductFubini_of_oldPressureL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hτ : 0 ≤ τ)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hOld : h3PreterminalOldPressureL1MassOnElapsed244 hNS ht hEnd hTail) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
      hNS ht hEnd hTail := by
  exact h3Preterminal_oldTemporalProductFubini_of_pressureDefectL1Mass244
    hNS ht hEnd hE hTail
    (h3Preterminal_pressureDefectL1Mass_of_oldPressureL1Mass244
      hNS ht hEnd hE hτ hTail hOld)

/-- A straddling physical restart with local temporal integrability of the
OLD pressure gradient only. The rest of the distributional momentum machinery
is already in the repository. -/
def h3PathInteriorTimeOldPressureL1MassAt244
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
      h3PreterminalOldPressureL1MassOnElapsed244
        hNSShort ht₀ hEnd hTail

/-- Old pressure L¹ mass on a genuine straddling restart implies the
pressure-defect corridor from the preceding checkpoint. -/
theorem h3Path_interiorPressureDefectL1Mass_of_oldPressureL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOld : h3PathInteriorTimeOldPressureL1MassAt244 hH3 s) :
    h3PathInteriorTimePressureDefectL1MassAt244 hH3 s := by
  rcases hOld with
    ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
      hNSShort, hs, hOldMass⟩
  refine ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
    hNSShort, hs, ?_⟩
  exact h3Preterminal_pressureDefectL1Mass_of_oldPressureL1Mass244
    hNSShort ht₀ hEnd hE hτ.le hTail hOldMass

/-- The actual physical Hilbert derivative from old-pressure temporal mass. -/
theorem h3Path_physicalHilbertHasDerivAt_of_oldPressureL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOld : h3PathInteriorTimeOldPressureL1MassAt244 hH3 s) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3 s) s := by
  exact h3Path_physicalHilbertHasDerivAt_of_pressureDefectL1Mass244
    hH3 (h3Path_interiorPressureDefectL1Mass_of_oldPressureL1Mass244
      hH3 hOld)

/-- Solenoidal physical distributional momentum from the old-pressure mass
condition alone, without a separately assumed pressure-difference envelope. -/
theorem h3Path_distributionalMomentum_of_oldPressureL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hOld : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeOldPressureL1MassAt244 hH3 s) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply h3Path_distributionalMomentum_of_pressureDefectL1Mass244
    hH3 ha hab hb
  intro s hs
  exact h3Path_interiorPressureDefectL1Mass_of_oldPressureL1Mass244
    hH3 (hOld s hs)

/-- Literal smooth compact temporal-test momentum equation. -/
theorem h3Path_timeTestMomentum_of_oldPressureL1Mass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hOld : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeOldPressureL1MassAt244 hH3 s) :
    h3PathSolenoidalTimeTestMomentumOn244 hH3 a b := by
  exact (h3Path_distributionalMomentum_iff_timeTestMomentum244
    hH3 ha hab hb).mp
    (h3Path_distributionalMomentum_of_oldPressureL1Mass244
      hH3 ha hab hb hOld)

/-- If the actual physical momentum FTC defect is nonzero, some interior time
fails the old-pressure L¹ criterion on every admissible straddling restart. -/
theorem h3Path_nonzeroPhysicalFTCDefect_forces_oldPressureL1Failure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ s : ℝ, s ∈ Set.Ioo a b ∧
      ¬ h3PathInteriorTimeOldPressureL1MassAt244 hH3 s := by
  obtain ⟨s, hs, hFail⟩ :=
    h3Path_nonzeroPhysicalFTCDefect_forces_pressureDefectL1Failure244
      hH3 ha hab hb hNonzero
  refine ⟨s, hs, ?_⟩
  intro hOld
  exact hFail (h3Path_interiorPressureDefectL1Mass_of_oldPressureL1Mass244
    hH3 hOld)

end
end PrimeTensor.FirstMonomialTriad

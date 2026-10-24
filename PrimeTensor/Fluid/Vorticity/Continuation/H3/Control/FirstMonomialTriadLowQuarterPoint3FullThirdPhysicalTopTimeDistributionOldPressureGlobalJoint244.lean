import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionOldPressureSelectedJoint244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Temporal.Pressure.Joint
import Mathlib.Tactic

/-!
# Global positive-time old-pressure joint continuity from sliding selected slabs

Every strict preterminal observation lies inside a selected restart based at
an earlier positive anchor. The selected pressure gradient is jointly
continuous on that slab and agrees with the old pressure gradient by the
already established curl weak-FTC / selected physical evolution bridge.

Pressure-gradient witness uniqueness makes this local fact independent of
which valid old preterminal pressure was chosen. Hence the original old
pressure gradient is jointly continuous on the entire OPEN (0,T) cylinder.

The already-proved compact-cylinder theorem then bounds its compact-tested
spatial mass on each closed elapsed interval, yielding its L1 time profile,
the old Fubini hypothesis, physical Hilbert differentiation, and the genuine
physical momentum time-distribution equation.

This implication is relative to LoggedPreterminalH3PathAdmissible, which
includes a classical preterminal NS PDE. It does NOT prove endpoint extension
or global smoothness up to a potentially singular terminal time T.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3OldPressureGlobalJoint244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

local instance point3NormTopologicalSpaceH3OldPressureGlobalJoint244 :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Sliding selected-restart slabs, already justified by curl weak FTC,
cover the open preterminal cylinder. Their old-pressure gradient continuity
glues through pressure-gradient uniqueness for the fixed global PDE witness. -/
theorem h3Path_oldPressureGradient_jointlyContinuousOnPreterminal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous
      hH3.navier_stokes := by
  unfold H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous
  dsimp only
  intro j
  apply continuousOn_of_forall_continuousAt
  intro z hz
  obtain ⟨t₀, S, E, ht₀, hST, hE, hTail,
    hq0, hqR, hts, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hz.1
  let q : ℝ := z.1 - t₀
  let R : ℝ := h3FinHeatLerayRestartRadius (1 : ℝ) E
  let upper : ℝ := min R (S - t₀)
  have hqUpper : q < upper := by
    dsimp only [q, upper, R]
    apply lt_min hqR
    linarith only [hsS]
  let τ : ℝ := (q + upper) / 2
  have hqτ : q < τ := by
    dsimp only [τ]
    linarith only [hqUpper]
  have hτUpper : τ < upper := by
    dsimp only [τ]
    linarith only [hqUpper]
  have hτpos : 0 < τ := by
    have hqpos : 0 < q := hq0
    linarith only [hqpos, hqτ]
  have hτR : τ ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    have hUpperR : upper ≤ R := min_le_left _ _
    dsimp only [R] at hUpperR
    exact (le_of_lt hτUpper).trans hUpperR
  have hEnd : t₀ + τ < S := by
    have hUpperS : upper ≤ S - t₀ := min_le_right _ _
    linarith only [hτUpper, hUpperS]
  have hSpos : 0 < S := lt_trans ht₀.1 ht₀.2
  let hNSShort : LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes hSpos hST.le
  have hSelectedJoint :
      H3PreterminalPressureFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
        (t := t₀) (tau := τ) hNSShort :=
    h3Preterminal_oldPressureJointOnSelectedAbsoluteSlab244
      hNSShort ht₀ hτpos hEnd hE hTail hτR
  unfold H3PreterminalPressureFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
    at hSelectedJoint
  dsimp only at hSelectedJoint
  have hFullPDEShort :
      PreterminalNavierStokes3
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        (Classical.choose hH3.navier_stokes) S :=
    (Classical.choose_spec hH3.navier_stokes).mono_terminal
      hSpos hST.le
  have hFullOn :
      ContinuousOn
        (fun w : ℝ × Point3 =>
          spatial3.d j
            ((Classical.choose hH3.navier_stokes :
              SpaceTimeScalarField ℝ ℝ ℝ Depth.three) w.1) w.2)
        (Set.Ioo t₀ (t₀ + τ) ×ˢ Set.univ) := by
    apply (hSelectedJoint j).congr
    intro w hw
    have hwS : w.1 ∈ Set.Ioo (0 : ℝ) S := by
      exact ⟨lt_trans ht₀.1 hw.1.1,
        lt_trans hw.1.2 hEnd⟩
    exact (preterminalNavierStokes3_pressureGradient_eq
      (Classical.choose_spec hNSShort)
      hFullPDEShort hwS w.2 j).symm
  have hzSlab : z ∈ Set.Ioo t₀ (t₀ + τ) ×ˢ Set.univ := by
    constructor
    · constructor
      · linarith only [hq0]
      · change z.1 - t₀ < τ at hqτ
        linarith only [hqτ]
    · exact Set.mem_univ z.2
  exact hFullOn.continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hzSlab)

/-- Pressure-gradient joint continuity transfers from the full H3-path
pressure witness to any shortened preterminal pressure witness. -/
theorem h3Path_oldPressureGradient_jointlyContinuousOnShortTerminal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hS : 0 < S) (hST : S ≤ T)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S) :
    H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous
      hNSShort := by
  have hFull := h3Path_oldPressureGradient_jointlyContinuousOnPreterminal244 hH3
  unfold H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous at hFull ⊢
  dsimp only at hFull ⊢
  intro j
  have hFullOn :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          spatial3.d j
            ((Classical.choose hH3.navier_stokes :
              SpaceTimeScalarField ℝ ℝ ℝ Depth.three) z.1) z.2)
        (Set.Ioo (0 : ℝ) S ×ˢ Set.univ) := by
    apply (hFull j).mono
    intro z hz
    exact ⟨⟨hz.1.1, lt_of_lt_of_le hz.1.2 hST⟩,
      Set.mem_univ z.2⟩
  apply hFullOn.congr
  intro z hz
  have hFullPDEShort :
      PreterminalNavierStokes3
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        (Classical.choose hH3.navier_stokes) S :=
    (Classical.choose_spec hH3.navier_stokes).mono_terminal hS hST
  exact (preterminalNavierStokes3_pressureGradient_eq
    hFullPDEShort (Classical.choose_spec hNSShort)
    hz.1 z.2 j).symm

/-- The old pressure L1-in-time compact-test condition now follows from
H3-path admissibility on ANY strictly internal shortened restart window. -/
theorem h3Preterminal_oldPressureL1Mass_of_h3Path244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hS : 0 < S) (hST : S ≤ T)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hτ : 0 ≤ τ) (hEnd : t + τ < S)
    (hTail : CanonicalH3TailDataFrom u t S E) :
    h3PreterminalOldPressureL1MassOnElapsed244 hNSShort ht hEnd hTail := by
  have hShortJoint :
      H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous hNSShort :=
    h3Path_oldPressureGradient_jointlyContinuousOnShortTerminal244
      hH3 hS hST hNSShort
  have hUniform :=
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed_of_pressureJoint
      hNSShort ht hτ hEnd hTail hShortJoint
  intro φ hφ i
  obtain ⟨C, hC⟩ := hUniform φ hφ
  refine ⟨fun _ => C, ?_, ?_⟩
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hτ).1
      intervalIntegrable_const
  · intro r hr
    exact hC i ⟨r, hr.1.le, hr.2.le⟩

/-- A previously existing local H3 restart is rebased to a window straddling
s. Full old-pressure joint continuity supplies the missing L1 premise. -/
theorem h3Path_interiorOldPressureL1Mass_fromH3Admissible244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    h3PathInteriorTimeOldPressureL1MassAt244 hH3 s := by
  obtain ⟨t₀, S, E, ht₀, hST, hE, hTail,
    hq0, _hqR, _hts, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hs
  let q : ℝ := s - t₀
  have hqS : q < S - t₀ := by
    dsimp only [q]
    linarith only [hsS]
  let τ : ℝ := (q + (S - t₀)) / 2
  have hqτ : q < τ := by
    dsimp only [τ]
    linarith only [hqS]
  have hτpos : 0 < τ := by
    have hqpos : 0 < q := hq0
    linarith only [hqpos, hqτ]
  have hEnd : t₀ + τ < S := by
    dsimp only [τ]
    linarith only [hqS]
  have hsWindow : s ∈ Set.Ioo t₀ (t₀ + τ) := by
    constructor
    · linarith only [hq0]
    · change s - t₀ < τ at hqτ
      linarith only [hqτ]
  have hSpos : 0 < S := lt_trans ht₀.1 ht₀.2
  let hNSShort : LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes hSpos hST.le
  refine ⟨t₀, S, E, τ, ht₀, hST, hE, hTail,
    hτpos, hEnd, hNSShort, hsWindow, ?_⟩
  exact h3Preterminal_oldPressureL1Mass_of_h3Path244
    hH3 hSpos hST.le hNSShort ht₀ hτpos.le hEnd hTail

/-- Physical Hilbert differentiation requires no EXTRA old-pressure temporal
mass assumption once the H3-path-admissible old PDE is fixed. -/
theorem h3Path_physicalHilbertHasDerivAt_fromH3Admissible244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3 s) s := by
  exact h3Path_physicalHilbertHasDerivAt_of_oldPressureL1Mass244
    hH3 (h3Path_interiorOldPressureL1Mass_fromH3Admissible244 hH3 hs)

/-- The literal physical solenoidal momentum time-distribution identity on
strict intervals, now without a new pressure profile hypothesis. -/
theorem h3Path_distributionalMomentum_fromH3Admissible244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply h3Path_distributionalMomentum_of_oldPressureL1Mass244
    hH3 ha hab hb
  intro s hs
  exact h3Path_interiorOldPressureL1Mass_fromH3Admissible244
    hH3 ⟨lt_trans ha hs.1, lt_trans hs.2 hb⟩

/-- Time-test form of the same unconditional (relative to the H3 path)
interior physical momentum equation. -/
theorem h3Path_timeTestMomentum_fromH3Admissible244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    h3PathSolenoidalTimeTestMomentumOn244 hH3 a b := by
  exact (h3Path_distributionalMomentum_iff_timeTestMomentum244
    hH3 ha hab hb).mp
    (h3Path_distributionalMomentum_fromH3Admissible244
      hH3 ha hab hb)

/-- The old physical Hilbert FTC defect is zero on each strict interval.
This is a consistency statement on (0,T), not endpoint regularity. -/
theorem h3Path_actualProjectedMomentumFTCDefect_zero_fromH3Admissible244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    h3PathActualProjectedMomentumFTCDefect244 hH3 a b = 0 := by
  by_contra hNonzero
  obtain ⟨s, hs, hFail⟩ :=
    h3Path_nonzeroPhysicalFTCDefect_forces_oldPressureL1Failure244
      hH3 ha hab hb hNonzero
  exact hFail
    (h3Path_interiorOldPressureL1Mass_fromH3Admissible244
      hH3 ⟨lt_trans ha hs.1, lt_trans hs.2 hb⟩)

end
end PrimeTensor.FirstMonomialTriad

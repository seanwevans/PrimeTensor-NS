import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionOldPressureL1Fubini244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.Pressure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Selected.Pressure.Force
import Mathlib.Tactic

/-!
# Old-pressure joint regularity on the selected restart, without new hypotheses

The selected unit-viscosity spectral pressure force is already jointly continuous
on every strict restart slab of admissible length. The physical-evolution result
established via the curl weak-FTC branch identifies that selected pressure force
with the OLD preterminal pressure force on the overlap. Their first spatial
pressure derivatives are consequently jointly continuous on that same slab.

A closed time subinterval strictly inside the slab, multiplied by the compact
spatial support of any weak test coordinate, is a compact cylinder. Continuity
on this cylinder gives a genuine uniform bound for the OLD pressure gradient
there, and hence a compact-test weighted spatial bound.

No global joint continuity for the old pressure on the entire preterminal
cylinder is assumed. This file does not yet assert that the particular elapsed
window in `h3PathInteriorTimeOldPressureL1MassAt244` has been rebased inside
one of these strict selected slabs. That interval bookkeeping is the next step.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3OldPressureSelectedJoint244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

-- The same norm topology for Point3 as the existing weak-test compactness lemmas.
local instance point3NormTopologicalSpaceH3OldPressureSelectedJoint244 :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Old pressure first spatial derivatives are jointly continuous on every
strict selected restart slab. Unlike the earlier joint-continuity reduction,
neither physical evolution nor selected-pressure joint continuity is assumed:
both are supplied by existing theorems of the canonical H3 tail. -/
theorem h3Preterminal_oldPressureJointOnSelectedAbsoluteSlab244
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hτ : 0 < τ)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hRadius : τ ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    H3PreterminalPressureFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
      (t := t) (tau := τ) hNS := by
  have hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail :=
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_tailH3_curl
      hNS ht hE hTail
  have hSelected :
      H3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnAbsoluteSlab
        (tau := τ) hNS ht hE hTail :=
    H3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnAbsoluteSlab_of_le_restartRadius
      hNS ht hE hTail hRadius
  exact
    H3PreterminalPressureFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab_of_selectedPressureForce
      hNS ht hτ hEnd hE hTail hEvolution hRadius hSelected

/-- On every strictly interior *closed* subslab of the selected restart,
the old pressure gradient is uniformly bounded over the spatial support
of any compact weak-test coordinate. The bound can depend on that test and
on the chosen closed subinterval, but not on its time or spatial point. -/
theorem h3Preterminal_oldPressureGradient_compactBound_insideSelectedSlab244
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ a b : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hτ : 0 < τ)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hRadius : τ ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (ha : t < a) (_hab : a ≤ b) (hb : b < t + τ)
    (φ : H3WeakTestVector) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, s ∈ Set.Icc a b →
        ∀ x : Point3, x ∈ tsupport (φ i : Point3 → ℝ) →
          ‖spatial3.d (h3AxisOfFin3 i)
              ((Classical.choose hNS :
                SpaceTimeScalarField ℝ ℝ ℝ Depth.three) s) x‖ ≤ C := by
  have hJoint :=
    h3Preterminal_oldPressureJointOnSelectedAbsoluteSlab244
      hNS ht hτ hEnd hE hTail hRadius
  unfold H3PreterminalPressureFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab at hJoint
  let K : Set (ℝ × Point3) :=
    Set.Icc a b ×ˢ tsupport (φ i : Point3 → ℝ)
  have hSupportCompact :
      IsCompact (tsupport (φ i : Point3 → ℝ)) := by
    unfold point3NormTopologicalSpaceH3OldPressureSelectedJoint244
    exact (φ i).hasCompactSupport
  have hKCompact : IsCompact K := by
    dsimp only [K]
    exact isCompact_Icc.prod hSupportCompact
  have hSubset : K ⊆ (Set.Ioo t (t + τ) ×ˢ Set.univ) := by
    intro z hz
    have hs : z.1 ∈ Set.Icc a b := hz.1
    exact ⟨⟨lt_of_lt_of_le ha hs.1,
      lt_of_le_of_lt hs.2 hb⟩, Set.mem_univ z.2⟩
  have hCont :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          spatial3.d (h3AxisOfFin3 i)
            ((Classical.choose hNS :
              SpaceTimeScalarField ℝ ℝ ℝ Depth.three) z.1) z.2)
        K :=
    (hJoint (h3AxisOfFin3 i)).mono hSubset
  obtain ⟨C, hC⟩ := hKCompact.exists_bound_of_continuousOn hCont
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro s hs x hx
  have hPoint : (s, x) ∈ K := ⟨hs, hx⟩
  exact (hC (s, x) hPoint).trans (le_max_left C 0)

/-- The compact-subslab estimate gives a bound on the exact old-pressure
factor appearing in the scalar absolute-mass integrand, including outside
the test support where the test vanishes. -/
theorem h3Preterminal_oldPressureGradient_testWeightedBound_insideSelectedSlab244
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ a b : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hτ : 0 < τ)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hRadius : τ ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (ha : t < a) (hab : a ≤ b) (hb : b < t + τ)
    (φ : H3WeakTestVector) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, s ∈ Set.Icc a b →
        ∀ x : Point3,
          ‖(ContinuousLinearMap.lsmul ℝ ℝ) (φ i x)
            (spatial3.d (h3AxisOfFin3 i)
              ((Classical.choose hNS :
                SpaceTimeScalarField ℝ ℝ ℝ Depth.three) s) x)‖
            ≤ C * ‖φ i x‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    h3Preterminal_oldPressureGradient_compactBound_insideSelectedSlab244
      hNS ht hτ hEnd hE hTail hRadius ha hab hb φ i
  refine ⟨C, hC0, ?_⟩
  intro s hs x
  by_cases hx : x ∈ tsupport (φ i : Point3 → ℝ)
  · have hGrad := hC s hs x hx
    change ‖φ i x * spatial3.d (h3AxisOfFin3 i)
      ((Classical.choose hNS :
        SpaceTimeScalarField ℝ ℝ ℝ Depth.three) s) x‖ ≤ C * ‖φ i x‖
    rw [norm_mul]
    calc
      ‖φ i x‖ * ‖spatial3.d (h3AxisOfFin3 i)
          ((Classical.choose hNS :
            SpaceTimeScalarField ℝ ℝ ℝ Depth.three) s) x‖
          ≤ ‖φ i x‖ * C :=
        mul_le_mul_of_nonneg_left hGrad (norm_nonneg _)
      _ = C * ‖φ i x‖ := mul_comm _ _
  · have hZero : φ i x = 0 := by
      by_contra hne
      exact hx (subset_tsupport (φ i : Point3 → ℝ) hne)
    simp [hZero]

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureCompactCylinder
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Joint

/-!
# Zeroth endpoint continuity: close compact-cylinder bounds from pressure joint continuity

`TemporalPressureCompactCylinder` reduced the remaining old-pressure mass to
one test-local compact-cylinder estimate.

The repository already has the exact spacetime regularity predicate naturally
suited to that estimate:

    H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous hNS.

For one retained elapsed interval `[0,τ]`, the absolute time interval
`[t,t+τ]` lies compactly inside `(0,T)`.  For each weak-test coordinate `φᵢ`,
the topological support `tsupport φᵢ` is compact.  Therefore joint continuity
of

    (s,x) ↦ ∂ᵢ p_old(s,x)

on `(0,T) × ℝ³` gives a finite bound on

    [t,t+τ] × tsupport φᵢ.

There are only three coordinates, so summing the three nonnegative coordinate
bounds gives one common scalar bound.  Outside `tsupport φᵢ`, the test
vanishes identically.  This is exactly the compact-cylinder predicate from the
previous increment.

Thus the global old-pressure mass frontier is implied by the much more
structural pressure-gradient joint-continuity frontier.  No endpoint
continuity, selected/old overlap, or physical evolution hypothesis is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3ZeroPressureJoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pin `Point3` to the norm topology used by `H3WeakTestFunction`. -/
local instance point3NormTopologicalSpaceH3ZeroPressureJoint :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Joint continuity of the old pressure gradient gives the compact-cylinder
bound required by one fixed weak-test vector. -/
theorem H3PressureWitnessGradientCompactCylinderBoundOnElapsed_of_oldPressureJoint
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hJoint :
      H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous
        hNS) :
    H3PressureWitnessGradientCompactCylinderBoundOnElapsed
      (t := t) (tau := tau)
      (Classical.choose hNS)
      φ := by
  unfold
    H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous
    at hJoint

  dsimp only at hJoint

  have hCoordinateBound :
      ∀ i : Fin 3,
        ∃ C : ℝ,
          0 ≤ C
            ∧
          ∀
            (q : Set.Icc (0 : ℝ) tau)
            (x : Point3),
              x ∈ tsupport (φ i : Point3 → ℝ) →
              ‖spatial3.d
                  (h3AxisOfFin3 i)
                  ((Classical.choose hNS) (t + (q : ℝ)))
                  x‖
                ≤
              C := by
    intro i

    let K : Set (ℝ × Point3) :=
      Set.Icc t (t + tau) ×ˢ
        tsupport (φ i : Point3 → ℝ)

    have hSupportCompact :
        IsCompact
          (tsupport (φ i : Point3 → ℝ)) := by
      unfold point3NormTopologicalSpaceH3ZeroPressureJoint
      exact (φ i).hasCompactSupport

    have hKCompact :
        IsCompact K := by
      dsimp only [K]
      exact isCompact_Icc.prod hSupportCompact

    have hKSubset :
        K ⊆
          (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
      intro z hz

      have hs :
          z.1 ∈ Set.Icc t (t + tau) :=
        hz.1

      refine
        ⟨
          ?_,
          Set.mem_univ z.2
        ⟩

      constructor
      · exact lt_of_lt_of_le ht.1 hs.1
      · exact lt_of_le_of_lt hs.2 hEnd

    have hContinuous :
        ContinuousOn
          (fun z : ℝ × Point3 =>
            spatial3.d
              (h3AxisOfFin3 i)
              ((Classical.choose hNS) z.1)
              z.2)
          K := by
      exact
        (hJoint (h3AxisOfFin3 i)).mono
          hKSubset

    obtain ⟨C, hC⟩ :=
      hKCompact.exists_bound_of_continuousOn
        hContinuous

    refine
      ⟨
        max C 0,
        le_max_right C 0,
        ?_
      ⟩

    intro q x hx

    have hTime :
        t + (q : ℝ) ∈
          Set.Icc t (t + tau) := by
      constructor
      · linarith [q.2.1]
      · linarith [q.2.2]

    have hPoint :
        (t + (q : ℝ), x) ∈ K := by
      exact ⟨hTime, hx⟩

    exact
      (hC (t + (q : ℝ), x) hPoint).trans
        (le_max_left C 0)

  choose C hCNonneg hCBound using hCoordinateBound

  let B : ℝ :=
    ∑ i : Fin 3, C i

  have hB :
      0 ≤ B := by
    dsimp only [B]
    exact
      Finset.sum_nonneg
        (fun i hi => hCNonneg i)

  refine
    ⟨
      B,
      hB,
      ?_
    ⟩

  intro i q x

  by_cases hx :
      x ∈ tsupport (φ i : Point3 → ℝ)

  · have hGrad :
        ‖spatial3.d
            (h3AxisOfFin3 i)
            ((Classical.choose hNS) (t + (q : ℝ)))
            x‖
          ≤
        C i :=
      hCBound i q x hx

    have hCi :
        C i ≤ B := by
      dsimp only [B]

      exact
        Finset.single_le_sum
          (fun j hj => hCNonneg j)
          (Finset.mem_univ i)

    have hGradB :
        ‖spatial3.d
            (h3AxisOfFin3 i)
            ((Classical.choose hNS) (t + (q : ℝ)))
            x‖
          ≤
        B :=
      hGrad.trans hCi

    change
      ‖(φ i x) *
          spatial3.d
            (h3AxisOfFin3 i)
            ((Classical.choose hNS) (t + (q : ℝ)))
            x‖
        ≤
      B * ‖φ i x‖

    rw [norm_mul]

    calc
      ‖φ i x‖ *
          ‖spatial3.d
              (h3AxisOfFin3 i)
              ((Classical.choose hNS) (t + (q : ℝ)))
              x‖
          ≤
        ‖φ i x‖ * B :=
          mul_le_mul_of_nonneg_left
            hGradB
            (norm_nonneg _)
      _ = B * ‖φ i x‖ := by
        ring

  · have hPhiZero :
        φ i x = 0 := by
      by_contra hne
      exact
        hx
          (subset_tsupport
            (φ i : Point3 → ℝ)
            hne)

    simp [hPhiZero]

/-- Pressure-gradient joint continuity closes the old-pressure mass condition
for every divergence-free weak test on one elapsed interval. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed_of_pressureJoint
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hJoint :
      H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous
        hNS) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail := by
  apply
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed_of_compactCylinder
      hNS ht hEnd hTail
      (Classical.choose hNS)
      (Classical.choose_spec hNS)

  intro φ hφ

  exact
    H3PressureWitnessGradientCompactCylinderBoundOnElapsed_of_oldPressureJoint
      hNS ht htau hEnd hTail
      φ hJoint

/-- Global structural pressure regularity frontier replacing the opaque
old-pressure mass frontier. -/
def H3PreterminalPressureFirstSpatialDerivativeJointContinuityFrontier : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T),
      H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous
        hNS

/-- Global pressure-gradient joint continuity closes the entire old-pressure
mass frontier. -/
theorem h3PreterminalTailUnitViscosityZeroOldPressureFrontier_of_pressureJoint
    (hJoint :
      H3PreterminalPressureFirstSpatialDerivativeJointContinuityFrontier) :
    H3PreterminalTailUnitViscosityZeroOldPressureFrontier := by
  intro E hE u T t hNS ht hTail
  intro q hqPos hEnd

  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed_of_pressureJoint
      hNS ht
      hqPos.le
      hEnd
      hTail
      (hJoint u T hNS)

end

end Euclidean
end Bridge
end PrimeTensor

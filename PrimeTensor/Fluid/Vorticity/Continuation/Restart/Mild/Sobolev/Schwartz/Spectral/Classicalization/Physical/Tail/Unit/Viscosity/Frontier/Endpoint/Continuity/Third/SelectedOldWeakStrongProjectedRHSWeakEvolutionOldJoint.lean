import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongProjectedRHSWeakEvolutionLocalDomination
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Joint
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Old temporal joint continuity closes endpoint-independent weak evolution

The previous increment reduced scalar weak evolution to a local domination
condition on the actual old temporal derivative

    (r,x) ↦ ∂ₜu_i(t+r,x).

This file discharges that domination condition from the already-isolated
old-branch spacetime regularity proposition

    H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T.

The point is local and compact.

For each elapsed `s ∈ [0,tau]`, the absolute time `t+s` lies strictly inside
`(0,T)`.  Choose a small closed elapsed slab around `s` whose absolute-time
translate remains inside `(0,T)`.  Joint continuity of the old temporal
derivative on the open preterminal cylinder makes it bounded on

    closed time slab × tsupport(φ_i).

Because `φ_i` has compact support, the bound

    x ↦ C * ‖φ_i(x)‖

is integrable and dominates the compact-tested temporal derivative uniformly
through that elapsed neighborhood.

Thus old temporal joint continuity implies:

* closed-interval local domination for every compact weak test;
* the endpoint-independent projected-RHS weak evolution identity;
* the scalar projected-RHS weak FTC interface.

No endpoint `L²` continuity or temporal product-integrability hypothesis is
used in this bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongProjectedRHSWeakEvolutionOldJoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongProjectedRHSWeakEvolutionOldJoint :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Pin `Point3` to the norm topology used by `TestFunction.tsupport`, exactly
as in the existing temporal-joint-continuity reduction. -/
local instance point3NormTopologicalSpaceH3SelectedOldWeakStrongProjectedRHSWeakEvolutionOldJoint :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Joint spacetime continuity of the actual old temporal derivative gives the
endpoint-independent local domination predicate at every closed elapsed time. -/
theorem H3PreterminalLoggedVelocityWeakTemporalLocalDominationAt_of_oldTemporalDerivativeJointlyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (hOldJoint :
      H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
        u T) :
    H3PreterminalLoggedVelocityWeakTemporalLocalDominationAt
      hNS t s φ := by
  intro i

  let c : ℝ := t + s
  let δ : ℝ :=
    min (c / 2) ((T - c) / 2)

  have hcPos : 0 < c := by
    dsimp only [c]
    linarith [ht.1, hs.1]

  have hcT : c < T := by
    dsimp only [c]
    linarith [hEnd, hs.2]

  have hδLeft : 0 < c / 2 := by
    linarith

  have hδRight : 0 < (T - c) / 2 := by
    linarith

  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hδLeft hδRight

  let a : ℝ := s - δ
  let b : ℝ := s + δ
  let S : Set ℝ := Set.Ioo a b

  have has : a < s := by
    dsimp only [a]
    linarith

  have hsb : s < b := by
    dsimp only [b]
    linarith

  have hS : S ∈ 𝓝 s := by
    dsimp only [S]
    exact Ioo_mem_nhds has hsb

  have hδLeLeft : δ ≤ c / 2 := by
    dsimp only [δ]
    exact min_le_left _ _

  have hδLeRight : δ ≤ (T - c) / 2 := by
    dsimp only [δ]
    exact min_le_right _ _

  have hSAbs :
      ∀ r : ℝ,
        r ∈ S →
        t + r ∈ Set.Ioo (0 : ℝ) T := by
    intro r hr

    have hra : a < r := hr.1
    have hrb : r < b := hr.2

    have hLower : 0 < t + r := by
      dsimp only [a] at hra
      dsimp only [c] at hδLeLeft
      linarith

    have hUpper : t + r < T := by
      dsimp only [b] at hrb
      dsimp only [c] at hδLeRight
      linarith

    exact ⟨hLower, hUpper⟩

  let oldDerivative : ℝ × Point3 → ℝ :=
    fun z =>
      temporal.d
        (fun q : ℝ =>
          loggedVelocityComponent
            u q (h3AxisOfFin3 i) z.2)
        z.1

  let shiftPair : ℝ × Point3 → ℝ × Point3 :=
    fun z => (t + z.1, z.2)

  have hOld :
      ContinuousOn
        oldDerivative
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
    dsimp only [oldDerivative]
    exact hOldJoint i

  have hShift :
      Continuous shiftPair := by
    dsimp only [shiftPair]
    fun_prop

  have hMaps :
      MapsTo
        shiftPair
        (Set.Icc a b ×ˢ
          tsupport (φ i : Point3 → ℝ))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
    intro z hz

    have hzTime :
        z.1 ∈ Set.Icc a b :=
      hz.1

    have hAbs :
        t + z.1 ∈ Set.Ioo (0 : ℝ) T := by
      have hza : a ≤ z.1 := hzTime.1
      have hzb : z.1 ≤ b := hzTime.2

      have hLower : 0 < t + z.1 := by
        dsimp only [a] at hza
        dsimp only [c] at hδLeLeft
        linarith

      have hUpper : t + z.1 < T := by
        dsimp only [b] at hzb
        dsimp only [c] at hδLeRight
        linarith

      exact ⟨hLower, hUpper⟩

    exact ⟨hAbs, Set.mem_univ z.2⟩

  have hShifted :
      ContinuousOn
        (oldDerivative ∘ shiftPair)
        (Set.Icc a b ×ˢ
          tsupport (φ i : Point3 → ℝ)) :=
    hOld.comp hShift.continuousOn hMaps

  have hSupportCompact :
      IsCompact
        (tsupport (φ i : Point3 → ℝ)) := by
    unfold
      point3NormTopologicalSpaceH3SelectedOldWeakStrongProjectedRHSWeakEvolutionOldJoint
    exact
      (φ i).hasCompactSupport

  have hProductCompact :
      IsCompact
        (Set.Icc a b ×ˢ
          tsupport (φ i : Point3 → ℝ)) :=
    isCompact_Icc.prod hSupportCompact

  obtain ⟨C, hC⟩ :=
    hProductCompact.exists_bound_of_continuousOn
      hShifted

  let C0 : ℝ := max C 0

  have hC0 : 0 ≤ C0 := by
    dsimp only [C0]
    exact le_max_right _ _

  let bound : Point3 → ℝ :=
    fun x => C0 * ‖φ i x‖

  have hNormIntegrable :
      Integrable
        (fun x : Point3 => ‖φ i x‖)
        (volume : Measure Point3) := by
    exact
      (φ i).continuous.norm.integrable_of_hasCompactSupport
        (φ i).hasCompactSupport.norm

  have hBoundIntegrable :
      Integrable bound
        (volume : Measure Point3) := by
    dsimp only [bound]
    exact Integrable.const_mul hNormIntegrable C0

  refine
    ⟨
      S,
      hS,
      hSAbs,
      bound,
      hBoundIntegrable,
      ?_
    ⟩

  filter_upwards with x

  intro r hr

  by_cases hx : φ i x = 0

  · change
      ‖(φ i x) *
          temporal.d
            (fun q : ℝ =>
              loggedVelocityComponent
                u q (h3AxisOfFin3 i) x)
            (t + r)‖
        ≤
      bound x

    dsimp only [bound]
    rw [hx]
    norm_num

  · have hxSupport :
        x ∈ tsupport (φ i : Point3 → ℝ) :=
      subset_tsupport _ hx

    have hrClosed :
        r ∈ Set.Icc a b :=
      ⟨hr.1.le, hr.2.le⟩

    have hPoint :
        (r, x) ∈
          Set.Icc a b ×ˢ
            tsupport (φ i : Point3 → ℝ) :=
      ⟨hrClosed, hxSupport⟩

    have hDerivative :
        ‖temporal.d
            (fun q : ℝ =>
              loggedVelocityComponent
                u q (h3AxisOfFin3 i) x)
            (t + r)‖
          ≤
        C0 := by
      have hRaw :=
        hC (r, x) hPoint

      dsimp only [
        oldDerivative,
        shiftPair,
        Function.comp_apply
      ] at hRaw

      exact
        hRaw.trans
          (le_max_left C 0)

    change
      ‖(φ i x) *
          temporal.d
            (fun q : ℝ =>
              loggedVelocityComponent
                u q (h3AxisOfFin3 i) x)
            (t + r)‖
        ≤
      bound x

    dsimp only [bound]

    calc
      ‖(φ i x) *
          temporal.d
            (fun q : ℝ =>
              loggedVelocityComponent
                u q (h3AxisOfFin3 i) x)
            (t + r)‖
          =
        ‖φ i x‖ *
          ‖temporal.d
            (fun q : ℝ =>
              loggedVelocityComponent
                u q (h3AxisOfFin3 i) x)
            (t + r)‖ := by
              exact norm_mul _ _
      _ ≤
        ‖φ i x‖ * C0 :=
          mul_le_mul_of_nonneg_left
            hDerivative
            (norm_nonneg _)
      _ =
        C0 * ‖φ i x‖ := by
          rw [mul_comm]

/-- Old temporal joint continuity gives local domination through the whole
closed elapsed interval. -/
theorem H3PreterminalLoggedVelocityWeakTemporalLocallyDominatedOnElapsed_of_oldTemporalDerivativeJointlyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hOldJoint :
      H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
        u T)
    (φ : H3WeakTestVector) :
    H3PreterminalLoggedVelocityWeakTemporalLocallyDominatedOnElapsed
      hNS t tau φ := by
  intro s hs

  exact
    H3PreterminalLoggedVelocityWeakTemporalLocalDominationAt_of_oldTemporalDerivativeJointlyContinuous
      hNS ht hEnd hs φ hOldJoint

/-- Old temporal joint continuity closes the endpoint-independent weak evolution
identity for every divergence-free compact test. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed_of_oldTemporalDerivativeJointlyContinuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hOldJoint :
      H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
        u T) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed
      hNS ht htau hEnd hTail := by
  apply
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed_of_allLocalDomination
      hNS ht htau hEnd hE hTail

  intro φ hφ

  exact
    H3PreterminalLoggedVelocityWeakTemporalLocallyDominatedOnElapsed_of_oldTemporalDerivativeJointlyContinuous
      hNS ht hEnd hOldJoint φ

/-- Consequently, old temporal joint continuity closes the scalar projected-RHS
weak FTC interface directly. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_oldTemporalDerivativeJointlyContinuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hOldJoint :
      H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
        u T) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
      hNS ht htau hEnd hTail := by
  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_allProjectedRHSWeakEvolution
      hNS ht htau hEnd hE hTail
      (H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed_of_oldTemporalDerivativeJointlyContinuous
        hNS ht htau hEnd hE hTail hOldJoint)

end

end Euclidean
end Bridge
end PrimeTensor

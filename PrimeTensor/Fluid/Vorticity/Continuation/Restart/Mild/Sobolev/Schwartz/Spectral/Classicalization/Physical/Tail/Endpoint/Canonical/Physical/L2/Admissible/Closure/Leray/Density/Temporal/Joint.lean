import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Support
import Mathlib.Analysis.Normed.Group.Bounded
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Old.Temporal.Derivative

/-!
# Classicalization: reduce supportwise temporal bounds to joint continuity

`Temporal.Support` reduced the remaining weak-FTC domination problem to one
supportwise scalar estimate:

    locally in time,
    |∂ₜ Wᵢ(r,x)| ≤ C

for `x` in the compact support of one weak-test coordinate.

The most natural sufficient regularity statement is joint continuity of the
pointwise temporal derivative on a compact time slab times that compact
support.  A continuous real-valued function on that compact product is
uniformly bounded, and the resulting scalar bound is exactly the input required
by `Temporal.Support`.

This file performs only that compactness step.  It deliberately does not infer
joint continuity from separate time and spatial regularity; doing so would be
mathematically invalid without an additional argument.  The next analytic
frontier is therefore the exact joint-continuity statement below.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityTemporalJoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pin `Point3` to its norm-induced topology in this file.

`H3WeakTestFunction` is a Mathlib `TestFunction` over the normed-space
topology.  `Point3` also has a competing product-topology instance.  Without
this local pin, a freshly elaborated `tsupport` can use `Pi.topologicalSpace`,
while `TestFunction.hasCompactSupport` uses the norm-induced topology. -/
local instance point3NormTopologicalSpaceH3PhysicalL2AdmissibleClosureLerayDensityTemporalJoint :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-! ## Joint continuity near one compact weak-test support -/

/-- At one strict elapsed time, each coordinate temporal derivative is jointly
continuous on some compact time slab around that time times the topological
support of the corresponding weak-test coordinate. -/
def H3PreterminalTailCanonicalWeakTemporalDerivativeJointlyContinuousNearSupportAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (φ : H3WeakTestVector) : Prop :=
  ∀ i : Fin 3,
    ∃ a b : ℝ,
      a < s
      ∧
      s < b
      ∧
      Set.Icc a b ⊆ Set.Ioo (0 : ℝ) tau
      ∧
      ContinuousOn
        (fun z : ℝ × Point3 =>
          temporal.d
            (fun q : ℝ =>
              (h3SpectralRealVelocityOfPath
                (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint)
                q z.2).component
                  (h3AxisOfFin3 i))
            z.1)
        (Set.Icc a b ×ˢ
          tsupport (φ i : Point3 → ℝ))

/-! ## Compactness gives the supportwise bound -/

/-- Joint continuity on a compact time slab times compact spatial support
produces the scalar supportwise temporal-derivative bound required by
`Temporal.Support`. -/
theorem H3PreterminalTailCanonicalWeakTemporalDerivativeLocallyBoundedOnSupportAt_of_jointlyContinuousNearSupport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (φ : H3WeakTestVector)
    (hJoint :
      H3PreterminalTailCanonicalWeakTemporalDerivativeJointlyContinuousNearSupportAt
        hNS ht htau hEnd hE hTail hEndpoint s φ) :
    H3PreterminalTailCanonicalWeakTemporalDerivativeLocallyBoundedOnSupportAt
      hNS ht htau hEnd hE hTail hEndpoint s φ := by
  intro i

  rcases hJoint i with
    ⟨a, b, has, hsb, hSlab, hContinuous⟩

  have hSupportCompact :
      IsCompact
        (tsupport (φ i : Point3 → ℝ)) := by
    unfold
      point3NormTopologicalSpaceH3PhysicalL2AdmissibleClosureLerayDensityTemporalJoint

    exact
      (φ i).hasCompactSupport

  have hProductCompact :
      IsCompact
        (Set.Icc a b ×ˢ
          tsupport (φ i : Point3 → ℝ)) :=
    isCompact_Icc.prod hSupportCompact

  obtain ⟨C, hC⟩ :=
    hProductCompact.exists_bound_of_continuousOn
      hContinuous

  refine
    ⟨
      Set.Ioo a b,
      Ioo_mem_nhds has hsb,
      ?_,
      max C 0,
      le_max_right C 0,
      ?_
    ⟩

  · intro r hr
    exact hSlab ⟨hr.1.le, hr.2.le⟩

  · intro x hx
    intro r hr

    have hxTSupport :
        x ∈ tsupport (φ i : Point3 → ℝ) :=
      subset_tsupport _ hx

    have hrClosed :
        r ∈ Set.Icc a b :=
      ⟨hr.1.le, hr.2.le⟩

    have hPoint :
        (r, x) ∈
          Set.Icc a b ×ˢ
            tsupport (φ i : Point3 → ℝ) :=
      ⟨hrClosed, hxTSupport⟩

    exact
      (hC (r, x) hPoint).trans
        (le_max_left C 0)

/-! ## Global joint-continuity frontier -/

/-- Exact joint-continuity frontier sufficient for all divergence-free weak
tests: at every strict elapsed time, every weak-test coordinate admits a
compact time slab on which its pointwise temporal derivative is jointly
continuous with space over the test support. -/
def H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeJointlyContinuousNearSupport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ s : ℝ,
      s ∈ Set.Ioo (0 : ℝ) tau →
      H3PreterminalTailCanonicalWeakTemporalDerivativeJointlyContinuousNearSupportAt
        hNS ht htau hEnd hE hTail hEndpoint s φ

/-- Joint continuity near every compact weak-test support closes the supportwise
bound frontier. -/
theorem H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeLocallyBoundedOnSupport_of_jointlyContinuousNearSupport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hJoint :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeJointlyContinuousNearSupport
        hNS ht htau hEnd hE hTail hEndpoint) :
    H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeLocallyBoundedOnSupport
      hNS ht htau hEnd hE hTail hEndpoint := by
  intro φ hDiv s hs

  exact
    H3PreterminalTailCanonicalWeakTemporalDerivativeLocallyBoundedOnSupportAt_of_jointlyContinuousNearSupport
      hNS ht htau hEnd hE hTail hEndpoint s φ
      (hJoint φ hDiv s hs)

/-- Consequently, joint continuity of the pointwise temporal derivative near
all compact divergence-free weak-test supports is sufficient for the physical
`L²` vector evolution identity. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_temporalDerivativeJointlyContinuousNearSupport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hJoint :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeJointlyContinuousNearSupport
        hNS ht htau hEnd hE hTail hEndpoint) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  apply
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_derivativeLocallyBoundedOnSupport
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeLocallyBoundedOnSupport_of_jointlyContinuousNearSupport
      hNS ht htau hEnd hE hTail hEndpoint hJoint


/-! ## Reduce endpoint joint continuity to an old-branch spacetime regularity field -/

/-- The exact old-branch regularity missing from the current preterminal
package: the ordinary temporal derivative of each logged velocity component is
jointly continuous in absolute time and physical space on the open
preterminal cylinder.

This is intentionally stronger than the existing pointwise-in-space temporal
`C¹` field.  No implication from the old regularity structure is asserted
here. -/
def H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop :=
  ∀ i : Fin 3,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent
              u q (h3AxisOfFin3 i) z.2)
          z.1)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)

/-- Joint continuity of the old preterminal temporal derivative implies the
endpoint joint-continuity condition near the support of one weak test.

The endpoint derivative is already known to equal the shifted old derivative
at every strict elapsed time.  We therefore choose a compact elapsed-time slab
strictly inside `(0,τ)`, compose the old jointly continuous field with the
translation `(r,x) ↦ (t+r,x)`, and rewrite pointwise. -/
theorem H3PreterminalTailCanonicalWeakTemporalDerivativeJointlyContinuousNearSupportAt_of_oldJoint
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hOldJoint :
      H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
        u T)
    (s : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestVector) :
    H3PreterminalTailCanonicalWeakTemporalDerivativeJointlyContinuousNearSupportAt
      hNS ht htau hEnd hE hTail hEndpoint s φ := by
  intro i

  let a : ℝ := s / 2
  let b : ℝ := (s + tau) / 2

  have haPos : 0 < a := by
    dsimp only [a]
    linarith [hs.1]

  have has : a < s := by
    dsimp only [a]
    linarith [hs.1]

  have hsb : s < b := by
    dsimp only [b]
    linarith [hs.2]

  have hbTau : b < tau := by
    dsimp only [b]
    linarith [hs.2]

  have hSlab :
      Set.Icc a b ⊆ Set.Ioo (0 : ℝ) tau := by
    intro r hr
    exact
      ⟨
        lt_of_lt_of_le haPos hr.1,
        lt_of_le_of_lt hr.2 hbTau
      ⟩

  refine ⟨a, b, has, hsb, hSlab, ?_⟩

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

    have hr :
        z.1 ∈ Set.Ioo (0 : ℝ) tau :=
      hSlab hz.1

    refine ⟨?_, Set.mem_univ z.2⟩

    constructor

    · linarith [ht.1, hr.1]

    · linarith [hEnd, hr.2]

  have hShifted :
      ContinuousOn
        (oldDerivative ∘ shiftPair)
        (Set.Icc a b ×ˢ
          tsupport (φ i : Point3 → ℝ)) :=
    hOld.comp hShift.continuousOn hMaps

  apply hShifted.congr

  intro z hz

  have hr :
      z.1 ∈ Set.Ioo (0 : ℝ) tau :=
    hSlab hz.1

  have hEq :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_temporal_d_eq_old
      hNS ht htau hEnd hE hTail hEndpoint
      hr i z.2

  dsimp only [
    oldDerivative,
    shiftPair,
    Function.comp_apply
  ]

  exact hEq

/-- Old-branch joint continuity closes the generatorwise endpoint
joint-continuity frontier for every divergence-free weak test. -/
theorem H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeJointlyContinuousNearSupport_of_oldJoint
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hOldJoint :
      H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
        u T) :
    H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeJointlyContinuousNearSupport
      hNS ht htau hEnd hE hTail hEndpoint := by
  intro φ hDiv s hs

  exact
    H3PreterminalTailCanonicalWeakTemporalDerivativeJointlyContinuousNearSupportAt_of_oldJoint
      hNS ht htau hEnd hE hTail hEndpoint
      hOldJoint s hs φ

/-- Consequently, the physical `L²` vector evolution identity is reduced to
joint spacetime continuity of the old preterminal temporal derivative. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_oldTemporalDerivativeJointlyContinuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hOldJoint :
      H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
        u T) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  apply
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_temporalDerivativeJointlyContinuousNearSupport
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeJointlyContinuousNearSupport_of_oldJoint
      hNS ht htau hEnd hE hTail hEndpoint hOldJoint

end

end Euclidean
end Bridge
end PrimeTensor

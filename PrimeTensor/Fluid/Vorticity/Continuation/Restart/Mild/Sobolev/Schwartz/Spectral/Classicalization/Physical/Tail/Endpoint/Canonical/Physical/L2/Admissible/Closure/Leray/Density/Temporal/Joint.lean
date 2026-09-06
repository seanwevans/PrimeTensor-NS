import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Support
import Mathlib.Analysis.Normed.Group.Bounded

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

end

end Euclidean
end Bridge
end PrimeTensor

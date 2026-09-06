import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Support
import Mathlib.Analysis.Normed.Group.Bounded
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Old.Temporal.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Classical.Overlap

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


/-! ## Reduce old temporal joint continuity to the classical momentum RHS -/

/-- Joint spacetime continuity of the classical preterminal momentum right-hand
side.

The pressure is the witness already carried by
`LoggedPreterminalNavierStokesAdmissible`.  This proposition does not strengthen
or alter the momentum equation itself: it isolates only the regularity needed
to turn that pointwise equation into joint continuity of `∂ₜu`.

Written componentwise, the field is

    -∂ᵢp + Δuᵢ - (u · ∇)uᵢ.

No implication from the existing separated preterminal regularity package is
asserted here. -/
def H3PreterminalMomentumRHSJointlyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  ∀ i : Fin 3,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3 p z.1 z.2 (h3AxisOfFin3 i)
          +
        (PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            z.1 z.2).component
          (h3AxisOfFin3 i)
          -
        (PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            z.1 z.2).component
          (h3AxisOfFin3 i))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)

/-- Joint continuity of the classical momentum RHS implies joint continuity of
the actual preterminal temporal derivative.

The proof uses only the already-assumed pointwise momentum equation:
`∂ₜu + (u·∇)u = -∇p + Δu`. -/
theorem H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous_of_momentumRHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hRHS : H3PreterminalMomentumRHSJointlyContinuous hNS) :
    H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
      u T := by
  intro i

  unfold H3PreterminalMomentumRHSJointlyContinuous at hRHS

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  let rhs : ℝ × Point3 → ℝ :=
    fun z =>
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3 p z.1 z.2 (h3AxisOfFin3 i)
        +
      (PrimeTensor.Bridge.RealFluid.laplacianVector
          spatial3
          (logSpaceTimeVectorField u)
          z.1 z.2).component
        (h3AxisOfFin3 i)
        -
      (PrimeTensor.Bridge.RealFluid.advection
          spatial3
          (logSpaceTimeVectorField u)
          z.1 z.2).component
        (h3AxisOfFin3 i)

  have hContinuous :
      ContinuousOn
        rhs
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
    dsimp only [rhs, p]
    exact hRHS i

  apply hContinuous.congr
  intro z hz

  have hMomentum :=
    hPDE.momentum
      z.1
      hz.1
      z.2
      (h3AxisOfFin3 i)

  change
    temporal.d
        (fun q : ℝ =>
          (logSpaceTimeVectorField u q z.2).component
            (h3AxisOfFin3 i))
        z.1
      =
    rhs z

  change
    temporal.d
          (fun q : ℝ =>
            (logSpaceTimeVectorField u q z.2).component
              (h3AxisOfFin3 i))
          z.1
        +
      (PrimeTensor.Bridge.RealFluid.advection
          spatial3
          (logSpaceTimeVectorField u)
          z.1 z.2).component
        (h3AxisOfFin3 i)
      =
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3 p z.1 z.2 (h3AxisOfFin3 i)
      +
    (PrimeTensor.Bridge.RealFluid.laplacianVector
        spatial3
        (logSpaceTimeVectorField u)
        z.1 z.2).component
      (h3AxisOfFin3 i)
    at hMomentum

  dsimp only [rhs]

  linarith

/-- Therefore continuity of the classical momentum RHS alone closes the whole
weak-FTC / admissible-density chain and yields the physical `L²` vector
evolution identity. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_momentumRHSJointlyContinuous
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
    (hRHS :
      H3PreterminalMomentumRHSJointlyContinuous hNS) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  apply
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_oldTemporalDerivativeJointlyContinuous
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous_of_momentumRHS
      hNS hRHS


/-! ## Split the momentum-RHS frontier into its three classical pieces -/

/-- Joint spacetime continuity of the old preterminal pressure-force component
for every velocity coordinate. -/
def H3PreterminalPressureForceJointlyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  ∀ i : Fin 3,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3 p z.1 z.2 (h3AxisOfFin3 i))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)

/-- Joint spacetime continuity of the old preterminal velocity Laplacian
component for every velocity coordinate. -/
def H3PreterminalLaplacianJointlyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  ∀ i : Fin 3,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        (PrimeTensor.Bridge.RealFluid.laplacianVector
          spatial3
          (logSpaceTimeVectorField u)
          z.1 z.2).component
            (h3AxisOfFin3 i))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)

/-- Joint spacetime continuity of the old preterminal advection component for
every velocity coordinate. -/
def H3PreterminalAdvectionJointlyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  ∀ i : Fin 3,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        (PrimeTensor.Bridge.RealFluid.advection
          spatial3
          (logSpaceTimeVectorField u)
          z.1 z.2).component
            (h3AxisOfFin3 i))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)

/-- The three termwise joint-continuity statements imply joint continuity of
the complete classical momentum right-hand side. -/
theorem H3PreterminalMomentumRHSJointlyContinuous_of_terms
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hPressure :
      H3PreterminalPressureForceJointlyContinuous hNS)
    (hLaplacian :
      H3PreterminalLaplacianJointlyContinuous hNS)
    (hAdvection :
      H3PreterminalAdvectionJointlyContinuous hNS) :
    H3PreterminalMomentumRHSJointlyContinuous hNS := by
  unfold
    H3PreterminalPressureForceJointlyContinuous
    at hPressure

  unfold
    H3PreterminalLaplacianJointlyContinuous
    at hLaplacian

  unfold
    H3PreterminalAdvectionJointlyContinuous
    at hAdvection

  unfold
    H3PreterminalMomentumRHSJointlyContinuous

  dsimp only at hPressure hLaplacian hAdvection ⊢

  intro i

  exact
    ((hPressure i).add
      (hLaplacian i)).sub
      (hAdvection i)

/-- Hence the physical `L²` vector evolution identity follows from exactly the
three classical spacetime-continuity obligations appearing in the momentum
right-hand side. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_momentumTermsJointlyContinuous
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
    (hPressure :
      H3PreterminalPressureForceJointlyContinuous hNS)
    (hLaplacian :
      H3PreterminalLaplacianJointlyContinuous hNS)
    (hAdvection :
      H3PreterminalAdvectionJointlyContinuous hNS) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  apply
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_momentumRHSJointlyContinuous
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    H3PreterminalMomentumRHSJointlyContinuous_of_terms
      hNS hPressure hLaplacian hAdvection


/-! ## Reduce the momentum terms to explicit jointly continuous spatial jets -/

/-- Joint spacetime continuity of each logged velocity component. -/
def H3PreterminalVelocityJointlyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  ∀ j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        loggedVelocityComponent u z.1 j z.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)

/-- Joint spacetime continuity of each first spatial derivative of each logged
velocity component. -/
def H3PreterminalVelocityFirstSpatialDerivativeJointlyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  ∀ a j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d
          a
          (loggedVelocityComponent u z.1 j)
          z.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)

/-- Joint spacetime continuity of each pure second spatial derivative
`∂ₐ² uⱼ`.  These are exactly the second derivatives appearing in the
Laplacian. -/
def H3PreterminalVelocityPureSecondSpatialDerivativeJointlyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  ∀ a j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d
          a
          (spatial3.d
            a
            (loggedVelocityComponent u z.1 j))
          z.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)

/-- Joint spacetime continuity of each first spatial derivative of the old
preterminal pressure witness. -/
def H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  ∀ j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d j (p z.1) z.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)

/-- A jointly continuous pressure first jet gives joint continuity of the
pressure-force term. -/
theorem H3PreterminalPressureForceJointlyContinuous_of_pressureFirstSpatialDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hPressure :
      H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous hNS) :
    H3PreterminalPressureForceJointlyContinuous hNS := by
  unfold
    H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous
    at hPressure

  unfold
    H3PreterminalPressureForceJointlyContinuous

  dsimp only at hPressure ⊢

  intro i

  unfold
    PrimeTensor.Bridge.RealFluid.pressureForceComponent

  exact
    (hPressure (h3AxisOfFin3 i)).neg

/-- Joint continuity of the pure second velocity jets gives joint continuity of
the Laplacian term. -/
theorem H3PreterminalLaplacianJointlyContinuous_of_pureSecondSpatialDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hSecond :
      H3PreterminalVelocityPureSecondSpatialDerivativeJointlyContinuous
        hNS) :
    H3PreterminalLaplacianJointlyContinuous hNS := by
  unfold
    H3PreterminalVelocityPureSecondSpatialDerivativeJointlyContinuous
    at hSecond

  unfold
    H3PreterminalLaplacianJointlyContinuous

  intro i

  change
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d
            xAxis
            (spatial3.d
              xAxis
              (loggedVelocityComponent
                u z.1 (h3AxisOfFin3 i)))
            z.2
          +
        (
          spatial3.d
              yAxis
              (spatial3.d
                yAxis
                (loggedVelocityComponent
                  u z.1 (h3AxisOfFin3 i)))
              z.2
            +
          spatial3.d
              zAxis
              (spatial3.d
                zAxis
                (loggedVelocityComponent
                  u z.1 (h3AxisOfFin3 i)))
              z.2
        ))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)

  exact
    (hSecond
        xAxis
        (h3AxisOfFin3 i)).add
      ((hSecond
          yAxis
          (h3AxisOfFin3 i)).add
        (hSecond
          zAxis
          (h3AxisOfFin3 i)))

/-- Joint continuity of velocity and its first spatial jet gives joint
continuity of the advection term. -/
theorem H3PreterminalAdvectionJointlyContinuous_of_velocity_and_firstSpatialDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hVelocity :
      H3PreterminalVelocityJointlyContinuous hNS)
    (hFirst :
      H3PreterminalVelocityFirstSpatialDerivativeJointlyContinuous hNS) :
    H3PreterminalAdvectionJointlyContinuous hNS := by
  unfold
    H3PreterminalVelocityJointlyContinuous
    at hVelocity

  unfold
    H3PreterminalVelocityFirstSpatialDerivativeJointlyContinuous
    at hFirst

  unfold
    H3PreterminalAdvectionJointlyContinuous

  intro i

  change
    ContinuousOn
      (fun z : ℝ × Point3 =>
        loggedVelocityComponent u z.1 xAxis z.2
            *
          spatial3.d
            xAxis
            (loggedVelocityComponent
              u z.1 (h3AxisOfFin3 i))
            z.2
          +
        (
          loggedVelocityComponent u z.1 yAxis z.2
              *
            spatial3.d
              yAxis
              (loggedVelocityComponent
                u z.1 (h3AxisOfFin3 i))
              z.2
            +
          loggedVelocityComponent u z.1 zAxis z.2
              *
            spatial3.d
              zAxis
              (loggedVelocityComponent
                u z.1 (h3AxisOfFin3 i))
              z.2
        ))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)

  exact
    ((hVelocity xAxis).mul
        (hFirst
          xAxis
          (h3AxisOfFin3 i))).add
      (((hVelocity yAxis).mul
          (hFirst
            yAxis
            (h3AxisOfFin3 i))).add
        ((hVelocity zAxis).mul
          (hFirst
            zAxis
            (h3AxisOfFin3 i))))

/-- The explicit joint spacetime jet regularity needed by the classical
momentum RHS. -/
def H3PreterminalMomentumJetsJointlyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  H3PreterminalVelocityJointlyContinuous hNS
    ∧
  H3PreterminalVelocityFirstSpatialDerivativeJointlyContinuous hNS
    ∧
  H3PreterminalVelocityPureSecondSpatialDerivativeJointlyContinuous hNS
    ∧
  H3PreterminalPressureFirstSpatialDerivativeJointlyContinuous hNS

/-- Explicit joint continuity of the velocity and pressure jets appearing in
the momentum equation closes the complete momentum-RHS continuity frontier. -/
theorem H3PreterminalMomentumRHSJointlyContinuous_of_momentumJets
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hJets :
      H3PreterminalMomentumJetsJointlyContinuous hNS) :
    H3PreterminalMomentumRHSJointlyContinuous hNS := by
  rcases hJets with
    ⟨hVelocity, hFirst, hSecond, hPressure⟩

  apply
    H3PreterminalMomentumRHSJointlyContinuous_of_terms
      hNS

  · exact
      H3PreterminalPressureForceJointlyContinuous_of_pressureFirstSpatialDerivative
        hNS hPressure

  · exact
      H3PreterminalLaplacianJointlyContinuous_of_pureSecondSpatialDerivative
        hNS hSecond

  · exact
      H3PreterminalAdvectionJointlyContinuous_of_velocity_and_firstSpatialDerivative
        hNS hVelocity hFirst

/-- Consequently, the physical `L²` vector evolution identity is reduced to
joint spacetime continuity of exactly the classical velocity/pressure jets
present in the momentum equation. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_momentumJetsJointlyContinuous
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
    (hJets :
      H3PreterminalMomentumJetsJointlyContinuous hNS) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  apply
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_momentumRHSJointlyContinuous
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    H3PreterminalMomentumRHSJointlyContinuous_of_momentumJets
      hNS hJets


/-! ## Localize the momentum-jet frontier to the absolute endpoint slab -/

/-- Joint spacetime continuity of each logged velocity component only on the
absolute-time slab actually used by this endpoint increment. -/
def H3PreterminalVelocityJointlyContinuousOnAbsoluteSlab
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (_hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  ∀ j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        loggedVelocityComponent u z.1 j z.2)
      (Set.Ioo t (t + tau) ×ˢ Set.univ)

/-- Joint spacetime continuity of each first spatial velocity derivative on
the absolute endpoint slab. -/
def H3PreterminalVelocityFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (_hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  ∀ a j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d
          a
          (loggedVelocityComponent u z.1 j)
          z.2)
      (Set.Ioo t (t + tau) ×ˢ Set.univ)

/-- Joint spacetime continuity of each pure second spatial velocity derivative
on the absolute endpoint slab. -/
def H3PreterminalVelocityPureSecondSpatialDerivativeJointlyContinuousOnAbsoluteSlab
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (_hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  ∀ a j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d
          a
          (spatial3.d
            a
            (loggedVelocityComponent u z.1 j))
          z.2)
      (Set.Ioo t (t + tau) ×ˢ Set.univ)

/-- Joint spacetime continuity of each first spatial derivative of the old
pressure witness on the absolute endpoint slab. -/
def H3PreterminalPressureFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  ∀ j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d j (p z.1) z.2)
      (Set.Ioo t (t + tau) ×ˢ Set.univ)

/-- Exact local spacetime jet package needed by the endpoint argument. -/
def H3PreterminalMomentumJetsJointlyContinuousOnAbsoluteSlab
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  H3PreterminalVelocityJointlyContinuousOnAbsoluteSlab
      (t := t) (tau := tau) hNS
    ∧
  H3PreterminalVelocityFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
      (t := t) (tau := tau) hNS
    ∧
  H3PreterminalVelocityPureSecondSpatialDerivativeJointlyContinuousOnAbsoluteSlab
      (t := t) (tau := tau) hNS
    ∧
  H3PreterminalPressureFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
      (t := t) (tau := tau) hNS

/-- Joint continuity of the complete classical momentum RHS, localized to the
absolute endpoint slab `(t,t+τ)`. -/
def H3PreterminalMomentumRHSJointlyContinuousOnAbsoluteSlab
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) : Prop :=
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  ∀ i : Fin 3,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3 p z.1 z.2 (h3AxisOfFin3 i)
          +
        (PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            z.1 z.2).component
          (h3AxisOfFin3 i)
          -
        (PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            z.1 z.2).component
          (h3AxisOfFin3 i))
      (Set.Ioo t (t + tau) ×ˢ Set.univ)

/-- The localized jet package gives localized momentum-RHS continuity. -/
theorem H3PreterminalMomentumRHSJointlyContinuousOnAbsoluteSlab_of_momentumJets
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hJets :
      H3PreterminalMomentumJetsJointlyContinuousOnAbsoluteSlab
        (t := t) (tau := tau) hNS) :
    H3PreterminalMomentumRHSJointlyContinuousOnAbsoluteSlab
      (t := t) (tau := tau) hNS := by
  rcases hJets with
    ⟨hVelocity, hFirst, hSecond, hPressure⟩

  unfold
    H3PreterminalVelocityJointlyContinuousOnAbsoluteSlab
    at hVelocity

  unfold
    H3PreterminalVelocityFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
    at hFirst

  unfold
    H3PreterminalVelocityPureSecondSpatialDerivativeJointlyContinuousOnAbsoluteSlab
    at hSecond

  unfold
    H3PreterminalPressureFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
    at hPressure

  unfold
    H3PreterminalMomentumRHSJointlyContinuousOnAbsoluteSlab

  dsimp only at hPressure ⊢

  intro i

  have hPressureForce :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3
            (Classical.choose hNS)
            z.1 z.2
            (h3AxisOfFin3 i))
        (Set.Ioo t (t + tau) ×ˢ Set.univ) := by
    unfold
      PrimeTensor.Bridge.RealFluid.pressureForceComponent

    exact
      (hPressure (h3AxisOfFin3 i)).neg

  have hLaplacian :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          (PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            z.1 z.2).component
              (h3AxisOfFin3 i))
        (Set.Ioo t (t + tau) ×ˢ Set.univ) := by
    change
      ContinuousOn
        (fun z : ℝ × Point3 =>
          spatial3.d
              xAxis
              (spatial3.d
                xAxis
                (loggedVelocityComponent
                  u z.1 (h3AxisOfFin3 i)))
              z.2
            +
          (
            spatial3.d
                yAxis
                (spatial3.d
                  yAxis
                  (loggedVelocityComponent
                    u z.1 (h3AxisOfFin3 i)))
                z.2
              +
            spatial3.d
                zAxis
                (spatial3.d
                  zAxis
                  (loggedVelocityComponent
                    u z.1 (h3AxisOfFin3 i)))
                z.2
          ))
        (Set.Ioo t (t + tau) ×ˢ Set.univ)

    exact
      (hSecond
          xAxis
          (h3AxisOfFin3 i)).add
        ((hSecond
            yAxis
            (h3AxisOfFin3 i)).add
          (hSecond
            zAxis
            (h3AxisOfFin3 i)))

  have hAdvection :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          (PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            z.1 z.2).component
              (h3AxisOfFin3 i))
        (Set.Ioo t (t + tau) ×ˢ Set.univ) := by
    change
      ContinuousOn
        (fun z : ℝ × Point3 =>
          loggedVelocityComponent u z.1 xAxis z.2
              *
            spatial3.d
              xAxis
              (loggedVelocityComponent
                u z.1 (h3AxisOfFin3 i))
              z.2
            +
          (
            loggedVelocityComponent u z.1 yAxis z.2
                *
              spatial3.d
                yAxis
                (loggedVelocityComponent
                  u z.1 (h3AxisOfFin3 i))
                z.2
              +
            loggedVelocityComponent u z.1 zAxis z.2
                *
              spatial3.d
                zAxis
                (loggedVelocityComponent
                  u z.1 (h3AxisOfFin3 i))
                z.2
          ))
        (Set.Ioo t (t + tau) ×ˢ Set.univ)

    exact
      ((hVelocity xAxis).mul
          (hFirst
            xAxis
            (h3AxisOfFin3 i))).add
        (((hVelocity yAxis).mul
            (hFirst
              yAxis
              (h3AxisOfFin3 i))).add
          ((hVelocity zAxis).mul
            (hFirst
              zAxis
              (h3AxisOfFin3 i))))

  exact
    (hPressureForce.add hLaplacian).sub
      hAdvection

/-- Localized momentum-RHS continuity gives localized joint continuity of the
actual old temporal derivative. -/
theorem H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuousOnAbsoluteSlab_of_momentumRHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hRHS :
      H3PreterminalMomentumRHSJointlyContinuousOnAbsoluteSlab
        (t := t) (tau := tau) hNS) :
    ∀ i : Fin 3,
      ContinuousOn
        (fun z : ℝ × Point3 =>
          temporal.d
            (fun q : ℝ =>
              loggedVelocityComponent
                u q (h3AxisOfFin3 i) z.2)
            z.1)
        (Set.Ioo t (t + tau) ×ˢ Set.univ) := by
  unfold
    H3PreterminalMomentumRHSJointlyContinuousOnAbsoluteSlab
    at hRHS

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  dsimp only at hRHS

  intro i

  let rhs : ℝ × Point3 → ℝ :=
    fun z =>
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3 p z.1 z.2 (h3AxisOfFin3 i)
        +
      (PrimeTensor.Bridge.RealFluid.laplacianVector
          spatial3
          (logSpaceTimeVectorField u)
          z.1 z.2).component
        (h3AxisOfFin3 i)
        -
      (PrimeTensor.Bridge.RealFluid.advection
          spatial3
          (logSpaceTimeVectorField u)
          z.1 z.2).component
        (h3AxisOfFin3 i)

  have hContinuous :
      ContinuousOn
        rhs
        (Set.Ioo t (t + tau) ×ˢ Set.univ) := by
    dsimp only [rhs, p]
    exact hRHS i

  apply hContinuous.congr
  intro z hz

  have hzT :
      z.1 ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · exact lt_trans ht.1 hz.1.1
    · exact lt_trans hz.1.2 hEnd

  have hMomentum :=
    hPDE.momentum
      z.1
      hzT
      z.2
      (h3AxisOfFin3 i)

  change
    temporal.d
        (fun q : ℝ =>
          (logSpaceTimeVectorField u q z.2).component
            (h3AxisOfFin3 i))
        z.1
      =
    rhs z

  change
    temporal.d
          (fun q : ℝ =>
            (logSpaceTimeVectorField u q z.2).component
              (h3AxisOfFin3 i))
          z.1
        +
      (PrimeTensor.Bridge.RealFluid.advection
          spatial3
          (logSpaceTimeVectorField u)
          z.1 z.2).component
        (h3AxisOfFin3 i)
      =
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3 p z.1 z.2 (h3AxisOfFin3 i)
      +
    (PrimeTensor.Bridge.RealFluid.laplacianVector
        spatial3
        (logSpaceTimeVectorField u)
        z.1 z.2).component
      (h3AxisOfFin3 i)
    at hMomentum

  dsimp only [rhs]

  linarith

/-- Only local old temporal-derivative joint continuity on `(t,t+τ)` is needed
to obtain the endpoint joint-continuity condition near one weak-test support. -/
theorem H3PreterminalTailCanonicalWeakTemporalDerivativeJointlyContinuousNearSupportAt_of_oldJointOnAbsoluteSlab
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
      ∀ i : Fin 3,
        ContinuousOn
          (fun z : ℝ × Point3 =>
            temporal.d
              (fun q : ℝ =>
                loggedVelocityComponent
                  u q (h3AxisOfFin3 i) z.2)
              z.1)
          (Set.Ioo t (t + tau) ×ˢ Set.univ))
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
        (Set.Ioo t (t + tau) ×ˢ Set.univ) := by
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
        (Set.Ioo t (t + tau) ×ˢ Set.univ) := by
    intro z hz

    have hr :
        z.1 ∈ Set.Ioo (0 : ℝ) tau :=
      hSlab hz.1

    refine ⟨?_, Set.mem_univ z.2⟩

    constructor <;> linarith [hr.1, hr.2]

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

/-- Localized momentum jets on the single absolute endpoint slab are sufficient
for every divergence-free weak test. -/
theorem H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeJointlyContinuousNearSupport_of_localMomentumJets
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
    (hJets :
      H3PreterminalMomentumJetsJointlyContinuousOnAbsoluteSlab
        (t := t) (tau := tau) hNS) :
    H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeJointlyContinuousNearSupport
      hNS ht htau hEnd hE hTail hEndpoint := by
  have hRHS :
      H3PreterminalMomentumRHSJointlyContinuousOnAbsoluteSlab
        (t := t) (tau := tau) hNS :=
    H3PreterminalMomentumRHSJointlyContinuousOnAbsoluteSlab_of_momentumJets
      hNS hJets

  have hOldJoint :=
    H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuousOnAbsoluteSlab_of_momentumRHS
      hNS ht hEnd hRHS

  intro φ hDiv s hs

  exact
    H3PreterminalTailCanonicalWeakTemporalDerivativeJointlyContinuousNearSupportAt_of_oldJointOnAbsoluteSlab
      hNS ht htau hEnd hE hTail hEndpoint
      hOldJoint s hs φ

/-- Final localized reduction: the physical `L²` vector evolution identity
requires joint spacetime regularity only on `(t,t+τ)`, not globally on `(0,T)`. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_localMomentumJetsJointlyContinuous
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
    (hJets :
      H3PreterminalMomentumJetsJointlyContinuousOnAbsoluteSlab
        (t := t) (tau := tau) hNS) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  apply
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_temporalDerivativeJointlyContinuousNearSupport
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeJointlyContinuousNearSupport_of_localMomentumJets
      hNS ht htau hEnd hE hTail hEndpoint hJets


/-! ## Transfer localized velocity jets from the selected restart -/

/-- Joint spacetime continuity of the selected restart velocity, its first
spatial derivatives, and the pure second derivatives needed by the Laplacian,
restricted to the elapsed slab `(0,τ)`.

This is deliberately only the velocity part of the localized momentum-jet
frontier.  The old pressure gradient remains a separate obligation. -/
def H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  let V :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    fun q =>
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        q
  (∀ j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        (V z.1 z.2).component j)
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ))
    ∧
  (∀ a j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d
          a
          (fun y : Point3 =>
            (V z.1 y).component j)
          z.2)
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ))
    ∧
  (∀ a j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d
          a
          (spatial3.d
            a
            (fun y : Point3 =>
              (V z.1 y).component j))
          z.2)
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ))

/-- The exact selected/old overlap equality transfers joint continuity of all
velocity jets needed by the momentum equation from elapsed time `(0,τ)` to
absolute time `(t,t+τ)`.

No differentiation of the overlap identity in time is used.  At each fixed
time the selected and old *spatial fields* are equal, so first and second
spatial derivatives transport by congruence. -/
theorem H3PreterminalVelocityJetsJointlyContinuousOnAbsoluteSlab_of_selectedRestart
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail)
    (hTauR :
      tau ≤ h3FinHeatLerayRestartRadius ν E)
    (hSelected :
      H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed
        (tau := tau)
        hν hNS ht hE hTail) :
    H3PreterminalVelocityJointlyContinuousOnAbsoluteSlab
        (t := t) (tau := tau) hNS
      ∧
    H3PreterminalVelocityFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
        (t := t) (tau := tau) hNS
      ∧
    H3PreterminalVelocityPureSecondSpatialDerivativeJointlyContinuousOnAbsoluteSlab
        (t := t) (tau := tau) hNS := by
  unfold
    H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed
    at hSelected

  dsimp only at hSelected

  rcases hSelected with
    ⟨hValueSelected, hFirstSelected, hSecondSelected⟩

  let V :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    fun q =>
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        q

  let shiftBack : ℝ × Point3 → ℝ × Point3 :=
    fun z => (z.1 - t, z.2)

  have hShiftBack :
      Continuous shiftBack := by
    dsimp only [shiftBack]
    fun_prop

  have hMaps :
      MapsTo
        shiftBack
        (Set.Ioo t (t + tau) ×ˢ Set.univ)
        (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
    intro z hz
    exact
      ⟨
        ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
        Set.mem_univ z.2
      ⟩

  have hFieldEq
      (s : ℝ)
      (hs : s ∈ Set.Ioo t (t + tau)) :
      V (s - t)
        =
      logSpaceTimeVectorField u s := by
    let q :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν E) :=
      ⟨
        s - t,
        by linarith [hs.1],
        le_trans (by linarith [hs.2]) hTauR
      ⟩

    have hqPos : 0 < (q : ℝ) := by
      dsimp only [q]
      linarith [hs.1]

    have hBefore :
        t + (q : ℝ) < T := by
      dsimp only [q]
      linarith [hs.2, hEnd]

    have hEq :=
      h3PreterminalTailCanonicalSelectedRestart_eq_old_on_positiveOverlap
        hν hNS ht hE hTail hEvolution
        q hqPos hBefore

    have hTime :
        t + (q : ℝ) = s := by
      dsimp only [q]
      ring

    rw [hTime] at hEq

    simpa only [V, q] using hEq

  constructor

  · unfold
      H3PreterminalVelocityJointlyContinuousOnAbsoluteSlab

    intro j

    have hComp :
        ContinuousOn
          ((fun z : ℝ × Point3 =>
              (V z.1 z.2).component j) ∘ shiftBack)
          (Set.Ioo t (t + tau) ×ˢ Set.univ) :=
      (hValueSelected j).comp
        hShiftBack.continuousOn
        hMaps

    apply hComp.congr
    intro z hz

    have hEq := hFieldEq z.1 hz.1

    have hPoint :
        (V (z.1 - t) z.2).component j
          =
        (logSpaceTimeVectorField u z.1 z.2).component j := by
      exact
        congrArg
          (fun f : VectorField3 => (f z.2).component j)
          hEq

    dsimp only [Function.comp_apply, shiftBack, V]

    unfold loggedVelocityComponent

    exact hPoint.symm

  constructor

  · unfold
      H3PreterminalVelocityFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab

    intro a j

    have hComp :
        ContinuousOn
          ((fun z : ℝ × Point3 =>
              spatial3.d
                a
                (fun y : Point3 =>
                  (V z.1 y).component j)
                z.2) ∘ shiftBack)
          (Set.Ioo t (t + tau) ×ˢ Set.univ) :=
      (hFirstSelected a j).comp
        hShiftBack.continuousOn
        hMaps

    apply hComp.congr
    intro z hz

    have hEq := hFieldEq z.1 hz.1

    have hScalar :
        (fun y : Point3 =>
          (V (z.1 - t) y).component j)
          =
        loggedVelocityComponent u z.1 j := by
      funext y

      have hPoint :
          (V (z.1 - t) y).component j
            =
          (logSpaceTimeVectorField u z.1 y).component j := by
        exact
          congrArg
            (fun f : VectorField3 => (f y).component j)
            hEq

      unfold loggedVelocityComponent
      exact hPoint

    have hDerivative :=
      congrArg
        (fun f : ScalarField3 =>
          spatial3.d a f z.2)
        hScalar

    dsimp only [Function.comp_apply, shiftBack]

    exact hDerivative.symm

  · unfold
      H3PreterminalVelocityPureSecondSpatialDerivativeJointlyContinuousOnAbsoluteSlab

    intro a j

    have hComp :
        ContinuousOn
          ((fun z : ℝ × Point3 =>
              spatial3.d
                a
                (spatial3.d
                  a
                  (fun y : Point3 =>
                    (V z.1 y).component j))
                z.2) ∘ shiftBack)
          (Set.Ioo t (t + tau) ×ˢ Set.univ) :=
      (hSecondSelected a j).comp
        hShiftBack.continuousOn
        hMaps

    apply hComp.congr
    intro z hz

    have hEq := hFieldEq z.1 hz.1

    have hScalar :
        (fun y : Point3 =>
          (V (z.1 - t) y).component j)
          =
        loggedVelocityComponent u z.1 j := by
      funext y

      have hPoint :
          (V (z.1 - t) y).component j
            =
          (logSpaceTimeVectorField u z.1 y).component j := by
        exact
          congrArg
            (fun f : VectorField3 => (f y).component j)
            hEq

      unfold loggedVelocityComponent
      exact hPoint

    have hDerivative :=
      congrArg
        (fun f : ScalarField3 =>
          spatial3.d a (spatial3.d a f) z.2)
        hScalar

    dsimp only [Function.comp_apply, shiftBack]

    exact hDerivative.symm

/-- After the velocity jets are transported from the selected restart, only
joint continuity of the old pressure first derivative remains from the
localized momentum-jet package. -/
theorem H3PreterminalMomentumJetsJointlyContinuousOnAbsoluteSlab_of_selectedVelocityJets_and_pressure
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail)
    (hTauR :
      tau ≤ h3FinHeatLerayRestartRadius ν E)
    (hSelected :
      H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed
        (tau := tau)
        hν hNS ht hE hTail)
    (hPressure :
      H3PreterminalPressureFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
        (t := t) (tau := tau) hNS) :
    H3PreterminalMomentumJetsJointlyContinuousOnAbsoluteSlab
      (t := t) (tau := tau) hNS := by
  obtain
    ⟨hVelocity, hFirst, hSecond⟩ :=
      H3PreterminalVelocityJetsJointlyContinuousOnAbsoluteSlab_of_selectedRestart
        hν hNS ht htau hEnd hE hTail
        hEvolution hTauR hSelected

  exact
    ⟨hVelocity, hFirst, hSecond, hPressure⟩

/-- Selected-restart velocity-jet continuity plus the remaining old pressure
gradient continuity closes the physical `L²` vector evolution identity. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_selectedVelocityJets_and_pressure
    {ν E : ℝ}
    (hν : 0 < ν)
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
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail)
    (hTauR :
      tau ≤ h3FinHeatLerayRestartRadius ν E)
    (hSelected :
      H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed
        (tau := tau)
        hν hNS ht hE hTail)
    (hPressure :
      H3PreterminalPressureFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab
        (t := t) (tau := tau) hNS) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  apply
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_localMomentumJetsJointlyContinuous
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    H3PreterminalMomentumJetsJointlyContinuousOnAbsoluteSlab_of_selectedVelocityJets_and_pressure
      hν hNS ht htau hEnd hE hTail
      hEvolution hTauR hSelected hPressure

end

end Euclidean
end Bridge
end PrimeTensor

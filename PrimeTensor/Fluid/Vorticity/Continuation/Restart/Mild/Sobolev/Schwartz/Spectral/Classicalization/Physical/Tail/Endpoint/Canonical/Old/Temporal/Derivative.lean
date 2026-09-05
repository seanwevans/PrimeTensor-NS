import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Old.Diffusion
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Classicalization: endpoint temporal derivative is the old temporal derivative

The endpoint canonical normalized real path is already known to reconstruct the
old logged velocity pointwise on every physical elapsed slice `s ∈ [0,τ]`.

This file upgrades that slice-by-slice equality to a genuine local temporal
derivative statement on the strict elapsed interval `(0,τ)`.

Fix a spatial point and one finite velocity coordinate.  Near any
`s ∈ (0,τ)`:

* the endpoint reconstructed component equals the shifted old component
  `r ↦ u(t+r)`;
* the old preterminal regularity package gives `C¹` time regularity of
  `q ↦ u(q)`;
* composing its `HasDerivAt` at absolute time `t+s` with the affine map
  `r ↦ t+r` gives the derivative of the shifted old component;
* `HasDerivAt.congr_of_eventuallyEq` transports that derivative through the
  local endpoint/old equality.

Thus the reconstructed endpoint component has a genuine ordinary derivative,
with coefficient exactly the old preterminal temporal derivative at absolute
time `t+s`.

This is intentionally a pointwise-in-space scalar theorem.  It does not claim
that the raw Fourier `L²` path is differentiable as a Banach-space-valued map.
That quotient-safe evolution step remains separate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalOldTemporalDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every strict physical elapsed time, one endpoint reconstructed velocity
component has a genuine ordinary derivative equal to the old preterminal
temporal derivative at the corresponding absolute time. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_hasDerivAt_old
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
    {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    HasDerivAt
      (fun r : ℝ =>
        (h3SpectralRealVelocityOfPath W r x).component
          (h3AxisOfFin3 i))
      (temporal.d
        (fun q : ℝ =>
          loggedVelocityComponent
            u q (h3AxisOfFin3 i) x)
        (t + s))
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let fOld : ℝ → ℝ :=
    fun q : ℝ =>
      loggedVelocityComponent
        u q (h3AxisOfFin3 i) x

  have hsClosed :
      s ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hs.1.le, hs.2.le⟩

  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd ⟨s, hsClosed⟩

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  have hOldC1 :
      ContDiffOn
        ℝ 1
        fOld
        (Set.Ioo (0 : ℝ) T) := by
    dsimp only [fOld]
    simpa only [loggedVelocityComponent] using
      hPDE.regularity.velocity_temporal_one
        x (h3AxisOfFin3 i)

  have hOldCriterion :
      ContDiffOn
          ℝ 1
          fOld
          (Set.Ioo (0 : ℝ) T)
        ↔
      DifferentiableOn
          ℝ
          fOld
          (Set.Ioo (0 : ℝ) T)
        ∧
      ContinuousOn
          (deriv fOld)
          (Set.Ioo (0 : ℝ) T) := by
    simpa using
      (contDiffOn_succ_iff_deriv_of_isOpen
        (𝕜 := ℝ)
        (f := fOld)
        (s := Set.Ioo (0 : ℝ) T)
        (n := 0)
        isOpen_Ioo)

  have hOldDiffWithin :
      DifferentiableWithinAt
        ℝ fOld (Set.Ioo (0 : ℝ) T) (t + s) :=
    (hOldCriterion.1 hOldC1).1
      (t + s) hAbs

  have hOldDiff :
      DifferentiableAt ℝ fOld (t + s) :=
    hOldDiffWithin.differentiableAt
      (isOpen_Ioo.mem_nhds hAbs)

  have hOldHas :
      HasDerivAt
        fOld
        (deriv fOld (t + s))
        (t + s) :=
    hOldDiff.hasDerivAt

  have hShift :
      HasDerivAt
        (fun r : ℝ => t + r)
        1
        s := by
    simpa using
      (hasDerivAt_id s).const_add t

  have hShiftedOld :
      HasDerivAt
        (fun r : ℝ => fOld (t + r))
        (deriv fOld (t + s))
        s := by
    have hComp :=
      hOldHas.comp s hShift

    simpa only [
      Function.comp_def,
      mul_one
    ] using hComp

  have hNeighborhood :
      Set.Ioo (0 : ℝ) tau ∈ 𝓝 s :=
    Ioo_mem_nhds hs.1 hs.2

  have hEventuallyEq :
      (fun r : ℝ =>
        (h3SpectralRealVelocityOfPath W r x).component
          (h3AxisOfFin3 i))
        =ᶠ[𝓝 s]
      (fun r : ℝ => fOld (t + r)) := by
    filter_upwards [hNeighborhood] with r hr

    have hrClosed :
        r ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hr.1.le, hr.2.le⟩

    have hPoint :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_apply_eq_old
        hNS ht htau hEnd hE hTail hEndpoint
        r hrClosed i x

    simpa only [W, fOld] using hPoint

  have hEndpointHas :
      HasDerivAt
        (fun r : ℝ =>
          (h3SpectralRealVelocityOfPath W r x).component
            (h3AxisOfFin3 i))
        (deriv fOld (t + s))
        s :=
    hShiftedOld.congr_of_eventuallyEq
      hEventuallyEq

  change
    HasDerivAt
      (fun r : ℝ =>
        (h3SpectralRealVelocityOfPath W r x).component
          (h3AxisOfFin3 i))
      (deriv
        (fun q : ℝ =>
          loggedVelocityComponent
            u q (h3AxisOfFin3 i) x)
        (t + s))
      s

  simpa only [fOld] using hEndpointHas

/-- Equality form of the preceding `HasDerivAt`: the endpoint representative's
relative-time derivative is exactly the old absolute-time derivative. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_temporal_d_eq_old
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
    {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    temporal.d
        (fun r : ℝ =>
          (h3SpectralRealVelocityOfPath W r x).component
            (h3AxisOfFin3 i))
        s
      =
    temporal.d
        (fun q : ℝ =>
          loggedVelocityComponent
            u q (h3AxisOfFin3 i) x)
        (t + s) := by
  dsimp only

  have h :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_hasDerivAt_old
      hNS ht htau hEnd hE hTail hEndpoint hs i x

  change
    deriv
        (fun r : ℝ =>
          (h3SpectralRealVelocityOfPath
            (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
              hNS ht htau.le hEnd hE hTail hEndpoint)
            r x).component
              (h3AxisOfFin3 i))
        s
      =
    deriv
        (fun q : ℝ =>
          loggedVelocityComponent
            u q (h3AxisOfFin3 i) x)
        (t + s)

  exact h.deriv

end

end Euclidean
end Bridge
end PrimeTensor

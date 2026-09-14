import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Increment
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Old.Temporal.Derivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Zeroth-order endpoint continuity: endpoint-independent old-branch FTC

The zeroth-order continuation branch has been reduced to a two-time Fourier
increment estimate.  The first genuinely PDE-side ingredient of that estimate
is already contained in the old preterminal regularity itself and does not
require any endpoint-continuity hypothesis.

For one physical point and one velocity coordinate, the logged preterminal
velocity is `C¹` in absolute time on `(0,T)`.  Hence its shifted elapsed-time
representative

    s ↦ u(t+s,x)

satisfies ordinary scalar FTC on every ordered subinterval of `[0,tau]`:

    ∫_q^r ∂ₜu(t+s,x) ds
      = u(t+r,x) - u(t+q,x).

This file records that statement directly on the old branch.  In particular it
does not pass through the endpoint reconstructed path, the selected restart, or
the endpoint `L²` continuity frontier.

The next step can therefore work snapshot-by-snapshot on the old temporal
derivative and identify its divergence-free Fourier `L²` class with the
already-bounded unit-viscosity projected RHS.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldPointwiseFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Endpoint-independent scalar FTC for one old preterminal velocity component
on an ordered elapsed-time subinterval.

Only the `C¹` temporal regularity already contained in
`LoggedPreterminalNavierStokesAdmissible` is used. -/
theorem h3PreterminalLoggedVelocityComponent_intervalIntegral_temporalDerivative_between
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q r : Set.Icc (0 : ℝ) tau)
    (hqr : (q : ℝ) ≤ (r : ℝ))
    (i : Fin 3)
    (x : Point3) :
    (∫ s in (q : ℝ)..(r : ℝ),
      temporal.d
        (fun a : ℝ =>
          loggedVelocityComponent
            u a (h3AxisOfFin3 i) x)
        (t + s))
      =
    loggedVelocityComponent
        u (t + (r : ℝ)) (h3AxisOfFin3 i) x
      -
    loggedVelocityComponent
        u (t + (q : ℝ)) (h3AxisOfFin3 i) x := by
  let fOld : ℝ → ℝ :=
    fun a : ℝ =>
      loggedVelocityComponent
        u a (h3AxisOfFin3 i) x

  let F : ℝ → ℝ :=
    fun s : ℝ =>
      fOld (t + s)

  let G : ℝ → ℝ :=
    fun s : ℝ =>
      temporal.d fOld (t + s)

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

  have hOldDiffOn :
      DifferentiableOn
        ℝ
        fOld
        (Set.Ioo (0 : ℝ) T) :=
    (hOldCriterion.1 hOldC1).1

  have hOldDerivContinuous :
      ContinuousOn
        (deriv fOld)
        (Set.Ioo (0 : ℝ) T) :=
    (hOldCriterion.1 hOldC1).2

  have hMaps :
      MapsTo
        (fun s : ℝ => t + s)
        (Set.Icc (q : ℝ) (r : ℝ))
        (Set.Ioo (0 : ℝ) T) := by
    intro s hs
    constructor
    · linarith [ht.1, q.property.1, hs.1]
    · have hsTau : s ≤ tau :=
        hs.2.trans r.property.2
      linarith [hEnd, hsTau]

  have hFContinuous :
      ContinuousOn
        F
        (Set.Icc (q : ℝ) (r : ℝ)) := by
    dsimp only [F]
    exact
      hOldC1.continuousOn.comp
        (continuous_const.add continuous_id).continuousOn
        hMaps

  have hGContinuous :
      ContinuousOn
        G
        (Set.Icc (q : ℝ) (r : ℝ)) := by
    change
      ContinuousOn
        (fun s : ℝ => deriv fOld (t + s))
        (Set.Icc (q : ℝ) (r : ℝ))

    exact
      hOldDerivContinuous.comp
        (continuous_const.add continuous_id).continuousOn
        hMaps

  have hGIntegrable :
      IntervalIntegrable
        G
        volume
        (q : ℝ)
        (r : ℝ) := by
    exact
      hGContinuous.intervalIntegrable_of_Icc
        hqr

  have hFDeriv :
      ∀ s : ℝ,
        s ∈ Set.Ioo (q : ℝ) (r : ℝ) →
        HasDerivAt F (G s) s := by
    intro s hs

    have hsClosed :
        s ∈ Set.Icc (q : ℝ) (r : ℝ) :=
      ⟨hs.1.le, hs.2.le⟩

    have hAbs :
        t + s ∈ Set.Ioo (0 : ℝ) T :=
      hMaps hsClosed

    have hOldDiffWithin :
        DifferentiableWithinAt
          ℝ
          fOld
          (Set.Ioo (0 : ℝ) T)
          (t + s) :=
      hOldDiffOn (t + s) hAbs

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
          (fun a : ℝ => t + a)
          1
          s := by
      simpa using
        (hasDerivAt_id s).const_add t

    have hComp :=
      hOldHas.comp s hShift

    change
      HasDerivAt
        (fun a : ℝ => fOld (t + a))
        (deriv fOld (t + s))
        s

    simpa only [
      Function.comp_def,
      mul_one
    ] using hComp

  have hFTC :
      (∫ s in (q : ℝ)..(r : ℝ), G s)
        =
      F (r : ℝ) - F (q : ℝ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hqr
      hFContinuous
      hFDeriv
      hGIntegrable

  simpa only [F, G, fOld] using hFTC

end

end Euclidean
end Bridge
end PrimeTensor

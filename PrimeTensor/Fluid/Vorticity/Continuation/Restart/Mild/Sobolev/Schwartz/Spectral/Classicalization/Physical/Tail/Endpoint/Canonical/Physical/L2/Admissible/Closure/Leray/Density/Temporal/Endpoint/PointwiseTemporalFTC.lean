import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Old.Temporal.Derivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Physical L² temporal admissibility: pointwise temporal FTC without spatial domination

The old weak-FTC route differentiated the compactly tested spatial integral
directly and therefore introduced the strong pointwise spatial-majorant
predicate

`H3PreterminalTailCanonicalWeakTemporalLocallyDominated`.

That predicate is stronger than the regularity naturally supplied by the H³
endpoint path: the Laplacian contribution is controlled in `L²`, not by a
common pointwise spatial supremum.

A better order of operations is available.

For each fixed physical point `x` and velocity coordinate `i`, the old
preterminal regularity package already gives genuine `C¹` time regularity of

    q ↦ loggedVelocityComponent u q i x

on `(0,T)`.  The normalized endpoint representative agrees pointwise with the
shifted old velocity on the whole closed elapsed interval `[0,tau]`.

Therefore, for every intermediate `q ∈ [0,tau]`, ordinary scalar FTC may be
applied in the **time variable first**:

    W_i(q,x) - W_i(0,x)
      =
    ∫₀^q ∂ₜ W_i(r,x) dr.

No spatial differentiation under an integral and no spatial majorant are used.

This is the first checkpoint in the replacement route.  The next step can
multiply this identity by a compact weak test and interchange the resulting
time/space integrals using the already-available physical `L²` control.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointPointwiseTemporalFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pointwise scalar FTC for one endpoint velocity coordinate, at every
intermediate elapsed target.

The time derivative is the endpoint representative's actual ordinary temporal
derivative.  The proof first integrates the shifted old `C¹` derivative and
then uses the already-proved endpoint/old derivative equality on the open
elapsed interval. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_intervalIntegral_temporalDerivative_to
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    (∫ r in (0 : ℝ)..q,
      temporal.d
        (fun s : ℝ =>
          (h3SpectralRealVelocityOfPath W s x).component
            (h3AxisOfFin3 i))
        r)
      =
    (h3SpectralRealVelocityOfPath W q x).component
        (h3AxisOfFin3 i)
      -
    (h3SpectralRealVelocityOfPath W 0 x).component
        (h3AxisOfFin3 i) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let F : ℝ → ℝ :=
    fun r =>
      (h3SpectralRealVelocityOfPath W r x).component
        (h3AxisOfFin3 i)

  let fOld : ℝ → ℝ :=
    fun s =>
      loggedVelocityComponent
        u s (h3AxisOfFin3 i) x

  let GOld : ℝ → ℝ :=
    fun r =>
      temporal.d fOld (t + r)

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

  have hOldDerivContinuous :
      ContinuousOn
        (deriv fOld)
        (Set.Ioo (0 : ℝ) T) :=
    (hOldCriterion.1 hOldC1).2

  have hMaps :
      MapsTo
        (fun r : ℝ => t + r)
        (Set.Icc (0 : ℝ) q)
        (Set.Ioo (0 : ℝ) T) := by
    intro r hr
    constructor
    · linarith [ht.1, hr.1]
    · have hrTau : r ≤ tau :=
        hr.2.trans (hq.2)
      linarith [hEnd, hrTau]

  have hShiftContinuous :
      ContinuousOn
        (fun r : ℝ => fOld (t + r))
        (Set.Icc (0 : ℝ) q) := by
    exact
      hOldC1.continuousOn.comp
        (continuous_const.add continuous_id).continuousOn
        hMaps

  have hFContinuous :
      ContinuousOn
        F
        (Set.Icc (0 : ℝ) q) := by
    apply hShiftContinuous.congr
    intro r hr

    have hrTau :
        r ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hr.1, hr.2.trans hq.2⟩

    have hPoint :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_apply_eq_old
        hNS ht htau hEnd hE hTail hEndpoint
        r hrTau i x

    dsimp only [F, W, fOld]
    exact hPoint

  have hGOldContinuous :
      ContinuousOn
        GOld
        (Set.Icc (0 : ℝ) q) := by
    change
      ContinuousOn
        (fun r : ℝ => deriv fOld (t + r))
        (Set.Icc (0 : ℝ) q)

    exact
      hOldDerivContinuous.comp
        (continuous_const.add continuous_id).continuousOn
        hMaps

  have hGOldIntegrable :
      IntervalIntegrable
        GOld
        volume
        (0 : ℝ)
        q := by
    exact
      hGOldContinuous.intervalIntegrable_of_Icc
        hq.1

  have hFDeriv :
      ∀ r : ℝ,
        r ∈ Set.Ioo (0 : ℝ) q →
        HasDerivAt F (GOld r) r := by
    intro r hr

    have hrTau :
        r ∈ Set.Ioo (0 : ℝ) tau :=
      ⟨hr.1, hr.2.trans_le hq.2⟩

    have h :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_hasDerivAt_old
        hNS ht htau hEnd hE hTail hEndpoint
        hrTau i x

    dsimp only [F, GOld, W, fOld]
    exact h

  have hFTC :
      (∫ r in (0 : ℝ)..q, GOld r)
        =
      F q - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hq.1
      hFContinuous
      hFDeriv
      hGOldIntegrable

  have hIntegralEq :
      (∫ r in (0 : ℝ)..q,
        temporal.d
          (fun s : ℝ =>
            (h3SpectralRealVelocityOfPath W s x).component
              (h3AxisOfFin3 i))
          r)
        =
      ∫ r in (0 : ℝ)..q,
        GOld r := by
    apply
      intervalIntegral.integral_congr_Ioo_of_le
        hq.1

    intro r hr

    have hrTau :
        r ∈ Set.Ioo (0 : ℝ) tau :=
      ⟨hr.1, hr.2.trans_le hq.2⟩

    have hEq :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_temporal_d_eq_old
        hNS ht htau hEnd hE hTail hEndpoint
        hrTau i x

    dsimp only [GOld, fOld]
    exact hEq

  calc
    (∫ r in (0 : ℝ)..q,
      temporal.d
        (fun s : ℝ =>
          (h3SpectralRealVelocityOfPath W s x).component
            (h3AxisOfFin3 i))
        r)
        =
      ∫ r in (0 : ℝ)..q,
        GOld r :=
      hIntegralEq
    _ =
      F q - F 0 :=
      hFTC
    _ =
      (h3SpectralRealVelocityOfPath W q x).component
          (h3AxisOfFin3 i)
        -
      (h3SpectralRealVelocityOfPath W 0 x).component
          (h3AxisOfFin3 i) := by
        rfl

end

end Euclidean
end Bridge
end PrimeTensor

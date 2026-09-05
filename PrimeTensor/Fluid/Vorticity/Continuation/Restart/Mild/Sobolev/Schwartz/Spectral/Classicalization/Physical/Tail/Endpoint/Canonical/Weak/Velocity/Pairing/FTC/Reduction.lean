import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Projected.RHS.Pairing.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Old.Temporal.Derivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Classicalization: reduce weak velocity-pairing FTC to local temporal domination

The preceding files have now closed all algebraic and topological pieces of the
weak projected evolution:

* the compactly tested velocity pairing is continuous on the closed elapsed
  interval;
* the compactly tested pointwise temporal derivative is integrable at each
  strict interior elapsed time;
* its value equals a continuous weak projected RHS pairing;
* that continuous scalar RHS pairing is exactly the pairing with the packaged
  quotient-safe physical `L²` RHS.

What is *not* supplied by `PreterminalVorticityRegularity3` is joint spacetime
continuity of the pointwise temporal derivative.  Therefore differentiation
under the spatial integral cannot honestly be justified by silently invoking a
compact-spacetime supremum bound.

This file isolates the exact missing analytic condition instead.

For one divergence-free compact test vector `φ`, at one strict elapsed time
`s`, require a neighborhood `S ∈ 𝓝 s` and, coordinatewise, an integrable spatial
majorant for

    x ↦ φᵢ(x) ∂ₜWᵢ(r,x)

uniformly for `r ∈ S`.

Under precisely this local domination condition, Mathlib's pinned
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` theorem applies.  The
pointwise `HasDerivAt` input is *already* available from
`PhysicalTailEndpointCanonicalOldTemporalDerivative`, so domination is the only
new hypothesis.

We then prove:

    d/ds <φ,W(s)> = weakProjectedRHSφ(s)

at every strict interior elapsed time, and, if the local domination condition
holds at every strict elapsed time,

    ∫₀^τ weakProjectedRHSφ(s) ds
      = <φ,W(τ)> - <φ,W(0)>.

Thus the remaining weak time-evolution frontier is reduced to one explicit
local-integrable-domination statement.  No joint spacetime regularity, fixed
Fourier mode evaluation, or Banach-valued temporal derivative is assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakVelocityPairingFTCReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakVelocityPairingFTCReduction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- One compact-test velocity coordinate pairing, defined on the ambient real
elapsed-time line. -/
noncomputable def h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal
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
    (φ : H3WeakTestFunction)
    (i : Fin 3)
    (s : ℝ) :
    ℝ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint
  ∫ x : Point3,
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ x)
      ((h3SpectralRealVelocityOfPath W s x).component
        (h3AxisOfFin3 i))
    ∂volume

/-- Complete compact-test velocity pairing on the ambient real elapsed-time
line. -/
noncomputable def h3PreterminalTailCanonicalWeakVelocityPairingReal
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
    (φ : H3WeakTestVector)
    (s : ℝ) :
    ℝ :=
  ∑ i : Fin 3,
    h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal
      hNS ht htau hEnd hE hTail hEndpoint (φ i) i s

/-- One compact-test temporal-derivative coordinate pairing on the ambient
elapsed-time line. -/
noncomputable def h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
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
    (φ : H3WeakTestFunction)
    (i : Fin 3)
    (s : ℝ) :
    ℝ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint
  ∫ x : Point3,
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ x)
      (temporal.d
        (fun r : ℝ =>
          (h3SpectralRealVelocityOfPath W r x).component
            (h3AxisOfFin3 i))
        s)
    ∂volume

/-- Ambient-real extension of the continuous weak projected RHS pairing.
Outside the physical elapsed interval it is set to zero; only its restriction
to `[0,τ]` is used. -/
noncomputable def h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
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
    (φ : H3WeakTestVector)
    (s : ℝ) :
    ℝ :=
  if hs : s ∈ Set.Icc (0 : ℝ) tau then
    h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ ⟨s, hs⟩
  else
    0

/-- On the physical elapsed interval, the ambient-real velocity pairing is
exactly the already-packaged continuous `L²` Hilbert pairing. -/
theorem h3PreterminalTailCanonicalWeakVelocityPairingReal_eq_onElapsed
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
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalWeakVelocityPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ (q : ℝ)
      =
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
      hNS ht hEnd hTail φ q := by
  unfold h3PreterminalTailCanonicalWeakVelocityPairingReal
  unfold h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal
  dsimp only

  exact
    (h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_eq_integral_normalizedRealPath
      hNS ht htau hEnd hE hTail hEndpoint φ q).symm

/-- The ambient-real velocity pairing is continuous on the physical closed
elapsed interval. -/
theorem continuousOn_h3PreterminalTailCanonicalWeakVelocityPairingReal
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
    (φ : H3WeakTestVector) :
    ContinuousOn
      (h3PreterminalTailCanonicalWeakVelocityPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ)
      (Set.Icc (0 : ℝ) tau) := by
  rw [continuousOn_iff_continuous_domRestrict]

  have hEq :
      (Set.Icc (0 : ℝ) tau).domRestrict
          (h3PreterminalTailCanonicalWeakVelocityPairingReal
            hNS ht htau hEnd hE hTail hEndpoint φ)
        =
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ := by
    funext q
    exact
      h3PreterminalTailCanonicalWeakVelocityPairingReal_eq_onElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ q

  rw [hEq]

  exact
    continuous_h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
      hNS ht hEnd hTail hEndpoint φ

/-- The ambient-real projected RHS extension agrees with the continuous subtype
pairing on `[0,τ]`. -/
theorem h3PreterminalTailCanonicalWeakProjectedRHSPairingReal_apply_of_mem
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
    (φ : H3WeakTestVector)
    {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s
      =
    h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ ⟨s, hs⟩ := by
  simp only [
    h3PreterminalTailCanonicalWeakProjectedRHSPairingReal,
    dif_pos hs
  ]

/-- The ambient-real projected RHS extension is continuous when restricted to
the physical closed elapsed interval. -/
theorem continuousOn_h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
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
    (φ : H3WeakTestVector) :
    ContinuousOn
      (h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ)
      (Set.Icc (0 : ℝ) tau) := by
  rw [continuousOn_iff_continuous_domRestrict]

  have hEq :
      (Set.Icc (0 : ℝ) tau).domRestrict
          (h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
            hNS ht htau hEnd hE hTail hEndpoint φ)
        =
      h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ := by
    funext q
    exact
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal_apply_of_mem
        hNS ht htau hEnd hE hTail hEndpoint φ q.property

  rw [hEq]

  exact
    continuous_h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ

/-- Exact remaining local domination condition for differentiating one
compact-test velocity pairing under the spatial integral.

The neighborhood may depend on the coordinate.  No joint spacetime continuity
is hidden in this definition. -/
def H3PreterminalTailCanonicalWeakTemporalLocalDominationAt
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
    (φ : H3WeakTestVector) :
    Prop :=
  ∀ i : Fin 3,
    ∃ S : Set ℝ,
      S ∈ 𝓝 s
      ∧
      S ⊆ Set.Ioo (0 : ℝ) tau
      ∧
      ∃ bound : Point3 → ℝ,
        Integrable bound (volume : Measure Point3)
        ∧
        ∀ᵐ x : Point3 ∂volume,
          ∀ r : ℝ,
            r ∈ S →
            ‖(ContinuousLinearMap.lsmul ℝ ℝ)
                (φ i x)
                (temporal.d
                  (fun q : ℝ =>
                    (h3SpectralRealVelocityOfPath
                      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                        hNS ht htau.le hEnd hE hTail hEndpoint)
                      q x).component
                        (h3AxisOfFin3 i))
                  r)‖
              ≤
            bound x

/-- Global interior version of the preceding local domination frontier. -/
def H3PreterminalTailCanonicalWeakTemporalLocallyDominated
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
    (φ : H3WeakTestVector) :
    Prop :=
  ∀ s : ℝ,
    s ∈ Set.Ioo (0 : ℝ) tau →
    H3PreterminalTailCanonicalWeakTemporalLocalDominationAt
      hNS ht htau hEnd hE hTail hEndpoint s φ

/-- Under the explicit local domination frontier, one compact-test coordinate
pairing can be differentiated under the spatial integral. -/
theorem h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal_hasDerivAt_of_localDomination
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
    (φ : H3WeakTestVector)
    (hDom :
      H3PreterminalTailCanonicalWeakTemporalLocalDominationAt
        hNS ht htau hEnd hE hTail hEndpoint s φ)
    (i : Fin 3) :
    HasDerivAt
      (h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal
        hNS ht htau hEnd hE hTail hEndpoint (φ i) i)
      (h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
        hNS ht htau hEnd hE hTail hEndpoint (φ i) i s)
      s := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let F : ℝ → Point3 → ℝ :=
    fun r x =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        ((h3SpectralRealVelocityOfPath W r x).component
          (h3AxisOfFin3 i))

  let F' : ℝ → Point3 → ℝ :=
    fun r x =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (temporal.d
          (fun q : ℝ =>
            (h3SpectralRealVelocityOfPath W q x).component
              (h3AxisOfFin3 i))
          r)

  rcases hDom i with
    ⟨S, hS, hSsub, bound, hBoundInt, hBound⟩

  have hsS : s ∈ S :=
    mem_of_mem_nhds hS

  have hsIoo : s ∈ Set.Ioo (0 : ℝ) tau :=
    hSsub hsS

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hSliceContinuous
      (r : ℝ)
      (hr : r ∈ Set.Ioo (0 : ℝ) tau) :
      Continuous
        (fun x : Point3 =>
          (h3SpectralRealVelocityOfPath W r x).component
            (h3AxisOfFin3 i)) := by
    have hrClosed :
        r ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hr.1.le, hr.2.le⟩

    have hAbs :
        t + r ∈ Set.Ioo (0 : ℝ) T :=
      h3PreterminalElapsedTime_mem_Ioo
        ht hEnd ⟨r, hrClosed⟩

    have hEq :
        (fun x : Point3 =>
          (h3SpectralRealVelocityOfPath W r x).component
            (h3AxisOfFin3 i))
          =
        loggedVelocityComponent
          u
          (t + r)
          (h3AxisOfFin3 i) := by
      dsimp only [W]
      exact
        h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
          hNS ht htau hEnd hE hTail hEndpoint
          r hrClosed i

    rw [hEq]

    unfold loggedVelocityComponent

    exact
      (hPDE.regularity.velocity_spatial_three
        (t + r)
        hAbs
        (h3AxisOfFin3 i)).continuous

  have hF_meas :
      ∀ᶠ r : ℝ in 𝓝 s,
        AEStronglyMeasurable
          (F r)
          (volume : Measure Point3) := by
    filter_upwards [hS] with r hr
    have hrIoo := hSsub hr

    have hCont :
        Continuous (F r) := by
      dsimp only [F]
      change
        Continuous
          (fun x : Point3 =>
            (φ i x) *
              (h3SpectralRealVelocityOfPath W r x).component
                (h3AxisOfFin3 i))
      exact
        (φ i).continuous.mul
          (hSliceContinuous r hrIoo)

    exact hCont.aestronglyMeasurable

  have hF_int :
      Integrable
        (F s)
        (volume : Measure Point3) := by
    have hVelLocal :
        LocallyIntegrable
          (fun x : Point3 =>
            (h3SpectralRealVelocityOfPath W s x).component
              (h3AxisOfFin3 i))
          (volume : Measure Point3) :=
      (hSliceContinuous s hsIoo).locallyIntegrable

    dsimp only [F]

    exact
      (φ i).integrable_bilin
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (hVelLocal.locallyIntegrableOn Set.univ)

  have hF'_int :
      Integrable
        (F' s)
        (volume : Measure Point3) := by
    dsimp only [F', W]

    exact
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_test_mul_temporalDerivative_integrable
        hNS ht htau hEnd hE hTail hEndpoint
        hsIoo i (φ i)

  have hF'_meas :
      AEStronglyMeasurable
        (F' s)
        (volume : Measure Point3) :=
    hF'_int.aestronglyMeasurable

  have hBound' :
      ∀ᵐ x : Point3 ∂volume,
        ∀ r : ℝ,
          r ∈ S →
          ‖F' r x‖ ≤ bound x := by
    simpa only [F', W] using hBound

  have hDiff :
      ∀ᵐ x : Point3 ∂volume,
        ∀ r : ℝ,
          r ∈ S →
          HasDerivAt
            (fun q : ℝ => F q x)
            (F' r x)
            r := by
    filter_upwards with x
    intro r hr

    have hrIoo :
        r ∈ Set.Ioo (0 : ℝ) tau :=
      hSsub hr

    have hComponentOld :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_hasDerivAt_old
        hNS ht htau hEnd hE hTail hEndpoint
        hrIoo i x

    have hTemporalEq :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_temporal_d_eq_old
        hNS ht htau hEnd hE hTail hEndpoint
        hrIoo i x

    have hComponent :
        HasDerivAt
          (fun q : ℝ =>
            (h3SpectralRealVelocityOfPath W q x).component
              (h3AxisOfFin3 i))
          (temporal.d
            (fun q : ℝ =>
              (h3SpectralRealVelocityOfPath W q x).component
                (h3AxisOfFin3 i))
            r)
          r := by
      dsimp only [W] at hComponentOld hTemporalEq ⊢
      rw [hTemporalEq]
      exact hComponentOld

    have hMul :=
      hComponent.const_mul (φ i x)

    dsimp only [F, F']

    change
      HasDerivAt
        (fun q : ℝ =>
          (φ i x) *
            (h3SpectralRealVelocityOfPath W q x).component
              (h3AxisOfFin3 i))
        ((φ i x) *
          temporal.d
            (fun q : ℝ =>
              (h3SpectralRealVelocityOfPath W q x).component
                (h3AxisOfFin3 i))
            r)
        r

    exact hMul

  have hParam :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F)
      (x₀ := s)
      (s := S)
      (bound := bound)
      hS
      hF_meas
      hF_int
      (F' := F')
      hF'_meas
      hBound'
      hBoundInt
      hDiff

  dsimp only [
    h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal,
    h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal,
    W
  ]

  exact hParam.2

/-- Under local domination, the complete compact-test velocity pairing has the
expected temporal derivative pairing. -/
theorem h3PreterminalTailCanonicalWeakVelocityPairingReal_hasDerivAt_temporalPairing_of_localDomination
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
    (φ : H3WeakTestVector)
    (hDom :
      H3PreterminalTailCanonicalWeakTemporalLocalDominationAt
        hNS ht htau hEnd hE hTail hEndpoint s φ) :
    HasDerivAt
      (h3PreterminalTailCanonicalWeakVelocityPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ)
      (∑ i : Fin 3,
        h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
          hNS ht htau hEnd hE hTail hEndpoint (φ i) i s)
      s := by
  have h0 :=
    h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal_hasDerivAt_of_localDomination
      hNS ht htau hEnd hE hTail hEndpoint hs φ hDom (0 : Fin 3)

  have h1 :=
    h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal_hasDerivAt_of_localDomination
      hNS ht htau hEnd hE hTail hEndpoint hs φ hDom (1 : Fin 3)

  have h2 :=
    h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal_hasDerivAt_of_localDomination
      hNS ht htau hEnd hE hTail hEndpoint hs φ hDom (2 : Fin 3)

  have h012 :=
    (h0.add h1).add h2

  rw [Fin.sum_univ_three]

  have hPairingEq :
      h3PreterminalTailCanonicalWeakVelocityPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ
        =
      (h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal
          hNS ht htau hEnd hE hTail hEndpoint (φ 0) 0
        +
       h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal
          hNS ht htau hEnd hE hTail hEndpoint (φ 1) 1
        +
       h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal
          hNS ht htau hEnd hE hTail hEndpoint (φ 2) 2) := by
    funext r
    unfold h3PreterminalTailCanonicalWeakVelocityPairingReal
    rw [Fin.sum_univ_three]
    rfl

  have hEventuallyEq :
      h3PreterminalTailCanonicalWeakVelocityPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ
        =ᶠ[𝓝 s]
      (h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal
          hNS ht htau hEnd hE hTail hEndpoint (φ 0) 0
        +
       h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal
          hNS ht htau hEnd hE hTail hEndpoint (φ 1) 1
        +
       h3PreterminalTailCanonicalWeakVelocityCoordinatePairingReal
          hNS ht htau hEnd hE hTail hEndpoint (φ 2) 2) := by
    exact
      Filter.Eventually.of_forall
        (fun r => congrFun hPairingEq r)

  exact
    h012.congr_of_eventuallyEq hEventuallyEq

/-- Under local domination and divergence-free testing, the derivative of the
continuous velocity pairing is exactly the already-constructed continuous weak
projected RHS pairing. -/
theorem h3PreterminalTailCanonicalWeakVelocityPairingReal_hasDerivAt_weakProjectedRHS_of_localDomination
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
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hDom :
      H3PreterminalTailCanonicalWeakTemporalLocalDominationAt
        hNS ht htau hEnd hE hTail hEndpoint s φ) :
    HasDerivAt
      (h3PreterminalTailCanonicalWeakVelocityPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ)
      (h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ
        ⟨s, ⟨hs.1.le, hs.2.le⟩⟩)
      s := by
  have hDeriv :=
    h3PreterminalTailCanonicalWeakVelocityPairingReal_hasDerivAt_temporalPairing_of_localDomination
      hNS ht htau hEnd hE hTail hEndpoint
      hs φ hDom

  have hTemporalEq :
      (∑ i : Fin 3,
        h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
          hNS ht htau hEnd hE hTail hEndpoint (φ i) i s)
        =
      h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ
        ⟨s, ⟨hs.1.le, hs.2.le⟩⟩ := by
    unfold h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
    dsimp only

    exact
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_weakTemporalPairing_eq_weakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint
        hs φ hφ

  rw [hTemporalEq] at hDeriv

  exact hDeriv

/-- At strict interior elapsed times, the ambient-real continuous weak RHS is
also the quotient-safe physical `L²` RHS pairing. -/
theorem h3PreterminalTailCanonicalWeakProjectedRHSPairingReal_eq_projectedRHSPhysicalL2
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
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    let hsClosed : s ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hs.1.le, hs.2.le⟩
    let R : Fin 3 → H3ScalarL2 :=
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Vector
        hNS ht htau hEnd hE hTail hEndpoint s hsClosed
    h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (R i x)
        ∂volume := by
  dsimp only

  have hsClosed :
      s ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hs.1.le, hs.2.le⟩

  rw [
    h3PreterminalTailCanonicalWeakProjectedRHSPairingReal_apply_of_mem
      hNS ht htau hEnd hE hTail hEndpoint φ hsClosed
  ]

  exact
    h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed_eq_projectedRHSPhysicalL2
      hNS ht htau hEnd hE hTail hEndpoint
      hs φ hφ

/-- If the explicit local domination frontier holds at every strict elapsed
time, scalar FTC closes the complete weak projected evolution on `[0,τ]`. -/
theorem h3PreterminalTailCanonicalWeakVelocityPairing_intervalIntegral_of_localDomination
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
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hDom :
      H3PreterminalTailCanonicalWeakTemporalLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint φ) :
    (∫ s in (0 : ℝ)..tau,
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s)
      =
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨tau, ⟨htau.le, le_rfl⟩⟩
      -
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨0, ⟨le_rfl, htau.le⟩⟩ := by
  let P : ℝ → ℝ :=
    h3PreterminalTailCanonicalWeakVelocityPairingReal
      hNS ht htau hEnd hE hTail hEndpoint φ

  let G : ℝ → ℝ :=
    h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
      hNS ht htau hEnd hE hTail hEndpoint φ

  have hPContinuous :
      ContinuousOn P (Set.Icc (0 : ℝ) tau) := by
    dsimp only [P]
    exact
      continuousOn_h3PreterminalTailCanonicalWeakVelocityPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ

  have hGContinuous :
      ContinuousOn G (Set.Icc (0 : ℝ) tau) := by
    dsimp only [G]
    exact
      continuousOn_h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ

  have hGIntegrable :
      IntervalIntegrable
        G
        volume
        (0 : ℝ)
        tau := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le htau.le] using hGContinuous

  have hPDeriv :
      ∀ s : ℝ,
        s ∈ Set.Ioo (0 : ℝ) tau →
        HasDerivAt P (G s) s := by
    intro s hs

    have h :=
      h3PreterminalTailCanonicalWeakVelocityPairingReal_hasDerivAt_weakProjectedRHS_of_localDomination
        hNS ht htau hEnd hE hTail hEndpoint
        hs φ hφ (hDom s hs)

    have hsClosed :
        s ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hs.1.le, hs.2.le⟩

    have hG :
        G s
          =
        h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
          hNS ht htau hEnd hE hTail hEndpoint φ
          ⟨s, hsClosed⟩ := by
      dsimp only [G]
      exact
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal_apply_of_mem
          hNS ht htau hEnd hE hTail hEndpoint φ hsClosed

    dsimp only [P]
    rw [hG]
    exact h

  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      htau.le
      hPContinuous
      hPDeriv
      hGIntegrable

  have hPtau :
      P tau
        =
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨tau, ⟨htau.le, le_rfl⟩⟩ := by
    dsimp only [P]
    exact
      h3PreterminalTailCanonicalWeakVelocityPairingReal_eq_onElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ
        ⟨tau, ⟨htau.le, le_rfl⟩⟩

  have hPzero :
      P 0
        =
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨0, ⟨le_rfl, htau.le⟩⟩ := by
    dsimp only [P]
    exact
      h3PreterminalTailCanonicalWeakVelocityPairingReal_eq_onElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ
        ⟨0, ⟨le_rfl, htau.le⟩⟩

  dsimp only [G] at hFTC
  rw [hPtau, hPzero] at hFTC

  exact hFTC

end

end Euclidean
end Bridge
end PrimeTensor

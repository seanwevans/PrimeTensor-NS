import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Projected.RHS.Weak.Evolution.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.PointwiseFTC
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Reduce endpoint-independent weak evolution to local temporal domination

The remaining scalar frontier is

    <φ, O(q)-O(0)> = ∫₀^q <φ,R_old(r)> dr.

This file does not assume endpoint `L²` continuity and does not reconstruct an
endpoint-normalized path.  Instead it works directly with the actual old
preterminal velocity

    r ↦ u(t+r,x).

For one compact divergence-free test `φ`, define the scalar pairing

    Pφ(r) = Σ_i ∫ φ_i(x) u_i(t+r,x) dx.

The only extra analytic input introduced here is local domination of the
compact-tested actual temporal derivative: at each closed elapsed time and
each coordinate there is a time neighborhood and an integrable spatial
majorant for

    |φ_i(x) ∂ₜu_i(t+r,x)|.

Under that condition Mathlib's parameter-integral derivative theorem applies,
so

    Pφ'(r) = Σ_i ∫ φ_i(x) ∂ₜu_i(t+r,x) dx.

The endpoint-independent weak momentum identity already identifies the latter
with `<φ,R_old(r)>`.  Derivatives at every closed elapsed point supply the
closed-interval continuity needed by scalar FTC.  Hence local domination
implies the exact projected-RHS weak evolution frontier.

No temporal product-space Fubini hypothesis and no endpoint continuity
hypothesis occurs below.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongProjectedRHSWeakEvolutionLocalDomination
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongProjectedRHSWeakEvolutionLocalDomination :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- One actual old compact-test velocity coordinate pairing on the ambient
elapsed-time line. -/
noncomputable def h3PreterminalLoggedVelocityWeakCoordinatePairingReal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t : ℝ)
    (φ : H3WeakTestFunction)
    (i : Fin 3)
    (r : ℝ) :
    ℝ :=
  ∫ x : Point3,
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ x)
      (loggedVelocityComponent
        u (t + r) (h3AxisOfFin3 i) x)
    ∂volume

/-- Complete actual old compact-test velocity pairing. -/
noncomputable def h3PreterminalLoggedVelocityWeakPairingReal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t : ℝ)
    (φ : H3WeakTestVector)
    (r : ℝ) :
    ℝ :=
  ∑ i : Fin 3,
    h3PreterminalLoggedVelocityWeakCoordinatePairingReal
      hNS t (φ i) i r

/-- One actual old compact-test temporal-derivative coordinate pairing. -/
noncomputable def h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t : ℝ)
    (φ : H3WeakTestFunction)
    (i : Fin 3)
    (r : ℝ) :
    ℝ :=
  ∫ x : Point3,
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ x)
      (temporal.d
        (fun a : ℝ =>
          loggedVelocityComponent
            u a (h3AxisOfFin3 i) x)
        (t + r))
    ∂volume

/-- Local domination for one actual-old weak temporal pairing.

The neighborhood is allowed to extend to either side of the requested elapsed
time, but every point of it must remain strictly inside the absolute
preterminal interval after the shift by `t`.  This lets the same condition
provide ordinary continuity even at elapsed endpoints `0` and `tau`. -/
def H3PreterminalLoggedVelocityWeakTemporalLocalDominationAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t s : ℝ)
    (φ : H3WeakTestVector) :
    Prop :=
  ∀ i : Fin 3,
    ∃ S : Set ℝ,
      S ∈ 𝓝 s
      ∧
      (∀ r : ℝ, r ∈ S → t + r ∈ Set.Ioo (0 : ℝ) T)
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
                  (fun a : ℝ =>
                    loggedVelocityComponent
                      u a (h3AxisOfFin3 i) x)
                  (t + r))‖
              ≤
            bound x

/-- Closed-elapsed-interval local domination family. -/
def H3PreterminalLoggedVelocityWeakTemporalLocallyDominatedOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t tau : ℝ)
    (φ : H3WeakTestVector) :
    Prop :=
  ∀ s : ℝ,
    s ∈ Set.Icc (0 : ℝ) tau →
    H3PreterminalLoggedVelocityWeakTemporalLocalDominationAt
      hNS t s φ

/-- Local domination justifies differentiation of one actual-old spatial
pairing. -/
theorem h3PreterminalLoggedVelocityWeakCoordinatePairingReal_hasDerivAt_of_localDomination
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (hDom :
      H3PreterminalLoggedVelocityWeakTemporalLocalDominationAt
        hNS t s φ)
    (i : Fin 3) :
    HasDerivAt
      (h3PreterminalLoggedVelocityWeakCoordinatePairingReal
        hNS t (φ i) i)
      (h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
        hNS t (φ i) i s)
      s := by
  let F : ℝ → Point3 → ℝ :=
    fun r x =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (loggedVelocityComponent
          u (t + r) (h3AxisOfFin3 i) x)

  let F' : ℝ → Point3 → ℝ :=
    fun r x =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (temporal.d
          (fun a : ℝ =>
            loggedVelocityComponent
              u a (h3AxisOfFin3 i) x)
          (t + r))

  rcases hDom i with
    ⟨S, hS, hSAbs, bound, hBoundInt, hBound⟩

  have hsS : s ∈ S :=
    mem_of_mem_nhds hS

  have hsAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    hSAbs s hsS

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
      (hr : t + r ∈ Set.Ioo (0 : ℝ) T) :
      Continuous
        (fun x : Point3 =>
          loggedVelocityComponent
            u (t + r) (h3AxisOfFin3 i) x) := by
    unfold loggedVelocityComponent
    exact
      (hPDE.regularity.velocity_spatial_three
        (t + r)
        hr
        (h3AxisOfFin3 i)).continuous

  have hF_meas :
      ∀ᶠ r : ℝ in 𝓝 s,
        AEStronglyMeasurable
          (F r)
          (volume : Measure Point3) := by
    filter_upwards [hS] with r hr

    have hCont :
        Continuous (F r) := by
      dsimp only [F]
      change
        Continuous
          (fun x : Point3 =>
            (φ i x) *
              loggedVelocityComponent
                u (t + r) (h3AxisOfFin3 i) x)
      exact
        (φ i).continuous.mul
          (hSliceContinuous r (hSAbs r hr))

    exact hCont.aestronglyMeasurable

  have hF_int :
      Integrable
        (F s)
        (volume : Measure Point3) := by
    have hVelLocal :
        LocallyIntegrable
          (fun x : Point3 =>
            loggedVelocityComponent
              u (t + s) (h3AxisOfFin3 i) x)
          (volume : Measure Point3) :=
      (hSliceContinuous s hsAbs).locallyIntegrable

    dsimp only [F]

    exact
      (φ i).integrable_bilin
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (hVelLocal.locallyIntegrableOn Set.univ)

  have hF'_int :
      Integrable
        (F' s)
        (volume : Measure Point3) := by
    dsimp only [F']

    exact
      h3PreterminalLoggedVelocity_test_mul_temporalDerivative_integrable
        hNS ht hEnd hTail
        ⟨s, hs⟩ i (φ i)

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
    simpa only [F'] using hBound

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

    let fOld : ℝ → ℝ :=
      fun a : ℝ =>
        loggedVelocityComponent
          u a (h3AxisOfFin3 i) x

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

    have hAbs :
        t + r ∈ Set.Ioo (0 : ℝ) T :=
      hSAbs r hr

    have hOldDiffWithin :
        DifferentiableWithinAt
          ℝ
          fOld
          (Set.Ioo (0 : ℝ) T)
          (t + r) :=
      hOldDiffOn (t + r) hAbs

    have hOldDiff :
        DifferentiableAt ℝ fOld (t + r) :=
      hOldDiffWithin.differentiableAt
        (isOpen_Ioo.mem_nhds hAbs)

    have hOldHas :
        HasDerivAt
          fOld
          (deriv fOld (t + r))
          (t + r) :=
      hOldDiff.hasDerivAt

    have hShift :
        HasDerivAt
          (fun a : ℝ => t + a)
          1
          r := by
      simpa using
        (hasDerivAt_id r).const_add t

    have hComp :=
      hOldHas.comp r hShift

    have hComponent :
        HasDerivAt
          (fun q : ℝ =>
            loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + r))
          r := by
      change
        HasDerivAt
          (fun q : ℝ => fOld (t + q))
          (deriv fOld (t + r))
          r

      simpa only [
        Function.comp_def,
        mul_one,
        temporal_d,
        fOld
      ] using hComp

    have hMul :=
      hComponent.const_mul (φ i x)

    dsimp only [F, F']

    change
      HasDerivAt
        (fun q : ℝ =>
          (φ i x) *
            loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x)
        ((φ i x) *
          temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + r))
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
    h3PreterminalLoggedVelocityWeakCoordinatePairingReal,
    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
  ]

  exact hParam.2

/-- Local domination differentiates the complete old scalar weak pairing. -/
theorem h3PreterminalLoggedVelocityWeakPairingReal_hasDerivAt_temporalPairing_of_localDomination
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (hDom :
      H3PreterminalLoggedVelocityWeakTemporalLocalDominationAt
        hNS t s φ) :
    HasDerivAt
      (h3PreterminalLoggedVelocityWeakPairingReal
        hNS t φ)
      (∑ i : Fin 3,
        h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
          hNS t (φ i) i s)
      s := by
  have h0 :=
    h3PreterminalLoggedVelocityWeakCoordinatePairingReal_hasDerivAt_of_localDomination
      hNS ht htau hEnd hTail hs φ hDom (0 : Fin 3)

  have h1 :=
    h3PreterminalLoggedVelocityWeakCoordinatePairingReal_hasDerivAt_of_localDomination
      hNS ht htau hEnd hTail hs φ hDom (1 : Fin 3)

  have h2 :=
    h3PreterminalLoggedVelocityWeakCoordinatePairingReal_hasDerivAt_of_localDomination
      hNS ht htau hEnd hTail hs φ hDom (2 : Fin 3)

  have h012 :=
    (h0.add h1).add h2

  rw [Fin.sum_univ_three]

  have hPairingEq :
      h3PreterminalLoggedVelocityWeakPairingReal
          hNS t φ
        =
      (h3PreterminalLoggedVelocityWeakCoordinatePairingReal
          hNS t (φ 0) 0
        +
       h3PreterminalLoggedVelocityWeakCoordinatePairingReal
          hNS t (φ 1) 1
        +
       h3PreterminalLoggedVelocityWeakCoordinatePairingReal
          hNS t (φ 2) 2) := by
    funext r
    unfold h3PreterminalLoggedVelocityWeakPairingReal
    rw [Fin.sum_univ_three]
    rfl

  have hEventuallyEq :
      h3PreterminalLoggedVelocityWeakPairingReal
          hNS t φ
        =ᶠ[𝓝 s]
      (h3PreterminalLoggedVelocityWeakCoordinatePairingReal
          hNS t (φ 0) 0
        +
       h3PreterminalLoggedVelocityWeakCoordinatePairingReal
          hNS t (φ 1) 1
        +
       h3PreterminalLoggedVelocityWeakCoordinatePairingReal
          hNS t (φ 2) 2) := by
    exact
      Filter.Eventually.of_forall
        (fun r => congrFun hPairingEq r)

  exact
    h012.congr_of_eventuallyEq hEventuallyEq

/-- For divergence-free testing, the derivative supplied by local domination is
exactly the old physical projected-RHS Hilbert pairing. -/
theorem h3PreterminalLoggedVelocityWeakPairingReal_hasDerivAt_projectedRHS_of_localDomination
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hDom :
      H3PreterminalLoggedVelocityWeakTemporalLocalDominationAt
        hNS t s φ) :
    HasDerivAt
      (h3PreterminalLoggedVelocityWeakPairingReal
        hNS t φ)
      (inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail s))
      s := by
  have hDeriv :=
    h3PreterminalLoggedVelocityWeakPairingReal_hasDerivAt_temporalPairing_of_localDomination
      hNS ht htau hEnd hTail hs φ hDom

  have hTemporalEq :
      (∑ i : Fin 3,
        h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
          hNS t (φ i) i s)
        =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail ⟨s, hs⟩) := by
    unfold h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal

    exact
      h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail ⟨s, hs⟩ φ hφ

  rw [hTemporalEq] at hDeriv

  rw [
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
      hNS ht hEnd hTail hs
  ]

  exact hDeriv

/-- The ambient scalar old pairing difference is the literal compact-test
logged-velocity difference appearing in the endpoint-independent Hilbert
increment bridge. -/
theorem h3PreterminalLoggedVelocityWeakPairingReal_sub_eq_loggedPairingDifference
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalLoggedVelocityWeakPairingReal hNS t φ (q : ℝ)
        -
      h3PreterminalLoggedVelocityWeakPairingReal hNS t φ 0
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + (q : ℝ)) (h3AxisOfFin3 i) x
            -
           loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume := by
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hqAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q

  unfold h3PreterminalLoggedVelocityWeakPairingReal
  rw [← Finset.sum_sub_distrib]

  apply Finset.sum_congr rfl
  intro i hi

  let Fq : Point3 → ℝ :=
    fun x : Point3 =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (loggedVelocityComponent
          u (t + (q : ℝ)) (h3AxisOfFin3 i) x)

  let F0 : Point3 → ℝ :=
    fun x : Point3 =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (loggedVelocityComponent
          u t (h3AxisOfFin3 i) x)

  have hQCont :
      Continuous
        (fun x : Point3 =>
          loggedVelocityComponent
            u (t + (q : ℝ)) (h3AxisOfFin3 i) x) := by
    unfold loggedVelocityComponent
    exact
      (hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ))
        hqAbs
        (h3AxisOfFin3 i)).continuous

  have h0Cont :
      Continuous
        (fun x : Point3 =>
          loggedVelocityComponent
            u t (h3AxisOfFin3 i) x) := by
    unfold loggedVelocityComponent
    exact
      (hPDE.regularity.velocity_spatial_three
        t
        ht
        (h3AxisOfFin3 i)).continuous

  have hQInt :
      Integrable Fq (volume : Measure Point3) := by
    dsimp only [Fq]
    exact
      (φ i).integrable_bilin
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (hQCont.locallyIntegrable.locallyIntegrableOn Set.univ)

  have h0Int :
      Integrable F0 (volume : Measure Point3) := by
    dsimp only [F0]
    exact
      (φ i).integrable_bilin
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (h0Cont.locallyIntegrable.locallyIntegrableOn Set.univ)

  unfold h3PreterminalLoggedVelocityWeakCoordinatePairingReal
  simp only [add_zero]

  rw [← integral_sub hQInt h0Int]

  apply integral_congr_ae
  filter_upwards with x

  dsimp only [Fq, F0]
  simp only [
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul
  ]
  ring

/-- Closed-interval local domination implies the exact scalar weak evolution
identity for one divergence-free compact test. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_oldVelocityIncrement_eq_projectedRHSHilbert_intervalIntegral_of_localDomination
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hDom :
      H3PreterminalLoggedVelocityWeakTemporalLocallyDominatedOnElapsed
        hNS t tau φ)
    (q : Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)
      =
    ∫ r in (0 : ℝ)..(q : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail r) := by
  let P : ℝ → ℝ :=
    h3PreterminalLoggedVelocityWeakPairingReal
      hNS t φ

  let G : ℝ → ℝ :=
    fun r : ℝ =>
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail r)

  have hPContinuous :
      ContinuousOn
        P
        (Set.Icc (0 : ℝ) (q : ℝ)) := by
    intro s hs

    have hsTau :
        s ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hs.1, hs.2.trans q.property.2⟩

    have hDeriv :=
      h3PreterminalLoggedVelocityWeakPairingReal_hasDerivAt_temporalPairing_of_localDomination
        hNS ht htau hEnd hTail
        hsTau φ (hDom s hsTau)

    exact
      hDeriv.continuousAt.continuousWithinAt

  have hGIntegrable :
      IntervalIntegrable
        G
        volume
        (0 : ℝ)
        (q : ℝ) := by
    dsimp only [G]
    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal
        hNS ht hEnd hE hTail φ hφ q

  have hPDeriv :
      ∀ s : ℝ,
        s ∈ Set.Ioo (0 : ℝ) (q : ℝ) →
        HasDerivAt P (G s) s := by
    intro s hs

    have hsTau :
        s ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hs.1.le, hs.2.le.trans q.property.2⟩

    dsimp only [P, G]

    exact
      h3PreterminalLoggedVelocityWeakPairingReal_hasDerivAt_projectedRHS_of_localDomination
        hNS ht htau hEnd hTail
        hsTau φ hφ (hDom s hsTau)

  have hFTC :
      (∫ s in (0 : ℝ)..(q : ℝ), G s)
        =
      P (q : ℝ) - P 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      q.property.1
      hPContinuous
      hPDeriv
      hGIntegrable

  have hLogged :
      P (q : ℝ) - P 0
        =
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (loggedVelocityComponent
                u (t + (q : ℝ)) (h3AxisOfFin3 i) x
              -
             loggedVelocityComponent
                u t (h3AxisOfFin3 i) x)
          ∂volume := by
    dsimp only [P]
    exact
      h3PreterminalLoggedVelocityWeakPairingReal_sub_eq_loggedPairingDifference
        hNS ht htau hEnd hTail φ q

  have hOld :=
    inner_h3WeakTestVectorPhysicalL2Hilbert_oldVelocityIncrement_eq_loggedPairingDifference
      hNS ht htau hEnd hTail φ q

  calc
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)
        =
      P (q : ℝ) - P 0 := by
        rw [hOld]
        exact hLogged.symm
    _ =
      ∫ r in (0 : ℝ)..(q : ℝ), G r :=
        hFTC.symm
    _ =
      ∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r) := by
        rfl

/-- Family-level local domination implies the evolution-only scalar frontier. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed_of_allLocalDomination
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hDom :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        H3PreterminalLoggedVelocityWeakTemporalLocallyDominatedOnElapsed
          hNS t tau φ) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed
      hNS ht htau hEnd hTail := by
  intro φ hφ q

  exact
    inner_h3WeakTestVectorPhysicalL2Hilbert_oldVelocityIncrement_eq_projectedRHSHilbert_intervalIntegral_of_localDomination
      hNS ht htau hEnd hE hTail
      φ hφ (hDom φ hφ) q

end

end Euclidean
end Bridge
end PrimeTensor

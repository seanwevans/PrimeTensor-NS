import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Fubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fundamental theorem of calculus for the endpoint vorticity pairings

`Fubini` moved the compactly tested vorticity temporal derivative through the
spatial integral.  This file evaluates the remaining one-dimensional temporal
integral pointwise in space.

For almost every spatial point, product-space integrability gives interval
integrability of the compactly tested zero-extended temporal derivative.
Inside the strict elapsed interval that extension is the genuine derivative of
the old vorticity trajectory.  The one-dimensional FTC therefore returns the
endpoint vorticity increment.

After integrating in space, this yields the three weak-vorticity pairing
increment identities needed by the curl route.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityFTC :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)


/-- Canonical zero point in the same elapsed interval as `q`. -/
noncomputable def h3EndpointElapsedZero
    {tau : ℝ}
    (q : Set.Icc (0 : ℝ) tau) :
    Set.Icc (0 : ℝ) tau :=
  ⟨0, by
    constructor
    · exact le_rfl
    · exact le_trans q.property.1 q.property.2⟩

@[simp]
theorem h3EndpointElapsedZero_coe
    {tau : ℝ}
    (q : Set.Icc (0 : ℝ) tau) :
    ((h3EndpointElapsedZero q : Set.Icc (0 : ℝ) tau) : ℝ) = 0 := by
  rfl

/-- Local copy of the first-derivative compact-test integrability lemma, using
the measure instance of this file. -/
theorem h3PreterminalTailCanonical_test_mul_loggedVelocitySpatialDerivative_integrable_ftc
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j a : PrimeTensor.Axis Depth.three)
    (ψ : H3WeakTestFunction) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d
            a
            (loggedVelocityComponent u (t + (q : ℝ)) j)
            x))
      (volume : Measure Point3) := by
  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hC3 :
      SpatialC3
        (loggedVelocityComponent
          u (t + (q : ℝ)) j) := by
    unfold loggedVelocityComponent
    exact
      hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ)) hAbs j

  have hC1 :
      SpatialC1
        (loggedVelocityComponent
          u (t + (q : ℝ)) j) :=
    hC3.of_le (by norm_num)

  have hDContinuous :
      Continuous
        (spatial3.d
          a
          (loggedVelocityComponent
            u (t + (q : ℝ)) j)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hC1 a

  exact
    ψ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hDContinuous.locallyIntegrable.locallyIntegrableOn Set.univ)

/-- Compact testing of the old x-vorticity is spatially integrable at every
closed endpoint slice. -/
theorem h3PreterminalTailCanonical_test_mul_realVorticityX_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (realVorticityX
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x))
      (volume : Measure Point3) := by
  have hDy :=
    h3PreterminalTailCanonical_test_mul_loggedVelocitySpatialDerivative_integrable_ftc
      hNS ht hEnd hTail q zAxis yAxis ψ

  have hDz :=
    h3PreterminalTailCanonical_test_mul_loggedVelocitySpatialDerivative_integrable_ftc
      hNS ht hEnd hTail q yAxis zAxis ψ

  have hSub := hDy.sub hDz

  have hzEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) zAxis
        =
      fun y : Point3 =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component zAxis := by
    rfl

  have hyEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) yAxis
        =
      fun y : Point3 =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component yAxis := by
    rfl

  rw [hzEq, hyEq] at hSub

  apply Integrable.congr hSub
  filter_upwards with x
  change
    (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d
              yAxis
              (fun y : Point3 =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component zAxis)
              x)
      -
    (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d
              zAxis
              (fun y : Point3 =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component yAxis)
              x)
      =
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (
        spatial3.d
            yAxis
            (fun y : Point3 =>
              (logSpaceTimeVectorField
                u (t + (q : ℝ)) y).component zAxis)
            x
          -
        spatial3.d
            zAxis
            (fun y : Point3 =>
              (logSpaceTimeVectorField
                u (t + (q : ℝ)) y).component yAxis)
            x
      )
  exact
    (((ContinuousLinearMap.lsmul ℝ ℝ) (ψ x)).map_sub
      (spatial3.d
        yAxis
        (fun y : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component zAxis)
        x)
      (spatial3.d
        zAxis
        (fun y : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component yAxis)
        x)).symm

/-- Compact testing of the old y-vorticity is spatially integrable at every
closed endpoint slice. -/
theorem h3PreterminalTailCanonical_test_mul_realVorticityY_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (realVorticityY
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x))
      (volume : Measure Point3) := by
  have hDz :=
    h3PreterminalTailCanonical_test_mul_loggedVelocitySpatialDerivative_integrable_ftc
      hNS ht hEnd hTail q xAxis zAxis ψ

  have hDx :=
    h3PreterminalTailCanonical_test_mul_loggedVelocitySpatialDerivative_integrable_ftc
      hNS ht hEnd hTail q zAxis xAxis ψ

  have hSub := hDz.sub hDx

  have hxEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) xAxis
        =
      fun y : Point3 =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component xAxis := by
    rfl

  have hzEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) zAxis
        =
      fun y : Point3 =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component zAxis := by
    rfl

  rw [hxEq, hzEq] at hSub

  apply Integrable.congr hSub
  filter_upwards with x
  change
    (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d
              zAxis
              (fun y : Point3 =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component xAxis)
              x)
      -
    (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d
              xAxis
              (fun y : Point3 =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component zAxis)
              x)
      =
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (
        spatial3.d
            zAxis
            (fun y : Point3 =>
              (logSpaceTimeVectorField
                u (t + (q : ℝ)) y).component xAxis)
            x
          -
        spatial3.d
            xAxis
            (fun y : Point3 =>
              (logSpaceTimeVectorField
                u (t + (q : ℝ)) y).component zAxis)
            x
      )
  exact
    (((ContinuousLinearMap.lsmul ℝ ℝ) (ψ x)).map_sub
      (spatial3.d
        zAxis
        (fun y : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component xAxis)
        x)
      (spatial3.d
        xAxis
        (fun y : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component zAxis)
        x)).symm

/-- Compact testing of the old z-vorticity is spatially integrable at every
closed endpoint slice. -/
theorem h3PreterminalTailCanonical_test_mul_realVorticityZ_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (realVorticityZ
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x))
      (volume : Measure Point3) := by
  have hDx :=
    h3PreterminalTailCanonical_test_mul_loggedVelocitySpatialDerivative_integrable_ftc
      hNS ht hEnd hTail q yAxis xAxis ψ

  have hDy :=
    h3PreterminalTailCanonical_test_mul_loggedVelocitySpatialDerivative_integrable_ftc
      hNS ht hEnd hTail q xAxis yAxis ψ

  have hSub := hDx.sub hDy

  have hyEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) yAxis
        =
      fun y : Point3 =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component yAxis := by
    rfl

  have hxEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) xAxis
        =
      fun y : Point3 =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component xAxis := by
    rfl

  rw [hyEq, hxEq] at hSub

  apply Integrable.congr hSub
  filter_upwards with x
  change
    (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d
              xAxis
              (fun y : Point3 =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component yAxis)
              x)
      -
    (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d
              yAxis
              (fun y : Point3 =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component xAxis)
              x)
      =
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (
        spatial3.d
            xAxis
            (fun y : Point3 =>
              (logSpaceTimeVectorField
                u (t + (q : ℝ)) y).component yAxis)
            x
          -
        spatial3.d
            yAxis
            (fun y : Point3 =>
              (logSpaceTimeVectorField
                u (t + (q : ℝ)) y).component xAxis)
            x
      )
  exact
    (((ContinuousLinearMap.lsmul ℝ ℝ) (ψ x)).map_sub
      (spatial3.d
        xAxis
        (fun y : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component yAxis)
        x)
      (spatial3.d
        yAxis
        (fun y : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component xAxis)
        x)).symm

/-- Pointwise-in-space FTC for the compactly tested x-vorticity trajectory. -/
theorem intervalIntegral_h3LoggedPreterminalVorticityXTemporalDerivative_eq_sub
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (x : Point3)
    (hInt :
      Integrable
        (fun r : ℝ =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
              hNS (t + r) x))
        ((volume : Measure ℝ).restrict
          (Set.Ioo (0 : ℝ) (q : ℝ)))) :
    (∫ r in (0 : ℝ)..(q : ℝ),
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
          hNS (t + r) x))
      =
    (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (realVorticityX
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          x)
      -
    (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (realVorticityX
          (logSpaceTimeVectorField u)
          t
          x) := by
  let F : ℝ → ℝ :=
    fun r =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (realVorticityX
          (logSpaceTimeVectorField u)
          (t + r)
          x)

  let F' : ℝ → ℝ :=
    fun r =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
          hNS (t + r) x)

  have hCont :
      ContinuousOn F (Set.uIcc (0 : ℝ) (q : ℝ)) := by
    rw [Set.uIcc_of_le q.2.1]
    intro r hr

    have hrTau :
        r ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hr.1, hr.2.trans q.2.2⟩

    have hAbs :
        t + r ∈ Set.Ioo (0 : ℝ) T :=
      h3PreterminalElapsedTime_mem_Ioo
        ht hEnd ⟨r, hrTau⟩

    have hBase :=
      h3LoggedPreterminalVorticityX_hasDerivAt
        hNS hAbs x

    have hShift :
        HasDerivAt
          (fun s : ℝ => t + s)
          1
          r := by
      simpa only [id_eq] using
        (hasDerivAt_id r).const_add t

    have hElapsed := hBase.comp r hShift

    have hPair :=
      HasDerivAt.const_mul
        (ψ x)
        hElapsed

    simpa only [
      F,
      Function.comp_def,
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul,
      mul_one
    ] using hPair.continuousAt.continuousWithinAt

  have hDeriv :
      ∀ r ∈ Set.Ioo
          (min (0 : ℝ) (q : ℝ))
          (max (0 : ℝ) (q : ℝ)),
        HasDerivWithinAt F (F' r) (Set.Ioi r) r := by
    intro r hr
    rw [
      min_eq_left q.2.1,
      max_eq_right q.2.1
    ] at hr

    have hrTau :
        r ∈ Set.Ioo (0 : ℝ) tau :=
      ⟨hr.1, lt_of_lt_of_le hr.2 q.2.2⟩

    have hElapsed :=
      h3LoggedPreterminalVorticityX_elapsed_hasDerivAt
        hNS ht hEnd hrTau x

    have hPair :=
      HasDerivAt.const_mul
        (ψ x)
        hElapsed

    have hAbs :
        t + r ∈ Set.Ioo (0 : ℝ) T :=
      h3PreterminalElapsedTime_mem_Ioo
        ht hEnd
        ⟨r, ⟨hr.1.le, hr.2.le.trans q.2.2⟩⟩

    have hExt :=
      h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
        hNS hAbs x

    dsimp only [F, F']
    rw [hExt]

    simpa only [
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul
    ] using hPair.hasDerivWithinAt

  have hInterval :
      IntervalIntegrable F' volume (0 : ℝ) (q : ℝ) := by
    rw [
      intervalIntegrable_iff_integrableOn_Ioc_of_le
        q.2.1
    ]

    change
      Integrable
        F'
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (q : ℝ)))

    rw [← restrict_Ioo_eq_restrict_Ioc]

    simpa only [F'] using hInt

  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right
      hCont hDeriv hInterval

  simpa only [F, F', add_zero] using hFTC

/-- Pointwise-in-space FTC for the compactly tested y-vorticity trajectory. -/
theorem intervalIntegral_h3LoggedPreterminalVorticityYTemporalDerivative_eq_sub
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (x : Point3)
    (hInt :
      Integrable
        (fun r : ℝ =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
              hNS (t + r) x))
        ((volume : Measure ℝ).restrict
          (Set.Ioo (0 : ℝ) (q : ℝ)))) :
    (∫ r in (0 : ℝ)..(q : ℝ),
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
          hNS (t + r) x))
      =
    (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (realVorticityY
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          x)
      -
    (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (realVorticityY
          (logSpaceTimeVectorField u)
          t
          x) := by
  let F : ℝ → ℝ :=
    fun r =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (realVorticityY
          (logSpaceTimeVectorField u)
          (t + r)
          x)

  let F' : ℝ → ℝ :=
    fun r =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
          hNS (t + r) x)

  have hCont :
      ContinuousOn F (Set.uIcc (0 : ℝ) (q : ℝ)) := by
    rw [Set.uIcc_of_le q.2.1]
    intro r hr

    have hrTau :
        r ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hr.1, hr.2.trans q.2.2⟩

    have hAbs :
        t + r ∈ Set.Ioo (0 : ℝ) T :=
      h3PreterminalElapsedTime_mem_Ioo
        ht hEnd ⟨r, hrTau⟩

    have hBase :=
      h3LoggedPreterminalVorticityY_hasDerivAt
        hNS hAbs x

    have hShift :
        HasDerivAt
          (fun s : ℝ => t + s)
          1
          r := by
      simpa only [id_eq] using
        (hasDerivAt_id r).const_add t

    have hElapsed := hBase.comp r hShift

    have hPair :=
      HasDerivAt.const_mul
        (ψ x)
        hElapsed

    simpa only [
      F,
      Function.comp_def,
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul,
      mul_one
    ] using hPair.continuousAt.continuousWithinAt

  have hDeriv :
      ∀ r ∈ Set.Ioo
          (min (0 : ℝ) (q : ℝ))
          (max (0 : ℝ) (q : ℝ)),
        HasDerivWithinAt F (F' r) (Set.Ioi r) r := by
    intro r hr
    rw [
      min_eq_left q.2.1,
      max_eq_right q.2.1
    ] at hr

    have hrTau :
        r ∈ Set.Ioo (0 : ℝ) tau :=
      ⟨hr.1, lt_of_lt_of_le hr.2 q.2.2⟩

    have hElapsed :=
      h3LoggedPreterminalVorticityY_elapsed_hasDerivAt
        hNS ht hEnd hrTau x

    have hPair :=
      HasDerivAt.const_mul
        (ψ x)
        hElapsed

    have hAbs :
        t + r ∈ Set.Ioo (0 : ℝ) T :=
      h3PreterminalElapsedTime_mem_Ioo
        ht hEnd
        ⟨r, ⟨hr.1.le, hr.2.le.trans q.2.2⟩⟩

    have hExt :=
      h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
        hNS hAbs x

    dsimp only [F, F']
    rw [hExt]

    simpa only [
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul
    ] using hPair.hasDerivWithinAt

  have hInterval :
      IntervalIntegrable F' volume (0 : ℝ) (q : ℝ) := by
    rw [
      intervalIntegrable_iff_integrableOn_Ioc_of_le
        q.2.1
    ]

    change
      Integrable
        F'
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (q : ℝ)))

    rw [← restrict_Ioo_eq_restrict_Ioc]

    simpa only [F'] using hInt

  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right
      hCont hDeriv hInterval

  simpa only [F, F', add_zero] using hFTC

/-- Pointwise-in-space FTC for the compactly tested z-vorticity trajectory. -/
theorem intervalIntegral_h3LoggedPreterminalVorticityZTemporalDerivative_eq_sub
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (x : Point3)
    (hInt :
      Integrable
        (fun r : ℝ =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
              hNS (t + r) x))
        ((volume : Measure ℝ).restrict
          (Set.Ioo (0 : ℝ) (q : ℝ)))) :
    (∫ r in (0 : ℝ)..(q : ℝ),
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
          hNS (t + r) x))
      =
    (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (realVorticityZ
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          x)
      -
    (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (realVorticityZ
          (logSpaceTimeVectorField u)
          t
          x) := by
  let F : ℝ → ℝ :=
    fun r =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (realVorticityZ
          (logSpaceTimeVectorField u)
          (t + r)
          x)

  let F' : ℝ → ℝ :=
    fun r =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
          hNS (t + r) x)

  have hCont :
      ContinuousOn F (Set.uIcc (0 : ℝ) (q : ℝ)) := by
    rw [Set.uIcc_of_le q.2.1]
    intro r hr

    have hrTau :
        r ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hr.1, hr.2.trans q.2.2⟩

    have hAbs :
        t + r ∈ Set.Ioo (0 : ℝ) T :=
      h3PreterminalElapsedTime_mem_Ioo
        ht hEnd ⟨r, hrTau⟩

    have hBase :=
      h3LoggedPreterminalVorticityZ_hasDerivAt
        hNS hAbs x

    have hShift :
        HasDerivAt
          (fun s : ℝ => t + s)
          1
          r := by
      simpa only [id_eq] using
        (hasDerivAt_id r).const_add t

    have hElapsed := hBase.comp r hShift

    have hPair :=
      HasDerivAt.const_mul
        (ψ x)
        hElapsed

    simpa only [
      F,
      Function.comp_def,
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul,
      mul_one
    ] using hPair.continuousAt.continuousWithinAt

  have hDeriv :
      ∀ r ∈ Set.Ioo
          (min (0 : ℝ) (q : ℝ))
          (max (0 : ℝ) (q : ℝ)),
        HasDerivWithinAt F (F' r) (Set.Ioi r) r := by
    intro r hr
    rw [
      min_eq_left q.2.1,
      max_eq_right q.2.1
    ] at hr

    have hrTau :
        r ∈ Set.Ioo (0 : ℝ) tau :=
      ⟨hr.1, lt_of_lt_of_le hr.2 q.2.2⟩

    have hElapsed :=
      h3LoggedPreterminalVorticityZ_elapsed_hasDerivAt
        hNS ht hEnd hrTau x

    have hPair :=
      HasDerivAt.const_mul
        (ψ x)
        hElapsed

    have hAbs :
        t + r ∈ Set.Ioo (0 : ℝ) T :=
      h3PreterminalElapsedTime_mem_Ioo
        ht hEnd
        ⟨r, ⟨hr.1.le, hr.2.le.trans q.2.2⟩⟩

    have hExt :=
      h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
        hNS hAbs x

    dsimp only [F, F']
    rw [hExt]

    simpa only [
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul
    ] using hPair.hasDerivWithinAt

  have hInterval :
      IntervalIntegrable F' volume (0 : ℝ) (q : ℝ) := by
    rw [
      intervalIntegrable_iff_integrableOn_Ioc_of_le
        q.2.1
    ]

    change
      Integrable
        F'
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (q : ℝ)))

    rw [← restrict_Ioo_eq_restrict_Ioc]

    simpa only [F'] using hInt

  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right
      hCont hDeriv hInterval

  simpa only [F, F', add_zero] using hFTC

/-- The time integral of the compactly tested x-vorticity temporal derivative
is exactly the increment of the old x-vorticity weak pairing. -/
theorem intervalIntegral_h3PreterminalWeakVorticityXTemporalDerivative_eq_pairing_sub_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    h3PreterminalTailCanonicalWeakVorticityXPairingOnElapsed
        (u := u) (t := t) ψ q
      -
    h3PreterminalTailCanonicalWeakVorticityXPairingOnElapsed
        (u := u) (t := t) ψ
        (h3EndpointElapsedZero q) := by
  have hSwap :=
    intervalIntegral_h3PreterminalWeakVorticityXTemporalDerivative_swap_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ q

  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  have hSlices :=
    hShort.1.prod_left_ae

  rw [hSwap]

  have hFTCae :
      ∀ᵐ x : Point3 ∂volume,
        (∫ r in (0 : ℝ)..(q : ℝ),
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
              hNS (t + r) x))
          =
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityX
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x)
          -
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityX
              (logSpaceTimeVectorField u)
              t
              x) := by
    filter_upwards [hSlices] with x hx
    exact
      intervalIntegral_h3LoggedPreterminalVorticityXTemporalDerivative_eq_sub
        hNS ht hEnd ψ q x hx

  rw [integral_congr_ae hFTCae]

  have hQ :=
    h3PreterminalTailCanonical_test_mul_realVorticityX_integrable
      hNS ht hEnd hTail ψ q

  have h0Raw :=
    h3PreterminalTailCanonical_test_mul_realVorticityX_integrable
      hNS ht hEnd hTail ψ
      (h3EndpointElapsedZero q)

  have h0 :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityX
              (logSpaceTimeVectorField u)
              t
              x))
        (volume : Measure Point3) := by
    simpa only [
      h3EndpointElapsedZero_coe,
      add_zero
    ] using h0Raw

  rw [integral_sub hQ h0]

  unfold h3PreterminalTailCanonicalWeakVorticityXPairingOnElapsed
  simp only [
    h3EndpointElapsedZero_coe,
    add_zero
  ]

/-- The time integral of the compactly tested y-vorticity temporal derivative
is exactly the increment of the old y-vorticity weak pairing. -/
theorem intervalIntegral_h3PreterminalWeakVorticityYTemporalDerivative_eq_pairing_sub_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
        (u := u) (t := t) ψ q
      -
    h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
        (u := u) (t := t) ψ
        (h3EndpointElapsedZero q) := by
  have hSwap :=
    intervalIntegral_h3PreterminalWeakVorticityYTemporalDerivative_swap_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ q

  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  have hSlices :=
    hShort.2.1.prod_left_ae

  rw [hSwap]

  have hFTCae :
      ∀ᵐ x : Point3 ∂volume,
        (∫ r in (0 : ℝ)..(q : ℝ),
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
              hNS (t + r) x))
          =
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityY
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x)
          -
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityY
              (logSpaceTimeVectorField u)
              t
              x) := by
    filter_upwards [hSlices] with x hx
    exact
      intervalIntegral_h3LoggedPreterminalVorticityYTemporalDerivative_eq_sub
        hNS ht hEnd ψ q x hx

  rw [integral_congr_ae hFTCae]

  have hQ :=
    h3PreterminalTailCanonical_test_mul_realVorticityY_integrable
      hNS ht hEnd hTail ψ q

  have h0Raw :=
    h3PreterminalTailCanonical_test_mul_realVorticityY_integrable
      hNS ht hEnd hTail ψ
      (h3EndpointElapsedZero q)

  have h0 :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityY
              (logSpaceTimeVectorField u)
              t
              x))
        (volume : Measure Point3) := by
    simpa only [
      h3EndpointElapsedZero_coe,
      add_zero
    ] using h0Raw

  rw [integral_sub hQ h0]

  unfold h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
  simp only [
    h3EndpointElapsedZero_coe,
    add_zero
  ]

/-- The time integral of the compactly tested z-vorticity temporal derivative
is exactly the increment of the old z-vorticity weak pairing. -/
theorem intervalIntegral_h3PreterminalWeakVorticityZTemporalDerivative_eq_pairing_sub_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    h3PreterminalTailCanonicalWeakVorticityZPairingOnElapsed
        (u := u) (t := t) ψ q
      -
    h3PreterminalTailCanonicalWeakVorticityZPairingOnElapsed
        (u := u) (t := t) ψ
        (h3EndpointElapsedZero q) := by
  have hSwap :=
    intervalIntegral_h3PreterminalWeakVorticityZTemporalDerivative_swap_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ q

  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  have hSlices :=
    hShort.2.2.prod_left_ae

  rw [hSwap]

  have hFTCae :
      ∀ᵐ x : Point3 ∂volume,
        (∫ r in (0 : ℝ)..(q : ℝ),
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
              hNS (t + r) x))
          =
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityZ
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x)
          -
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityZ
              (logSpaceTimeVectorField u)
              t
              x) := by
    filter_upwards [hSlices] with x hx
    exact
      intervalIntegral_h3LoggedPreterminalVorticityZTemporalDerivative_eq_sub
        hNS ht hEnd ψ q x hx

  rw [integral_congr_ae hFTCae]

  have hQ :=
    h3PreterminalTailCanonical_test_mul_realVorticityZ_integrable
      hNS ht hEnd hTail ψ q

  have h0Raw :=
    h3PreterminalTailCanonical_test_mul_realVorticityZ_integrable
      hNS ht hEnd hTail ψ
      (h3EndpointElapsedZero q)

  have h0 :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityZ
              (logSpaceTimeVectorField u)
              t
              x))
        (volume : Measure Point3) := by
    simpa only [
      h3EndpointElapsedZero_coe,
      add_zero
    ] using h0Raw

  rw [integral_sub hQ h0]

  unfold h3PreterminalTailCanonicalWeakVorticityZPairingOnElapsed
  simp only [
    h3EndpointElapsedZero_coe,
    add_zero
  ]

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Fresh.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Cocycle
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Spectral.Duhamel.Coordinate.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected.Second.Coordinate.Duhamel

/-!
# Classicalization: spectral second-Fréchet fresh quotient

The literal retarded fresh Hessian quotient is already closed:

    h⁻¹ • ∫ₜ^{t+h} D²K(t+h,s,x)[e_b,e_a] ds
      ⟶
    D²N(W(t),W(t))(x)[e_a,e_b].

The quotient split, however, contains the second Fréchet derivative of the
actual shifted spectral H³ Duhamel state.  This file identifies those two
objects.

We deliberately avoid asserting a generic bounded Hessian-evaluation map on
arbitrary H³ states.  The exact selected cocycle has already shown that this
particular fresh remainder is spatially C².

The existing generic spectral first-coordinate bridge identifies

    (D Fresh(y)) e_b

with the translated retarded first-derivative integral.  We differentiate that
identity once more in the outer `e_a` direction.  The short source-time
integral is handled by the same dominated parametric-integral argument used in
the complete selected Hessian construction, restricted from `(0,t+h)` to the
fresh interval `(t,t+h)`.

The project's raw second-coordinate multiplier is symmetric in its two
coordinate symbols, so the resulting `(b,a)` coordinate is exactly the
`[e_a,e_b]` iterated-Fréchet coordinate represented in the fresh endpoint
theorem.

Consequently the normalized Hessian coordinate of the *actual spectral fresh
remainder* has the already-closed instantaneous forcing limit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondFrechetFreshSpectralQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The two mixed coordinate symbols commute, hence the fixed-lag mixed second
representative is symmetric in its coordinate indices. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_swap
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ U V i a b x
      =
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ U V i b a x := by
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
  apply congrArg
    (fun F : H3FourierPoint3 → ℂ =>
      FourierTransformInv.fourierInv F x)
  funext ξ
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
  ring

/-- Symmetry of the mixed second-coordinate multiplier along an arbitrary
retarded path. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_swap
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i a b : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) :
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν t U V i a b x s
      =
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν t U V i b a x s := by
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
  exact
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_swap
      ν (t - s) (U s) (V s) i a b x

/-- Differentiating the translated fresh first-coordinate retarded integral in
one further canonical direction gives the corresponding short-interval mixed
second-coordinate integral. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFreshFirstDerivativeIntegral_hasDerivAt_secondCoordinate
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (hthR : t + h ≤ h3FinHeatLerayRestartRadius ν A)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ek : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 k)
    HasDerivAt
      (fun r : ℝ =>
        ∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν (t + h) W W i j (x + r • ek) s)
      (∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν (t + h) W W i j k x s)
      0 := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let T : ℝ := t + h

  let ek : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 k)

  let F : ℝ → ℝ → ℂ :=
    fun r s =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν T W W i j (x + r • ek) s

  let F' : ℝ → ℝ → ℂ :=
    fun r s =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν T W W i j k (x + r • ek) s

  let bound : ℝ → ℝ :=
    h3SelectedSecondCoordinateDerivativePathMajorant
      ν A T hν U₀ hA hU₀ i

  have hT : 0 < T := by
    dsimp only [T]
    linarith

  have htT : t ≤ T := by
    dsimp only [T]
    linarith

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hWbound : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hFreshSubset :
      Set.Ioo t T ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_trans ht hs.1, hs.2⟩

  have hFInt :
      ∀ r : ℝ,
        Integrable
          (F r)
          (volume.restrict (Set.Ioo t T)) := by
    intro r

    have hLong :
        IntegrableOn
          (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν T W W i j (x + r • ek))
          (Set.Ioo (0 : ℝ) T)
          volume := by
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
      exact
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_intervalIntegrable_of_continuous
          hν hT.le h2A h2A
          W W hWcont hWcont
          (fun s _hs => hWbound s)
          (fun s _hs => hWbound s)
          i j (x + r • ek)

    exact hLong.mono_set hFreshSubset

  have hFMeas :
      ∀ᶠ r : ℝ in 𝓝 0,
        AEStronglyMeasurable
          (F r)
          (volume.restrict (Set.Ioo t T)) :=
    Filter.Eventually.of_forall fun r =>
      (hFInt r).aestronglyMeasurable

  have hF0Int :
      Integrable
        (F 0)
        (volume.restrict (Set.Ioo t T)) :=
    hFInt 0

  have hF'0Int :
      Integrable
        (F' 0)
        (volume.restrict (Set.Ioo t T)) := by
    have hLong :
        IntegrableOn
          (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
            ν T W W i j k x)
          (Set.Ioo (0 : ℝ) T)
          volume :=
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_integrableOn_Ioo
        hν U₀ hA hU₀ hT hthR i j k x

    have hShort :=
      hLong.mono_set hFreshSubset

    change
      IntegrableOn
        (F' 0)
        (Set.Ioo t T)
        volume
    simpa only [F', zero_smul, add_zero] using hShort

  have hF'0Meas :
      AEStronglyMeasurable
        (F' 0)
        (volume.restrict (Set.Ioo t T)) :=
    hF'0Int.aestronglyMeasurable

  have hBoundInt :
      Integrable
        bound
        (volume.restrict (Set.Ioo t T)) := by
    have hLong :
        IntegrableOn
          (h3SelectedSecondCoordinateDerivativePathMajorant
            ν A T hν U₀ hA hU₀ i)
          (Set.Ioo (0 : ℝ) T)
          volume := by
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
      exact
        h3SelectedSecondCoordinateDerivativePathMajorant_intervalIntegrable
          hν U₀ hA hU₀ hT hthR i

    exact hLong.mono_set hFreshSubset

  have hBound :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo t T)),
        ∀ r ∈ (Set.univ : Set ℝ),
          ‖F' r s‖ ≤ bound s := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro r hr
    dsimp only [F', bound]
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_le_majorant
        hν U₀ hA hU₀ hs.2 i j k (x + r • ek)

  have hDiff :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo t T)),
        ∀ r ∈ (Set.univ : Set ℝ),
          HasDerivAt (F · s) (F' r s) r := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro r hr
    dsimp only [F, F']
    unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
    simpa [ek] using
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_hasDerivAt_secondCoordinate_at
        hν (sub_pos.mpr hs.2) (W s) (W s) i j k x r)

  have hIntegral :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := (Set.univ : Set ℝ))
      (F := F)
      (F' := F')
      (x₀ := (0 : ℝ))
      (bound := bound)
      (μ := volume.restrict (Set.Ioo t T))
      Filter.univ_mem
      hFMeas
      hF0Int
      hF'0Meas
      hBound
      hBoundInt
      hDiff).2

  have hValueIntegral (r : ℝ) :
      (∫ s : ℝ,
          F r s
          ∂(volume.restrict (Set.Ioo t T)))
        =
      ∫ s in t..T,
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν T W W i j (x + r • ek) s := by
    rw [intervalIntegral.integral_of_le htT]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  have hDerivativeIntegral :
      (∫ s : ℝ,
          F' 0 s
          ∂(volume.restrict (Set.Ioo t T)))
        =
      ∫ s in t..T,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν T W W i j k x s := by
    rw [intervalIntegral.integral_of_le htT]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    simp [F', ek]

  change
    HasDerivAt
      (fun r : ℝ =>
        ∫ s in t..T,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν T W W i j (x + r • ek) s)
      (∫ s in t..T,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν T W W i j k x s)
      0

  have hValueFunction :
      (fun r : ℝ =>
        ∫ s in t..T,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν T W W i j (x + r • ek) s)
        =
      (fun r : ℝ =>
        ∫ s : ℝ,
          F r s
          ∂(volume.restrict (Set.Ioo t T))) := by
    funext r
    exact (hValueIntegral r).symm

  rw [hValueFunction]
  rw [← hDerivativeIntegral]
  exact hIntegral

/-- For every positive increment staying inside the restart interval, the
ordered second Fréchet coordinate of the actual shifted spectral fresh Duhamel
state is exactly the literal translated retarded Hessian integral. -/
theorem h3SelectedDuhamelFresh_secondFrechet_coordinate_eq_intervalIntegral
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (hthR : t + h ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let Dfresh : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel
        ν h hν
        (fun r => W (r + t))
        (fun r => W (r + t))
        i
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative Dfresh)
        x
        ![ea, eb]
      =
    ∫ s in t..t + h,
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
        ν (t + h) W W i x s eb ea := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Ushift : ℝ → H3SpectralFinVectorState :=
    fun r => W (r + t)

  let Dfresh : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν h hν Ushift Ushift i

  let Fresh : H3FourierPoint3 → ℂ :=
    h3SpectralScalarC1Representative Dfresh

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hWbound :
      ∀ r : ℝ, ‖W r‖ ≤ 2 * A := by
    intro r
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ r

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hShiftCont : Continuous Ushift := by
    dsimp only [Ushift]
    exact
      hWcont.comp
        (continuous_id.add continuous_const)

  have hShiftBound :
      ∀ r : ℝ, ‖Ushift r‖ ≤ 2 * A := by
    intro r
    dsimp only [Ushift]
    exact hWbound (r + t)

  have hFreshC2 :
      ContDiff ℝ 2 Fresh := by
    dsimp only [Fresh, Dfresh, Ushift, W]
    exact
      h3SelectedDuhamelFresh_C1Representative_contDiff_two
        hν U₀ hA hU₀ ht hh hthR i

  have hFreshC2' :
      ContDiff ℝ (1 + 1) Fresh := by
    convert hFreshC2 using 1 <;> norm_num

  have hfdC1 :
      ContDiff ℝ 1 (fderiv ℝ Fresh) := by
    exact
      (contDiff_succ_iff_fderiv.mp hFreshC2').2.2

  have hfdDiffAt :
      DifferentiableAt ℝ (fderiv ℝ Fresh) x :=
    hfdC1.differentiable_one.differentiableAt

  have hFirstEq
      (y : H3FourierPoint3) :
      (fderiv ℝ Fresh y) eb
        =
      ∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν (t + h) W W i b y s := by
    have hSpec :=
      h3SpectralFinHeatLerayDuhamel_C1_fderiv_coordinate_eq_intervalIntegral
        hν hh.le h2A h2A
        Ushift Ushift
        hShiftCont hShiftCont
        hShiftBound hShiftBound
        i b y

    let P : ℝ → ℂ :=
      fun s =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν (t + h) W W i b y s

    have hPoint :
        ∀ r : ℝ,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
              ν h Ushift Ushift i b y r
            =
          P (r + t) := by
      intro r
      dsimp only [P, Ushift]
      unfold
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
      congr 1 <;> ring

    have hTranslate :
        (∫ r in (0 : ℝ)..h,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν h Ushift Ushift i b y r)
          =
        ∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν (t + h) W W i b y s := by
      calc
        (∫ r in (0 : ℝ)..h,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν h Ushift Ushift i b y r)
            =
          ∫ r in (0 : ℝ)..h, P (r + t) := by
            apply intervalIntegral.integral_congr_uIoo
            intro r hr
            exact hPoint r
        _ =
          ∫ s in (0 : ℝ) + t..h + t, P s := by
            rw [intervalIntegral.integral_comp_add_right]
        _ =
          ∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
              ν (t + h) W W i b y s := by
            dsimp only [P]
            congr 1 <;> ring

    dsimp only [Fresh, Dfresh, ea, eb] at hSpec ⊢
    exact hSpec.trans hTranslate

  have hEvalFDeriv :
      HasFDerivAt
        (fun y : H3FourierPoint3 => (fderiv ℝ Fresh y) eb)
        ((fderiv ℝ (fderiv ℝ Fresh) x).flip eb)
        x := by
    have h :=
      hfdDiffAt.hasFDerivAt.clm_apply
        (hasFDerivAt_const eb x)
    simpa using h

  have hEvalLine :
      HasDerivAt
        (fun r : ℝ =>
          (fderiv ℝ Fresh (x + r • ea)) eb)
        ((fderiv ℝ (fderiv ℝ Fresh) x) ea eb)
        0 := by
    have hLine := hEvalFDeriv.hasLineDerivAt ea
    change
      HasDerivAt
        (fun r : ℝ =>
          (fderiv ℝ Fresh (x + r • ea)) eb)
        ((fderiv ℝ (fderiv ℝ Fresh) x) ea eb)
        0
      at hLine
    exact hLine

  have hEvalLine' :
      HasDerivAt
        (fun r : ℝ =>
          ∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
              ν (t + h) W W i b (x + r • ea) s)
        ((fderiv ℝ (fderiv ℝ Fresh) x) ea eb)
        0 := by
    convert hEvalLine using 1
    funext r
    exact (hFirstEq (x + r • ea)).symm

  have hMixed :
      HasDerivAt
        (fun r : ℝ =>
          ∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
              ν (t + h) W W i b (x + r • ea) s)
        (∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
            ν (t + h) W W i b a x s)
        0 := by
    dsimp only [ea]
    exact
      h3RawFinLerayOuterProductDivergenceHeatFreshFirstDerivativeIntegral_hasDerivAt_secondCoordinate
        hν U₀ hA hU₀ ht hh hthR i b a x

  have hNested :
      ((fderiv ℝ (fderiv ℝ Fresh) x) ea eb)
        =
      ∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν (t + h) W W i b a x s :=
    hEvalLine'.unique hMixed

  have hSwapIntegral :
      (∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν (t + h) W W i b a x s)
        =
      ∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν (t + h) W W i a b x s := by
    apply intervalIntegral.integral_congr_uIoo
    intro s hs
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_swap
        ν (t + h) W W i b a x s

  have hAxisIntegral :
      (∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν (t + h) W W i a b x s)
        =
      ∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
          ν (t + h) W W i x s eb ea := by
    apply intervalIntegral.integral_congr_uIoo
    intro s hs
    dsimp only [ea, eb]
    exact
      (h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_axis_axis
        ν (t + h) W W i a b x s).symm

  change
    iteratedFDeriv ℝ 2 Fresh x ![ea, eb]
      =
    ∫ s in t..t + h,
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
        ν (t + h) W W i x s eb ea

  rw [iteratedFDeriv_two_apply]

  simpa only [
    Matrix.cons_val_zero,
    Matrix.cons_val_one,
    Matrix.head_cons,
    Matrix.tail_cons
  ] using
    hNested.trans (hSwapIntegral.trans hAxisIntegral)

/-- The normalized ordered Hessian coordinate of the actual shifted spectral
fresh Duhamel remainder converges from the right to the instantaneous forcing
Hessian coordinate. -/
theorem tendsto_inv_smul_h3SelectedDuhamelFresh_secondFrechet_coordinate_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν h hν
                (fun r => W (r + t))
                (fun r => W (r + t))
                i))
            x
            ![ea, eb])
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x
          ![ea, eb])) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  have hLiteral :=
    tendsto_inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechet_selectedRestart_zero_right
      hν U₀ hA hU₀ ht htR i a b x

  have hLiteral' :
      Tendsto
        (fun h : ℝ =>
          h⁻¹ •
            (∫ s in t..t + h,
              h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
                ν (t + h) W W i x s eb ea))
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝
          (iteratedFDeriv ℝ 2
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            x
            ![ea, eb])) := by
    simpa only [W, ea, eb] using hLiteral

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  have hGap :
      0 < R - t := by
    dsimp only [R]
    linarith

  have hSmall :
      Set.Iio (R - t) ∈
        (𝓝[Set.Ioi (0 : ℝ)] 0) := by
    exact
      mem_inf_of_left
        (Iio_mem_nhds hGap)

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν h hν
                (fun r => W (r + t))
                (fun r => W (r + t))
                i))
            x
            ![ea, eb])
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
              ν (t + h) W W i x s eb ea)) := by
    filter_upwards
      [self_mem_nhdsWithin, hSmall]
      with h hh hsmall

    have hthR :
        t + h ≤
          h3FinHeatLerayRestartRadius ν A := by
      dsimp only [R] at hsmall
      change h < h3FinHeatLerayRestartRadius ν A - t at hsmall
      linarith

    have hFresh :=
      h3SelectedDuhamelFresh_secondFrechet_coordinate_eq_intervalIntegral
        hν U₀ hA hU₀ ht hh hthR i a b x

    dsimp only [W, ea, eb] at hFresh
    rw [hFresh]

  exact
    Tendsto.congr'
      hEq.symm
      hLiteral'

end

end Euclidean
end Bridge
end PrimeTensor

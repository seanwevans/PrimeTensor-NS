import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelFirstFrechetRightDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelFirstFrechetTimeCandidateContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.FDerivCoordinateCLM
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Classicalization: ordinary time derivative of the selected Duhamel first Fréchet derivative

The selected Duhamel first spatial Fréchet derivative now has the canonical
right derivative at every strict positive interior restart time:

    HasDerivWithinAt Dₐ Gₐ(t) (Ioi t) t.

The candidate `Gₐ` is already continuous on that interior interval.  To use
the same right-derivative FTC upgrade previously used at zeroth spatial order,
we also need ordinary continuity of `Dₐ`.

That continuity is obtained without a new estimate.  The H³-valued spectral
Duhamel map is already continuous on nonnegative physical time for globally
continuous bounded inputs.  Near a positive real time, composing with
`Real.toNNReal` is locally the identity.  Projecting to component `i` and
applying the bounded H³ coordinate derivative evaluation functional therefore
gives continuity of `Dₐ`.

With continuity of both `Dₐ` and `Gₐ` available on a compact interior window,
FTC-2 reconstructs `Dₐ` from the integral of `Gₐ`, and FTC-1 differentiates
that reconstruction ordinarily at the target time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetOrdinaryTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- One coordinate evaluation of the selected spectral Duhamel first spatial
Fréchet derivative is ordinarily continuous at every strict positive interior
restart time. -/
theorem h3SelectedDuhamel_C1_fderiv_coordinate_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    ContinuousAt
      (fun r : ℝ =>
        (fderiv ℝ
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν r hν W W i))
            x) ea)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let E : H3SpectralScalarState →L[ℂ] ℂ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCLM a x

  let Dnn : ℝ≥0 → H3SpectralFinVectorState :=
    fun q =>
      h3SpectralFinHeatLerayDuhamel
        ν (q : ℝ) hν W W

  let Q : ℝ → ℂ :=
    fun r =>
      E ((Dnn (Real.toNNReal r)) i)

  let D : ℝ → ℂ :=
    fun r =>
      (fderiv ℝ
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i))
          x) ea

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

  have hDnnCont : Continuous Dnn := by
    dsimp only [Dnn]
    exact
      continuous_h3SpectralFinHeatLerayDuhamel_nnreal
        hν h2A h2A W W
        hWcont hWcont
        hWbound hWbound

  have hCoordCont :
      Continuous
        (fun q : ℝ≥0 => (Dnn q) i) :=
    (continuous_apply i).comp hDnnCont

  have hQCont : Continuous Q := by
    dsimp only [Q]
    exact
      E.continuous.comp
        (hCoordCont.comp continuous_real_toNNReal)

  have hPos :
      Set.Ioi (0 : ℝ) ∈ 𝓝 s :=
    Ioi_mem_nhds hs

  have hEq :
      Q =ᶠ[𝓝 s] D := by
    filter_upwards [hPos] with r hr
    dsimp only [Q, D, Dnn, E]
    rw [Real.coe_toNNReal r hr.le]
    rw [h3SpectralScalarC1CoordinateDerivativeEvaluationCLM_apply]

  have hAt :
      Q s = D s :=
    hEq.self_of_nhds

  change
    Tendsto D (𝓝 s) (𝓝 (D s))

  rw [← hAt]

  exact
    hQCont.continuousAt.congr' hEq

/-- At every strict positive interior restart time, one coordinate evaluation
of the selected Duhamel first spatial Fréchet derivative has an ordinary time
derivative equal to the continuous third-trace-plus-forcing candidate. -/
theorem h3SelectedDuhamel_C1_fderiv_coordinate_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    HasDerivAt
      (fun r : ℝ =>
        (fderiv ℝ
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν r hν W W i))
            x) ea)
      ((ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 3
              (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                ν t W W i)
              x
              ![
                ea,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        +
      (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x) ea)
      t := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let α : ℝ := t / 2
  let β : ℝ := (t + R) / 2

  let D : ℝ → ℂ :=
    fun r =>
      (fderiv ℝ
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i))
          x) ea

  let G : ℝ → ℂ :=
    fun r =>
      (ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 3
              (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                ν r W W i)
              x
              ![
                ea,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        +
      (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W r) (W r) i)
          x) ea

  have htR' : t < R := by
    simpa only [R] using htR

  have hα0 : 0 < α := by
    dsimp only [α]
    linarith

  have hαt : α < t := by
    dsimp only [α]
    linarith

  have htβ : t < β := by
    dsimp only [β]
    linarith

  have hβR : β < R := by
    dsimp only [β]
    linarith

  have hαβ : α ≤ β :=
    (hαt.trans htβ).le

  have hDAt :
      ∀ y ∈ Set.Icc α β,
        ContinuousAt D y := by
    intro y hy

    have hy0 : 0 < y :=
      lt_of_lt_of_le hα0 hy.1

    have hyR : y < R :=
      lt_of_le_of_lt hy.2 hβR

    dsimp only [D, W, ea]

    exact
      h3SelectedDuhamel_C1_fderiv_coordinate_continuousAt_time
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i a x

  have hDContinuous :
      ContinuousOn D (Set.Icc α β) := by
    intro y hy
    exact
      (hDAt y hy).continuousWithinAt

  have hGAt :
      ∀ y ∈ Set.Icc α β,
        ContinuousAt G y := by
    intro y hy

    have hy0 : 0 < y :=
      lt_of_lt_of_le hα0 hy.1

    have hyR : y < R :=
      lt_of_le_of_lt hy.2 hβR

    dsimp only [G, W, ea]

    exact
      h3SelectedDuhamel_firstFrechet_timeDerivativeCandidate_coordinate_continuousAt
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i a x

  have hGContinuous :
      ContinuousOn G (Set.Icc α β) := by
    intro y hy
    exact
      (hGAt y hy).continuousWithinAt

  have hGIntervalIntegrable :
      IntervalIntegrable G volume α β := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hαβ]
    exact hGContinuous

  have hRightDerivative :
      ∀ y ∈ Set.Ioo α β,
        HasDerivWithinAt
          D
          (G y)
          (Set.Ioi y)
          y := by
    intro y hy

    have hy0 : 0 < y :=
      lt_trans hα0 hy.1

    have hyR : y < R :=
      lt_trans hy.2 hβR

    dsimp only [D, G, W, ea]

    exact
      h3SelectedDuhamel_C1_fderiv_coordinate_hasDerivWithinAt_right
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i a x

  have hFTC
      (y : ℝ)
      (hy : y ∈ Set.Icc α β) :
      (∫ z in α..y, G z)
        =
      D y - D α := by
    have hαy : α ≤ y :=
      hy.1

    have hSub :
        Set.Icc α y ⊆ Set.Icc α β := by
      intro z hz
      exact
        ⟨hz.1, hz.2.trans hy.2⟩

    have hDContinuousAy :
        ContinuousOn D (Set.Icc α y) :=
      hDContinuous.mono hSub

    have hGContinuousAy :
        ContinuousOn G (Set.Icc α y) :=
      hGContinuous.mono hSub

    have hGIntegrableAy :
        IntervalIntegrable G volume α y := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hαy]
      exact hGContinuousAy

    have hRightAy :
        ∀ z ∈ Set.Ioo α y,
          HasDerivWithinAt
            D
            (G z)
            (Set.Ioi z)
            z := by
      intro z hz
      exact
        hRightDerivative z
          ⟨hz.1, lt_of_lt_of_le hz.2 hy.2⟩

    exact
      intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
        hαy
        hDContinuousAy
        hRightAy
        hGIntegrableAy

  let J : ℝ → ℂ :=
    fun y =>
      D α + ∫ z in α..y, G z

  have hJEq
      (y : ℝ)
      (hy : y ∈ Set.Icc α β) :
      J y = D y := by
    dsimp only [J]
    rw [hFTC y hy]
    abel

  have hGIntegrableAt :
      IntervalIntegrable G volume α t := by
    have hSub :
        Set.Icc α t ⊆ Set.Icc α β := by
      intro z hz
      exact
        ⟨hz.1, hz.2.trans htβ.le⟩

    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hαt.le]
    exact hGContinuous.mono hSub

  have hGMeasurableAt :
      StronglyMeasurableAtFilter
        G
        (𝓝 t)
        (volume : Measure ℝ) := by
    exact
      ContinuousAt.stronglyMeasurableAtFilter
        (μ := (volume : Measure ℝ))
        isOpen_Ioo
        (fun y hy =>
          hGAt y ⟨hy.1.le, hy.2.le⟩)
        t
        ⟨hαt, htβ⟩

  have hIntegralDerivative :
      HasDerivAt
        (fun y : ℝ =>
          ∫ z in α..y, G z)
        (G t)
        t :=
    intervalIntegral.integral_hasDerivAt_right
      hGIntegrableAt
      hGMeasurableAt
      (hGAt t ⟨hαt.le, htβ.le⟩)

  have hJDerivative :
      HasDerivAt J (G t) t := by
    dsimp only [J]
    exact
      hIntegralDerivative.const_add (D α)

  have hIccNeighborhood :
      Set.Icc α β ∈ 𝓝 t :=
    Icc_mem_nhds hαt htβ

  have hEventuallyEq :
      D =ᶠ[𝓝 t] J := by
    filter_upwards [hIccNeighborhood] with y hy
    exact
      (hJEq y hy).symm

  have hDDerivative :
      HasDerivAt D (G t) t :=
    hJDerivative.congr_of_eventuallyEq hEventuallyEq

  dsimp only [D, G, W, ea] at hDDerivative ⊢
  exact hDDerivative

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Right.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Derivative.Candidate.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Time.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Classicalization: ordinary time derivative of the selected Duhamel third Fréchet derivative

The selected Duhamel third spatial Fréchet derivative now has a canonical
right derivative at every strict positive interior restart time,

    HasDerivWithinAt D_abc G_abc(t) (Ioi t) t,

and the complete candidate

    G_abc(t)
      =
    ν * Σ_k D⁵D(t,x)[e_a,e_b,e_c,e_k,e_k]
      + D³N(W(t),W(t))(x)[e_a,e_b,e_c]

is time-continuous.

The literal selected Duhamel third jet is already ordinarily time-continuous.
We first transport that continuity to the canonical spectral Duhamel
representative.  On a compact interior window, continuity of the coordinate
path and candidate plus the right derivative identity allow the standard
one-sided FTC reconstruction.  The reconstructed integral path has an
ordinary derivative at the base time, and local equality transfers that
derivative back to the canonical Duhamel coordinate.

No new Fourier estimate or endpoint argument is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetOrdinaryTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

attribute [local instance 1100] NormedSpace.complexToReal

/-- One ordered canonical-coordinate evaluation of the canonical spectral
selected-Duhamel third spatial Fréchet derivative is ordinarily continuous in
time. -/
theorem h3SelectedDuhamel_C1_thirdFrechet_coordinate_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let ec : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 c)
    let m : Fin 3 → H3FourierPoint3 :=
      ![ea, eb, ec]
    ContinuousAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i))
          x m)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)

  let m : Fin 3 → H3FourierPoint3 :=
    ![ea, eb, ec]

  let D : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν r hν W W i))
        x m

  let Q : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν r W W i)
        x m

  have hQ :
      ContinuousAt Q s := by
    dsimp only [Q, W, ea, eb, ec, m]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_thirdFrechet_coordinate_eval_continuousAt_time
        hν U₀ hA hU₀ hs hsR i a b c x

  have hInterior :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEq :
      D =ᶠ[𝓝 s] Q := by
    filter_upwards [hInterior] with r hr

    have hGeneric :=
      h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
        hν U₀ hA hU₀ hr.1 i

    have hClassical :=
      h3SelectedDuhamelC1Representative_eq_C3Duhamel
        hν U₀ hA hU₀ hr.1 hr.2.le i

    dsimp only at hGeneric hClassical

    have hFunction :
        h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i)
          =
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν r W W i := by
      rw [← hGeneric]
      exact hClassical

    have hOperator :=
      congrArg
        (fun f =>
          iteratedFDeriv ℝ 3 f x)
        hFunction

    have hEval :=
      congrArg
        (fun T => T m)
        hOperator

    dsimp only [D, Q]
    exact hEval

  change ContinuousAt D s
  exact hQ.congr_of_eventuallyEq hEq

/-- At every strict positive interior restart time, one ordered canonical
coordinate evaluation of the selected Duhamel third spatial Fréchet derivative
has an ordinary time derivative equal to the continuous
fifth-trace-plus-forcing-third-derivative candidate. -/
theorem h3SelectedDuhamel_C1_thirdFrechet_coordinate_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let ec : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 c)
    let m : Fin 3 → H3FourierPoint3 :=
      ![ea, eb, ec]
    HasDerivAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i))
          x m)
      ((ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 5
              (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                ν t W W i)
              x
              ![
                ea,
                eb,
                ec,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        +
      iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        x m)
      t := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)

  let m : Fin 3 → H3FourierPoint3 :=
    ![ea, eb, ec]

  let α : ℝ := t / 2
  let β : ℝ := (t + R) / 2

  let D : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν r hν W W i))
        x m

  let G : ℝ → ℂ :=
    fun r =>
      (ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 5
              (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                ν r W W i)
              x
              ![
                ea,
                eb,
                ec,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        +
      iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W r) (W r) i)
        x m

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

    dsimp only [D, W, ea, eb, ec, m]

    exact
      h3SelectedDuhamel_C1_thirdFrechet_coordinate_continuousAt_time
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i a b c x

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

    dsimp only [G, W, ea, eb, ec, m]

    exact
      h3SelectedDuhamel_C1_thirdFrechet_coordinate_derivativeCandidate_continuousAt_time
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i a b c x

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

    dsimp only [D, G, W, ea, eb, ec, m]

    exact
      h3SelectedDuhamel_C1_thirdFrechet_coordinate_hasDerivWithinAt_right
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i a b c x

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

  dsimp only [D, G, W, ea, eb, ec, m] at hDDerivative ⊢
  exact hDDerivative

end

end Euclidean
end Bridge
end PrimeTensor

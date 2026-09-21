import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Right.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Derivative.Candidate.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quadratic.Second.Frechet.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Hessian.Trace.Mild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Second.Coordinate.Time.Derivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Classicalization: ordinary time derivative of the selected Duhamel second Fréchet derivative

The selected Duhamel second spatial Fréchet derivative now has a canonical
right derivative at every strict positive interior restart time,

    HasDerivWithinAt D_ab G_ab(t) (Ioi t) t,

and the complete candidate

    G_ab(t)
      =
    ν * Σ_k D⁴D(t,x)[e_a,e_b,e_k,e_k]
      + D²N(W(t),W(t))(x)[e_a,e_b]

is time-continuous.

To apply the same FTC upgrade already used at spatial orders zero and one, this
file first proves ordinary time continuity of the Duhamel Hessian coordinate.
The twice-spatially differentiated mild identity gives

    D²D = D²Heat - D²Selected.

The heat Hessian coordinate is continuous because its positive-time path has an
ordinary derivative, while the selected Hessian coordinate is continuous by the
quadratic classicalization layer.  The explicit selected-Duhamel
reconstruction is then identified with the canonical spectral Duhamel
representative.

With continuity of the Hessian coordinate and its derivative candidate on a
compact interior window, FTC-2 reconstructs the Hessian coordinate from the
candidate and FTC-1 upgrades the right derivative to an ordinary derivative.

No new Fourier estimate or endpoint argument is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondFrechetOrdinaryTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

attribute [local instance 1100] NormedSpace.complexToReal

/-- Ordered-coordinate form of the twice-differentiated selected mild
identity:

    D² Duhamel[e_a,e_b] = D² Heat[e_a,e_b] - D² Selected[e_a,e_b].
-/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_two_coordinate_eval_eq_heat_sub_selected
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let m : Fin 2 → H3FourierPoint3 :=
      ![ea, eb]
    iteratedFDeriv ℝ 2
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x m
      =
    iteratedFDeriv ℝ 2
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x m
      -
    iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t i))
        x m := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let m : Fin 2 → H3FourierPoint3 :=
    ![ea, eb]

  have hMild :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
      hν U₀ hA hU₀ ht htR i

  dsimp only at hMild

  have hHeatC2 :
      ContDiff ℝ 2
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i)) :=
    (h3SpectralScalarHeatC3Representative_contDiff_three
      hν ht (U₀ i)).of_le (by norm_num)

  have hDuhamelC2 :
      ContDiff ℝ 2
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i) := by
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_contDiff_two
        hν U₀ hA hU₀ ht htR i

  have hSub :=
    iteratedFDeriv_sub_apply
      (𝕜 := ℝ)
      (i := 2)
      (x := x)
      hHeatC2.contDiffAt
      hDuhamelC2.contDiffAt

  have hSubEval :=
    congrArg
      (fun T => T m)
      hSub

  have hMildSecond :=
    congrArg
      (fun f =>
        iteratedFDeriv ℝ 2 f x)
      hMild

  have hMildSecondEval :=
    congrArg
      (fun T => T m)
      hMildSecond

  rw [hSubEval] at hMildSecondEval

  change
    iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t i))
        x m
      =
    iteratedFDeriv ℝ 2
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x m
      -
    iteratedFDeriv ℝ 2
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x m
    at hMildSecondEval

  change
    iteratedFDeriv ℝ 2
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x m
      =
    iteratedFDeriv ℝ 2
        (h3SpectralScalarHeatC3Representative
          ν t (U₀ i))
        x m
      -
    iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W t i))
        x m

  rw [eq_sub_iff_add_eq]
  rw [hMildSecondEval]
  abel

/-- Every fixed ordered canonical-coordinate evaluation of the literal
selected Duhamel Hessian is time-continuous at every strict positive interior
restart time. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_secondFrechet_coordinate_eval_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let m : Fin 2 → H3FourierPoint3 :=
      ![ea, eb]
    ContinuousAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν r W W i)
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

  let m : Fin 2 → H3FourierPoint3 :=
    ![ea, eb]

  let D : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 2
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν r W W i)
        x m

  let H : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 2
        (h3SpectralScalarHeatC3Representative
          ν r (U₀ i))
        x m

  let S : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W r i))
        x m

  have hHeatNamed :
      ContinuousAt
        (fun r : ℝ =>
          h3SpectralScalarHeatSecondCoordinateRepresentative
            ν r (U₀ i) a b x)
        s :=
    (h3SpectralScalarHeatSecondCoordinateRepresentative_hasDerivAt_time
      hν hs (U₀ i) a b x).continuousAt

  have hPositive :
      Set.Ioi (0 : ℝ) ∈ 𝓝 s :=
    Ioi_mem_nhds hs

  have hHeatEq :
      H =ᶠ[𝓝 s]
        (fun r : ℝ =>
          h3SpectralScalarHeatSecondCoordinateRepresentative
            ν r (U₀ i) a b x) := by
    filter_upwards [hPositive] with r hr
    dsimp only [H, m, ea, eb]
    symm
    exact
      h3SpectralScalarHeatSecondCoordinateRepresentative_eq_iteratedFDeriv
        hν hr (U₀ i) a b x

  have hHeat :
      ContinuousAt H s :=
    hHeatNamed.congr_of_eventuallyEq hHeatEq

  have hSelected :
      ContinuousAt S s := by
    dsimp only [S, m, W, ea, eb]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_secondFrechet_eval_continuousAt
        hν U₀ hA hU₀ hs hsR i x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b)
        ]

  have hRHS :
      ContinuousAt
        (fun r : ℝ => H r - S r)
        s :=
    hHeat.sub hSelected

  have hInterior :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEq :
      D =ᶠ[𝓝 s]
        (fun r : ℝ => H r - S r) := by
    filter_upwards [hInterior] with r hr
    dsimp only [D, H, S, m, W, ea, eb]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_iteratedFDeriv_two_coordinate_eval_eq_heat_sub_selected
        hν U₀ hA hU₀ hr.1 hr.2.le i a b x

  change ContinuousAt D s
  exact hRHS.congr_of_eventuallyEq hEq

/-- One ordered canonical-coordinate evaluation of the canonical spectral
selected-Duhamel Hessian is ordinarily continuous in time. -/
theorem h3SelectedDuhamel_C1_secondFrechet_coordinate_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let m : Fin 2 → H3FourierPoint3 :=
      ![ea, eb]
    ContinuousAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 2
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

  let m : Fin 2 → H3FourierPoint3 :=
    ![ea, eb]

  let D : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν r hν W W i))
        x m

  let Q : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 2
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν r W W i)
        x m

  have hQ :
      ContinuousAt Q s := by
    dsimp only [Q, W, ea, eb, m]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_secondFrechet_coordinate_eval_continuousAt_time
        hν U₀ hA hU₀ hs hsR i a b x

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
          iteratedFDeriv ℝ 2 f x)
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
coordinate evaluation of the selected Duhamel second spatial Fréchet
derivative has an ordinary time derivative equal to the continuous
fourth-trace-plus-forcing-Hessian candidate. -/
theorem h3SelectedDuhamel_C1_secondFrechet_coordinate_hasDerivAt_time
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
    let m : Fin 2 → H3FourierPoint3 :=
      ![ea, eb]
    HasDerivAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayDuhamel
              ν r hν W W i))
          x m)
      ((ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 4
              (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                ν t W W i)
              x
              ![
                ea,
                eb,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        +
      iteratedFDeriv ℝ 2
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

  let m : Fin 2 → H3FourierPoint3 :=
    ![ea, eb]

  let α : ℝ := t / 2
  let β : ℝ := (t + R) / 2

  let D : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν r hν W W i))
        x m

  let G : ℝ → ℂ :=
    fun r =>
      (ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 4
              (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                ν r W W i)
              x
              ![
                ea,
                eb,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        +
      iteratedFDeriv ℝ 2
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

    dsimp only [D, W, ea, eb, m]

    exact
      h3SelectedDuhamel_C1_secondFrechet_coordinate_continuousAt_time
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i a b x

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

    dsimp only [G, W, ea, eb, m]

    exact
      h3SelectedDuhamel_C1_secondFrechet_coordinate_derivativeCandidate_continuousAt_time
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i a b x

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

    dsimp only [D, G, W, ea, eb, m]

    exact
      h3SelectedDuhamel_C1_secondFrechet_coordinate_hasDerivWithinAt_right
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i a b x

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

  dsimp only [D, G, W, ea, eb, m] at hDDerivative ⊢
  exact hDDerivative

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Derivative.Candidate.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Pointwise.Mild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Time.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Classicalization: ordinary time derivative of the selected classical Duhamel diagonal

The selected Duhamel diagonal already has a canonical right derivative at every
positive time up to the restart radius:

    HasDerivWithinAt D (G t) (Ioi t) t.

The preceding continuity checkpoint proves that `G` is continuous at every
strict positive interior restart time.

This file upgrades the one-sided derivative to an ordinary derivative.  Fix a
strict interior time `t` and choose

    a = t / 2,
    b = (t + R) / 2,

where `R` is the canonical restart radius.  Then

    0 < a < t < b < R.

On `[a,b]`:

* the Duhamel diagonal is continuous, by the literal pointwise mild identity
  `D = heat - selected`;
* the derivative candidate is continuous;
* the canonical right derivative exists at every interior point.

Mathlib's right-derivative FTC-2 therefore gives

    ∫_a^y G = D(y) - D(a)

for every `y ∈ [a,b]`.  Hence locally around `t`,

    D(y) = D(a) + ∫_a^y G.

FTC-1 differentiates the right-hand side ordinarily at `t`, because `G` is
continuous there.  Local equality then transfers the ordinary derivative to
the classical Duhamel diagonal.

This is the bridge from the completed one-sided Duhamel calculus to the
ordinary temporal derivative consumed by the selected velocity reduction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedDuhamelOrdinaryTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

attribute [local instance 1100] NormedSpace.complexToReal

/-- The selected classical Duhamel diagonal itself is continuous at every
strict positive interior restart time.  This follows directly from the
pointwise classical mild identity and the already-continuous heat and selected
reconstructions. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν r W W i x)
      s := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : ℝ → ℂ :=
    fun r =>
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν r W W i x

  let Q : ℝ → ℂ :=
    fun r =>
      h3SpectralScalarHeatC3Representative
          ν r (U₀ i) x
        -
      h3SpectralScalarC1Representative
          (W r i) x

  have hWContinuous : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hCoordinateContinuous :
      Continuous
        (fun r : ℝ => W r i) :=
    (continuous_apply i).comp hWContinuous

  have hSelectedContinuous :
      ContinuousAt
        (fun r : ℝ =>
          h3SpectralScalarC1Representative
            (W r i) x)
        s :=
    h3SpectralScalarC1Representative_continuousAt_of_spectral
      (fun r : ℝ => W r i)
      s
      hCoordinateContinuous.continuousAt
      x

  have hHeatContinuous :
      ContinuousAt
        (fun r : ℝ =>
          h3SpectralScalarHeatC3Representative
            ν r (U₀ i) x)
        s :=
    (h3SpectralScalarHeatC3Representative_hasDerivAt_time
      hν hs (U₀ i) x).continuousAt

  have hQContinuous :
      ContinuousAt Q s := by
    dsimp only [Q]
    exact hHeatContinuous.sub hSelectedContinuous

  have hAt :
      D s = Q s := by
    have hMild :=
      congrFun
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
          hν U₀ hA hU₀ hs hsR.le i)
        x

    change
      h3SpectralScalarC1Representative
          (W s i) x
        =
      h3SpectralScalarHeatC3Representative
          ν s (U₀ i) x
        -
      D s
      at hMild

    dsimp only [Q]
    apply (eq_sub_iff_add_eq).2
    have hSum :
        h3SpectralScalarC1Representative
              (W s i) x
            +
          D s
          =
        h3SpectralScalarHeatC3Representative
          ν s (U₀ i) x :=
      (eq_sub_iff_add_eq).1 hMild
    simpa only [add_comm] using hSum

  have hInterior :
      Set.Ioo (0 : ℝ) R ∈ 𝓝 s := by
    apply Ioo_mem_nhds
    · exact hs
    · simpa only [R] using hsR

  have hEventuallyEq :
      ∀ᶠ r in 𝓝 s,
        Q r = D r := by
    filter_upwards [hInterior] with r hr

    have hMild :=
      congrFun
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
          hν U₀ hA hU₀ hr.1
          (by
            simpa only [R] using hr.2.le)
          i)
        x

    change
      h3SpectralScalarC1Representative
          (W r i) x
        =
      h3SpectralScalarHeatC3Representative
          ν r (U₀ i) x
        -
      D r
      at hMild

    dsimp only [Q]
    symm
    apply (eq_sub_iff_add_eq).2
    have hSum :
        h3SpectralScalarC1Representative
              (W r i) x
            +
          D r
          =
        h3SpectralScalarHeatC3Representative
          ν r (U₀ i) x :=
      (eq_sub_iff_add_eq).1 hMild
    simpa only [add_comm] using hSum

  change
    Tendsto D (𝓝 s) (𝓝 (D s))

  rw [hAt]

  exact hQContinuous.congr' hEventuallyEq

/-- At every strict positive interior restart time, the selected classical
Duhamel diagonal has an ordinary derivative equal to the canonical candidate
already produced by the one-sided Duhamel calculus. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    HasDerivAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν r W W i x)
      ((ν : ℂ) *
          (∑ j : Fin 3,
            h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
              ν t W W i x
              (h3FourierAxisDirection (h3AxisOfFin3 j))
              (h3FourierAxisDirection (h3AxisOfFin3 j)))
        +
      h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i x)
      t := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let a : ℝ := t / 2
  let b : ℝ := (t + R) / 2

  let D : ℝ → ℂ :=
    fun r =>
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν r W W i x

  let G : ℝ → ℂ :=
    fun r =>
      (ν : ℂ) *
          (∑ j : Fin 3,
            h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
              ν r W W i x
              (h3FourierAxisDirection (h3AxisOfFin3 j))
              (h3FourierAxisDirection (h3AxisOfFin3 j)))
        +
      h3RawFinLerayOuterProductDivergenceC0Representative
        (W r) (W r) i x

  have htR' : t < R := by
    simpa only [R] using htR

  have ha0 : 0 < a := by
    dsimp only [a]
    linarith

  have hat : a < t := by
    dsimp only [a]
    linarith

  have htb : t < b := by
    dsimp only [b]
    linarith

  have hbR : b < R := by
    dsimp only [b]
    linarith

  have hab : a ≤ b :=
    (hat.trans htb).le

  have hDAt :
      ∀ y ∈ Set.Icc a b,
        ContinuousAt D y := by
    intro y hy

    have hy0 : 0 < y :=
      lt_of_lt_of_le ha0 hy.1

    have hyR : y < R :=
      lt_of_le_of_lt hy.2 hbR

    dsimp only [D, W]

    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_continuousAt_time
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i x

  have hDContinuous :
      ContinuousOn D (Set.Icc a b) := by
    intro y hy
    exact (hDAt y hy).continuousWithinAt

  have hGAt :
      ∀ y ∈ Set.Icc a b,
        ContinuousAt G y := by
    intro y hy

    have hy0 : 0 < y :=
      lt_of_lt_of_le ha0 hy.1

    have hyR : y < R :=
      lt_of_le_of_lt hy.2 hbR

    dsimp only [G, W]

    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_derivativeCandidate_continuousAt
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i x

  have hGContinuous :
      ContinuousOn G (Set.Icc a b) := by
    intro y hy
    exact (hGAt y hy).continuousWithinAt

  have hGIntervalIntegrable :
      IntervalIntegrable G volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hGContinuous

  have hRightDerivative :
      ∀ y ∈ Set.Ioo a b,
        HasDerivWithinAt
          D
          (G y)
          (Set.Ioi y)
          y := by
    intro y hy

    have hy0 : 0 < y :=
      lt_trans ha0 hy.1

    have hyR : y ≤ R := by
      exact
        (lt_trans hy.2 hbR).le

    dsimp only [D, G, W]

    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_hasDerivWithinAt_right
        hν U₀ hA hU₀ hy0
        (by
          simpa only [R] using hyR)
        i x

  have hFTC
      (y : ℝ)
      (hy : y ∈ Set.Icc a b) :
      (∫ z in a..y, G z)
        =
      D y - D a := by
    have hay : a ≤ y :=
      hy.1

    have hSub :
        Set.Icc a y ⊆ Set.Icc a b := by
      intro z hz
      exact
        ⟨hz.1, hz.2.trans hy.2⟩

    have hDContinuousAy :
        ContinuousOn D (Set.Icc a y) :=
      hDContinuous.mono hSub

    have hGContinuousAy :
        ContinuousOn G (Set.Icc a y) :=
      hGContinuous.mono hSub

    have hGIntegrableAy :
        IntervalIntegrable G volume a y := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hay]
      exact hGContinuousAy

    have hRightAy :
        ∀ z ∈ Set.Ioo a y,
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
        hay
        hDContinuousAy
        hRightAy
        hGIntegrableAy

  let J : ℝ → ℂ :=
    fun y =>
      D a + ∫ z in a..y, G z

  have hJEq
      (y : ℝ)
      (hy : y ∈ Set.Icc a b) :
      J y = D y := by
    dsimp only [J]
    rw [hFTC y hy]
    abel

  have hGIntegrableAt :
      IntervalIntegrable G volume a t := by
    have hSub :
        Set.Icc a t ⊆ Set.Icc a b := by
      intro z hz
      exact
        ⟨hz.1, hz.2.trans htb.le⟩

    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hat.le]
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
        ⟨hat, htb⟩

  have hIntegralDerivative :
      HasDerivAt
        (fun y : ℝ =>
          ∫ z in a..y, G z)
        (G t)
        t :=
    intervalIntegral.integral_hasDerivAt_right
      hGIntegrableAt
      hGMeasurableAt
      (hGAt t ⟨hat.le, htb.le⟩)

  have hJDerivative :
      HasDerivAt J (G t) t := by
    dsimp only [J]
    exact hIntegralDerivative.const_add (D a)

  have hIccNeighborhood :
      Set.Icc a b ∈ 𝓝 t :=
    Icc_mem_nhds hat htb

  have hEventuallyEq :
      D =ᶠ[𝓝 t] J := by
    filter_upwards [hIccNeighborhood] with y hy
    exact (hJEq y hy).symm

  have hDDerivative :
      HasDerivAt D (G t) t :=
    hJDerivative.congr_of_eventuallyEq hEventuallyEq

  dsimp only [D, G, W] at hDDerivative ⊢
  exact hDDerivative

end

end Euclidean
end Bridge
end PrimeTensor

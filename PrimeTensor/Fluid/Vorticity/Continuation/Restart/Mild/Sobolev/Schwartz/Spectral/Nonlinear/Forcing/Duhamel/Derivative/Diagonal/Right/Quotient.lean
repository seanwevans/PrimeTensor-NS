import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.Old.Source.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.Fresh.Tail.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.GeneratorIntegral

/-!
# Selected Duhamel classical diagonal right quotient

The old-source and fresh-tail right quotients are now closed independently on
the literal classical Duhamel integrand.

This file performs the remaining algebra.

For `h > 0`, interval additivity gives

    D(t+h)
      =
    ∫₀ᵗ K(t+h,s) ds
      +
    ∫ₜ^{t+h} K(t+h,s) ds.

Subtracting `D(t)`, multiplying by `h⁻¹`, and using interval-integral
linearity gives the exact identity

    h⁻¹ • (D(t+h) - D(t))
      =
    ∫₀ᵗ h⁻¹ • (K(t+h,s) - K(t,s)) ds
      +
    h⁻¹ • ∫ₜ^{t+h} K(t+h,s) ds.

The first term converges to the integrated heat generator and the second to
the instantaneous nonlinear forcing.  Hence the actual literal classical
Duhamel diagonal has the right difference quotient

    ν Δ D(t) + F(W(t),W(t)).

No Fourier interchange or dominated-convergence argument is introduced here;
all analytic work is imported from the two quotient checkpoints.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace BigOperators

noncomputable section

noncomputable local instance axisFintypeH3DuhamelDiagonalRightQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- For a positive increment, the literal selected classical Duhamel diagonal
difference quotient is exactly the sum of its fixed-old-source quotient and
fresh moving-endpoint quotient. -/
theorem inv_smul_sub_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_eq_oldSource_add_fresh
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h⁻¹ •
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν (t + h) W W i x
        -
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i x)
      =
    (∫ s in (0 : ℝ)..t,
      h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
        ν t h W i x s)
      +
    h⁻¹ •
      (∫ s in t..t + h,
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν (t + h) W W i x s) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Kplus : ℝ → ℂ :=
    fun s =>
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν (t + h) W W i x s

  let Kbase : ℝ → ℂ :=
    fun s =>
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t W W i x s

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hPlusFull :
      ContinuousOn Kplus (Set.Icc (0 : ℝ) (t + h)) := by
    dsimp only [Kplus]
    exact
      continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Icc
        (a := (0 : ℝ))
        (t := t + h)
        hν
        (by linarith)
        W W hWcont hWcont i x

  have hPlusOldCont :
      ContinuousOn Kplus (Set.Icc (0 : ℝ) t) := by
    exact
      hPlusFull.mono
        (by
          intro s hs
          exact ⟨hs.1, by linarith [hs.2, hh]⟩)

  have hPlusFreshCont :
      ContinuousOn Kplus (Set.Icc t (t + h)) := by
    exact
      hPlusFull.mono
        (by
          intro s hs
          exact ⟨ht.le.trans hs.1, hs.2⟩)

  have hBaseCont :
      ContinuousOn Kbase (Set.Icc (0 : ℝ) t) := by
    dsimp only [Kbase]
    exact
      continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Icc
        (a := (0 : ℝ))
        (t := t)
        hν
        ht
        W W hWcont hWcont i x

  have hPlusOld :
      IntervalIntegrable Kplus volume (0 : ℝ) t :=
    hPlusOldCont.intervalIntegrable_of_Icc ht.le

  have hPlusFresh :
      IntervalIntegrable Kplus volume t (t + h) :=
    hPlusFreshCont.intervalIntegrable_of_Icc
      (le_add_of_nonneg_right hh.le)

  have hBase :
      IntervalIntegrable Kbase volume (0 : ℝ) t :=
    hBaseCont.intervalIntegrable_of_Icc ht.le

  have hSplit :
      (∫ s in (0 : ℝ)..t, Kplus s)
        +
      (∫ s in t..t + h, Kplus s)
        =
      ∫ s in (0 : ℝ)..t + h, Kplus s :=
    intervalIntegral.integral_add_adjacent_intervals
      hPlusOld hPlusFresh

  have hOld :
      (∫ s in (0 : ℝ)..t,
        h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
          ν t h W i x s)
        =
      h⁻¹ •
        ((∫ s in (0 : ℝ)..t, Kplus s)
          -
        ∫ s in (0 : ℝ)..t, Kbase s) := by
    unfold h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
    dsimp only [Kplus, Kbase]
    rw [intervalIntegral.integral_smul]
    rw [intervalIntegral.integral_sub hPlusOld hBase]

  unfold h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
  dsimp only [Kplus, Kbase] at hSplit hOld ⊢

  rw [hOld]
  rw [← hSplit]

  simp only [sub_eq_add_neg, smul_add, smul_neg]
  abel

/-- The actual literal selected classical Duhamel diagonal right quotient
converges to the sum of the integrated old-history heat generator and the
instantaneous nonlinear forcing. -/
theorem tendsto_inv_smul_sub_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
              ν (t + h) W W i x
            -
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
              ν t W W i x))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        ((∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
            ν t W W i x s)
          +
        h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i x)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hOld :=
    tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient_selectedRestart_zero_right
      hν U₀ hA hU₀ ht htR i x

  have hFresh :=
    tendsto_inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshTail_selectedRestart_zero_right
      (t := t)
      hν U₀ hA hU₀ hWcont i x

  have hSum := hOld.add hFresh

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
              ν (t + h) W W i x
            -
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
              ν t W W i x))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        (∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
            ν t h W i x s)
          +
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
              ν (t + h) W W i x s)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact
      inv_smul_sub_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_eq_oldSource_add_fresh
        hν U₀ hA hU₀ ht hh i x

  dsimp only [W] at hOld hFresh hSum hEq ⊢
  exact Tendsto.congr' hEq.symm hSum

/-- Canonical form of the selected classical Duhamel right quotient: the old
history is viscosity times the trace of the already-constructed Duhamel
Hessian, and the endpoint term is the instantaneous nonlinear forcing. -/
theorem tendsto_inv_smul_sub_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_zero_right_eq_viscosity_hessianTrace_add_forcing
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
              ν (t + h) W W i x
            -
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
              ν t W W i x))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        ((ν : ℂ) *
            (∑ j : Fin 3,
              h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
                ν t W W i x
                (h3FourierAxisDirection (h3AxisOfFin3 j))
                (h3FourierAxisDirection (h3AxisOfFin3 j)))
          +
        h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i x)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hDiag :=
    tendsto_inv_smul_sub_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_zero_right
      hν U₀ hA hU₀ ht htR i x

  have hGen :=
    intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath_eq_viscosity_mul_DuhamelHessianTrace_selectedRestart
      hν U₀ hA hU₀ ht htR i x

  dsimp only [W] at hDiag hGen ⊢
  rw [hGen] at hDiag
  exact hDiag

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.DiagonalC1Cocycle
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.GeneratorIntegral
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.C0.Endpoint.FTC
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Selected Duhamel old-source classical right quotient

The fresh endpoint quotient is already closed.  This file treats the
complementary part directly on the literal classical Duhamel integral, keeping
the source interval fixed at `0..t` while the terminal heat time changes from
`t` to `t+h`.

For a strict source slice `s < t`, set `a = t - s`.  The fixed-lag nonlinear
heat reconstruction is differentiable in its heat-time parameter, so

    h⁻¹ • (H_{a+h} N(W(s)) - H_a N(W(s)))

converges to the fixed-lag heat generator at `a`.

The key uniform domination is also already present analytically.  For every
later lag `r ≥ a`, heat contractivity bounds the generator by the second
Fourier moment at the anchor lag `a`.  Along the selected restart path this is
exactly a constant multiple of the named selected second-moment profile, which
is genuinely interval-integrable on `0..t`.

Dominated convergence therefore gives

    ∫₀ᵗ h⁻¹ (K_{t+h,s} - K_{t,s}) ds
      ⟶
    ∫₀ᵗ G_{t,s} ds

as `h ↓ 0`.

The next checkpoint only needs interval-integral linearity to move the scalar
quotient outside the old-source integral, and then add the already-closed
fresh-tail quotient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3DuhamelOldSourceQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- A later positive heat lag is bounded, after inverse Fourier reconstruction
of the time generator, by the second Fourier moment at any earlier positive
anchor lag. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative_le_anchor_secondMoment
    {ν a r : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (har : a ≤ r)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
        ν r U V i x‖
      ≤
    (ν * (2 * Real.pi) ^ 2) *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν a U V i ξ‖) := by
  have hr : 0 < r := lt_of_lt_of_le ha har

  have hTargetInt :=
    (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative_integrable
      hν hr U V i).norm

  have hMoment :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
      hν ha U V i 2 (by norm_num)

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (ν * (2 * Real.pi) ^ 2) *
            (‖ξ‖ ^ 2 *
              ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν a U V i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul (ν * (2 * Real.pi) ^ 2)

  unfold h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourier_eq]

  calc
    ‖∫ ξ : H3FourierPoint3,
        𝐞 (-(inner ℝ ξ (-x))) •
          h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
            ν r U V i ξ‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖𝐞 (-(inner ℝ ξ (-x))) •
          h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
            ν r U V i ξ‖ :=
      norm_integral_le_integral_norm _
    _ =
      ∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
          ν r U V i ξ‖ := by
        apply integral_congr_ae
        filter_upwards with ξ
        simp only [Circle.norm_smul]
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (ν * (2 * Real.pi) ^ 2) *
          (‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν a U V i ξ‖) := by
        refine integral_mono_ae hTargetInt hMajorantInt ?_
        filter_upwards with ξ
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative_le_anchor
            hν har U V i ξ
    _ =
      (ν * (2 * Real.pi) ^ 2) *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν a U V i ξ‖) := by
        rw [integral_const_mul]

/-- Pointwise old-source difference quotient for the literal classical
retarded nonlinear forcing. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) : ℂ :=
  h⁻¹ •
    (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν (t + h) W W i x s
      -
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t W W i x s)

/-- At every strict source slice, the old-source quotient converges from the
right to the terminal-time heat generator at the base lag. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient_zero_right
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (W : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
          ν t h W i x s)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
          ν t W W i x s)) := by
  let a : ℝ := t - s
  let U : H3SpectralFinVectorState := W s

  have ha : 0 < a := by
    dsimp only [a]
    exact sub_pos.mpr hs

  have hDeriv :=
    h3RawFinLerayOuterProductDivergenceHeatC3Representative_hasDerivAt_time
      hν ha U U i x

  have hSlope := hDeriv.tendsto_slope_zero_right

  have hEq :
      (fun h : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
          ν t h W i x s)
        =
      (fun h : ℝ =>
        h⁻¹ •
          (h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (a + h) U U i x
            -
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν a U U i x)) := by
    funext h
    unfold
      h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
    dsimp only [a, U]
    congr 3
    ring

  rw [hEq]

  unfold h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
  dsimp only [a, U]
  exact hSlope

/-- For a positive increment and strict selected source slice, the old-source
quotient is dominated by the base-time selected second-moment profile. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient_selectedRestart_le_profile
    {ν A t h s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hh : 0 < h)
    (hs : s < t)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
        ν t h W i x s‖
      ≤
    (ν * (2 * Real.pi) ^ 2) *
      h3NonlinearForcingHeatSecondMomentProfile
        ν t W i s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let a : ℝ := t - s
  let U : H3SpectralFinVectorState := W s
  let f : ℝ → ℂ :=
    fun r =>
      h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν r U U i x
  let f' : ℝ → ℂ :=
    fun r =>
      h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
        ν r U U i x
  let C : ℝ :=
    (ν * (2 * Real.pi) ^ 2) *
      h3NonlinearForcingHeatSecondMomentProfile
        ν t W i s

  have ha : 0 < a := by
    dsimp only [a]
    exact sub_pos.mpr hs

  have hDeriv :
      ∀ r ∈ Set.Icc a (a + h),
        HasDerivWithinAt
          f
          (f' r)
          (Set.Icc a (a + h))
          r := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le ha hr.1
    exact
      (h3RawFinLerayOuterProductDivergenceHeatC3Representative_hasDerivAt_time
        hν hrpos U U i x).hasDerivWithinAt

  have hBound :
      ∀ r ∈ Set.Ico a (a + h),
        ‖f' r‖ ≤ C := by
    intro r hr

    have hAnchor :=
      norm_h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative_le_anchor_secondMoment
        hν ha hr.1 U U i x

    dsimp only [f', C]
    dsimp only [U, W] at hAnchor
    simpa only [
      h3NonlinearForcingHeatSecondMomentProfile,
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
    ] using hAnchor

  have hIncrement :
      ‖f (a + h) - f a‖ ≤ C * ((a + h) - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      hDeriv
      hBound
      (a + h)
      ⟨le_add_of_nonneg_right hh.le, le_rfl⟩

  have hInvNonneg : 0 ≤ h⁻¹ := inv_nonneg.mpr hh.le

  have hQuotient :
      ‖h⁻¹ • (f (a + h) - f a)‖ ≤ C := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
    calc
      h⁻¹ * ‖f (a + h) - f a‖
          ≤ h⁻¹ * (C * ((a + h) - a)) :=
        mul_le_mul_of_nonneg_left hIncrement hInvNonneg
      _ = C := by
        rw [show (a + h) - a = h by ring]
        calc
          h⁻¹ * (C * h) = (h⁻¹ * h) * C := by ring
          _ = C := by simp [ne_of_gt hh]

  unfold
    h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath

  change
    ‖h⁻¹ •
      (f ((t + h) - s) - f (t - s))‖
      ≤
    (ν * (2 * Real.pi) ^ 2) *
      h3NonlinearForcingHeatSecondMomentProfile
        ν t W i s

  have hplus : (t + h) - s = a + h := by
    dsimp only [a]
    ring
  have hbase : t - s = a := by
    rfl

  rw [hplus, hbase]
  dsimp only [C] at hQuotient
  exact hQuotient

/-- Dominated convergence for the selected old-source classical quotient on
the fixed source interval `0..t`. -/
theorem tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient_selectedRestart_zero_right
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
        ∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
            ν t h W i x s)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
            ν t W W i x s)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let μ : Measure ℝ :=
    volume.restrict (Set.Ioo (0 : ℝ) t)

  let F : ℝ → ℝ → ℂ :=
    fun h s =>
      h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
        ν t h W i x s

  let G : ℝ → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
      ν t W W i x

  let bound : ℝ → ℝ :=
    fun s =>
      (ν * (2 * Real.pi) ^ 2) *
        h3NonlinearForcingHeatSecondMomentProfile
          ν t W i s

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hFMeas :
      ∀ᶠ h : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
        AEStronglyMeasurable
          (F h)
          μ := by
    filter_upwards [self_mem_nhdsWithin] with h hh

    have hhpos : 0 < h := by
      exact hh

    have hPlusFull :=
      continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Icc
        (a := (0 : ℝ))
        (t := t + h)
        hν
        (by linarith [ht, hhpos])
        W W hWcont hWcont i x

    have hBaseFull :=
      continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Icc
        (a := (0 : ℝ))
        (t := t)
        hν
        ht
        W W hWcont hWcont i x

    have hPlus :
        ContinuousOn
          (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
            ν (t + h) W W i x)
          (Set.Ioo (0 : ℝ) t) := by
      exact
        hPlusFull.mono
          (by
            intro s hs
            constructor
            · exact hs.1.le
            · linarith [hs.2, hhpos])

    have hBase :
        ContinuousOn
          (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
            ν t W W i x)
          (Set.Ioo (0 : ℝ) t) := by
      exact
        hBaseFull.mono
          (by
            intro s hs
            exact ⟨hs.1.le, hs.2.le⟩)

    dsimp only [F, μ]
    unfold h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient

    exact
      AEStronglyMeasurable.const_smul
        ((hPlus.aestronglyMeasurable measurableSet_Ioo).sub
          (hBase.aestronglyMeasurable measurableSet_Ioo))
        h⁻¹

  have hBoundAE :
      ∀ᶠ h : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
        ∀ᵐ s : ℝ ∂μ,
          ‖F h s‖ ≤ bound s := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    dsimp only [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    dsimp only [F, bound, W]
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient_selectedRestart_le_profile
        hν U₀ hA hU₀ hh hs.2 i x

  have hBoundInt :
      Integrable
        bound
        μ := by
    have hProfile :=
      h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_intervalIntegrable
        hν U₀ hA hU₀ ht htR i

    dsimp only [bound, μ, W]
    change
      IntegrableOn
        (fun s : ℝ =>
          (ν * (2 * Real.pi) ^ 2) *
            h3NonlinearForcingHeatSecondMomentProfile
              ν t
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀)
              i s)
        (Set.Ioo (0 : ℝ) t)
        volume

    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    exact hProfile.const_mul (ν * (2 * Real.pi) ^ 2)

  have hLim :
      ∀ᵐ s : ℝ ∂μ,
        Tendsto
          (fun h : ℝ => F h s)
          (𝓝[Set.Ioi (0 : ℝ)] 0)
          (𝓝 (G s)) := by
    dsimp only [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    dsimp only [F, G]
    exact
      tendsto_h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient_zero_right
        hν hs.2 W i x

  have hMain :
      Tendsto
        (fun h : ℝ =>
          ∫ s : ℝ, F h s ∂μ)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝
          (∫ s : ℝ, G s ∂μ)) := by
    exact
      tendsto_integral_filter_of_dominated_convergence
        (μ := μ)
        (l := (𝓝[Set.Ioi (0 : ℝ)] 0))
        (F := F)
        (f := G)
        (bound := bound)
        hFMeas
        hBoundAE
        hBoundInt
        hLim

  have hPathEq :
      (fun h : ℝ =>
        ∫ s : ℝ, F h s ∂μ)
        =
      (fun h : ℝ =>
        ∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatOldSourceQuotient
            ν t h W i x s) := by
    funext h
    dsimp only [F, μ]
    rw [intervalIntegral.integral_of_le ht.le]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  have hLimitEq :
      (∫ s : ℝ, G s ∂μ)
        =
      ∫ s in (0 : ℝ)..t,
        h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
          ν t W W i x s := by
    dsimp only [G, μ]
    rw [intervalIntegral.integral_of_le ht.le]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  rw [hPathEq, hLimitEq] at hMain
  exact hMain

end

end Euclidean
end Bridge
end PrimeTensor

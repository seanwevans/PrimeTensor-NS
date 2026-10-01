import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Endpoint.Dynamic
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.C0.Endpoint.FTC
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# First-order limit of the physical short Duhamel tail

The nonlinear heat forcing is now stable under simultaneous zero-lag collapse
and motion of both spectral inputs.  This file applies that theorem to the
shrinking restart triangle.

For a restart origin `a` and a short positive elapsed time `h`, consider the
physical scalar tail

    ∫ s in 0..h,
      H_{h-s} F(U(a+s), V(a+s))(x).

Rescale `s = h r`.  After dividing by `h`, the tail becomes the fixed-domain
integral

    ∫ r in 0..1,
      H_{h-h r} F(U(a+h r), V(a+h r))(x).

For every `r < 1`, the heat lag tends to zero through positive values and both
inputs tend to their values at `a`.  The dynamic zero-lag theorem therefore
gives pointwise convergence to the instantaneous unheated forcing at `a`.
The already-proved lag-uniform bilinear estimate and global path bounds give a
constant integrable majorant on `[0,1]`.

Dominated convergence then proves that the normalized short tail tends to the
instantaneous Leray--divergence forcing.  This is the nonlinear first-order
piece needed in the positive-time mild-equation derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailFirstOrder
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The rescaled physical short-tail kernel on the fixed interval `[0,1]`. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailKernel
    (ν a h : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (r : ℝ) : ℂ :=
  h3RawFinLerayOuterProductDivergenceHeatC3Representative
    ν
    (h - h * r)
    (U (a + h * r))
    (V (a + h * r))
    i
    x

/-- For fixed positive `h`, the rescaled short-tail kernel is continuous on
the closed unit interval. -/
theorem continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailKernel
    {ν a h : ℝ}
    (hν : 0 < ν)
    (hh : 0 < h)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousOn
      (h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailKernel
        ν a h U V i x)
      (Set.Icc (0 : ℝ) 1) := by
  let Ua : ℝ → H3SpectralFinVectorState :=
    fun s => U (a + s)
  let Va : ℝ → H3SpectralFinVectorState :=
    fun s => V (a + s)
  let R : ℝ → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
      ν h Ua Va i x

  have hUa : Continuous Ua := by
    dsimp only [Ua]
    exact hU.comp (continuous_const.add continuous_id)

  have hVa : Continuous Va := by
    dsimp only [Va]
    exact hV.comp (continuous_const.add continuous_id)

  have hR :
      ContinuousOn
        R
        (Set.Icc (0 : ℝ) h) := by
    dsimp only [R]
    exact
      continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Icc
        hν hh Ua Va hUa hVa i x

  have hScale :
      Continuous
        (fun r : ℝ => h * r) :=
    continuous_const.mul continuous_id

  have hMaps :
      MapsTo
        (fun r : ℝ => h * r)
        (Set.Icc (0 : ℝ) 1)
        (Set.Icc (0 : ℝ) h) := by
    intro r hr
    constructor
    · exact mul_nonneg hh.le hr.1
    · calc
        h * r ≤ h * 1 :=
          mul_le_mul_of_nonneg_left hr.2 hh.le
        _ = h := by ring

  have hComp :
      ContinuousOn
        (fun r : ℝ => R (h * r))
        (Set.Icc (0 : ℝ) 1) :=
    hR.comp hScale.continuousOn hMaps

  change
    ContinuousOn
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν
          (h - h * r)
          (U (a + h * r))
          (V (a + h * r))
          i
          x)
      (Set.Icc (0 : ℝ) 1)
  exact hComp

/-- On globally bounded continuous paths, the rescaled `[0,1]` short-tail
integral converges to the instantaneous unheated forcing at the restart
origin. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailIntegral
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        ∫ r in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailKernel
            ν a h U V i x r)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (U a) (V a) i x)) := by
  let l : Filter ℝ :=
    𝓝[Set.Ioi (0 : ℝ)] 0

  let M : ℝ :=
    h3NonlinearForcingL1Coefficient * MU * MV

  let E : ℂ :=
    h3RawFinLerayOuterProductDivergenceC0Representative
      (U a) (V a) i x

  let F : ℝ → ℝ → ℂ :=
    fun h r =>
      h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailKernel
        ν a h U V i x r

  have hh0 :
      Tendsto
        (fun h : ℝ => h)
        l
        (𝓝 (0 : ℝ)) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds

  have hEventuallyPos :
      ∀ᶠ h : ℝ in l, 0 < h := by
    exact self_mem_nhdsWithin

  have hF_meas :
      ∀ᶠ h : ℝ in l,
        AEStronglyMeasurable
          (F h)
          (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [hEventuallyPos] with h hh
    have hCont :=
      continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailKernel
        (a := a) hν hh U V hUcont hVcont i x
    have hContUIcc :
        ContinuousOn
          (F h)
          [[(0 : ℝ), 1]] := by
      dsimp only [F]
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hCont
    exact
      (hContUIcc.mono uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc

  have h_bound :
      ∀ᶠ h : ℝ in l,
        ∀ᵐ r : ℝ ∂volume,
          r ∈ Ι (0 : ℝ) 1 →
            ‖F h r‖ ≤ M := by
    filter_upwards [hEventuallyPos] with h hh
    filter_upwards [(volume : Measure ℝ).ae_ne (1 : ℝ)] with r hr1
    intro hr

    have hrIoc :
        r ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr

    have hrlt : r < 1 :=
      lt_of_le_of_ne hrIoc.2 hr1

    have hlag :
        0 < h - h * r := by
      have hOne : 0 < 1 - r := sub_pos.mpr hrlt
      calc
        0 < h * (1 - r) := mul_pos hh hOne
        _ = h - h * r := by ring

    have h0 :=
      norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_le_bilinear
        hν hlag
        (U (a + h * r))
        (V (a + h * r))
        i x

    have hC :
        0 ≤ h3NonlinearForcingL1Coefficient :=
      h3NonlinearForcingL1Coefficient_nonneg

    have h1 :
        h3NonlinearForcingL1Coefficient *
              ‖U (a + h * r)‖
          ≤
        h3NonlinearForcingL1Coefficient * MU :=
      mul_le_mul_of_nonneg_left
        (hU (a + h * r))
        hC

    have h2 :
        h3NonlinearForcingL1Coefficient *
              ‖U (a + h * r)‖ *
              ‖V (a + h * r)‖
          ≤
        h3NonlinearForcingL1Coefficient * MU * MV :=
      mul_le_mul
        h1
        (hV (a + h * r))
        (norm_nonneg _)
        (mul_nonneg hC hMU)

    dsimp only [
      F,
      M,
      h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailKernel
    ]
    exact h0.trans h2

  have hMInt :
      IntervalIntegrable
        (fun _r : ℝ => M)
        volume
        0
        1 :=
    intervalIntegrable_const

  have h_lim :
      ∀ᵐ r : ℝ ∂volume,
        r ∈ Ι (0 : ℝ) 1 →
          Tendsto
            (fun h : ℝ => F h r)
            l
            (𝓝 E) := by
    filter_upwards [(volume : Measure ℝ).ae_ne (1 : ℝ)] with r hr1
    intro hr

    have hrIoc :
        r ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr

    have hrlt : r < 1 :=
      lt_of_le_of_ne hrIoc.2 hr1

    have hOne : 0 < 1 - r :=
      sub_pos.mpr hrlt

    let τr : ℝ → ℝ :=
      fun h => h - h * r

    let Ur : ℝ → H3SpectralFinVectorState :=
      fun h => U (a + h * r)

    let Vr : ℝ → H3SpectralFinVectorState :=
      fun h => V (a + h * r)

    have hτNhds :
        Tendsto
          τr
          l
          (𝓝 (0 : ℝ)) := by
      have hmul :=
        hh0.mul_const (1 - r)
      dsimp only [τr]
      simpa only [zero_mul] using
        hmul.congr'
          (Eventually.of_forall fun h => by ring)

    have hτMaps :
        ∀ᶠ h : ℝ in l,
          τr h ∈ Set.Ici (0 : ℝ) := by
      filter_upwards [hEventuallyPos] with h hh
      dsimp only [τr]
      have hp : 0 < h * (1 - r) :=
        mul_pos hh hOne
      have heq : h - h * r = h * (1 - r) := by ring
      rw [heq]
      exact hp.le

    have hτ :
        Tendsto
          τr
          l
          (𝓝[Set.Ici (0 : ℝ)] 0) := by
      exact
        tendsto_inf.2
          ⟨hτNhds,
            tendsto_principal.2 hτMaps⟩

    have hτpos :
        ∀ᶠ h : ℝ in l,
          0 < τr h := by
      filter_upwards [hEventuallyPos] with h hh
      dsimp only [τr]
      have hp : 0 < h * (1 - r) :=
        mul_pos hh hOne
      nlinarith

    have hhr :
        Tendsto
          (fun h : ℝ => h * r)
          l
          (𝓝 (0 : ℝ)) := by
      simpa only [zero_mul] using
        hh0.mul_const r

    have har :
        Tendsto
          (fun h : ℝ => a + h * r)
          l
          (𝓝 a) := by
      simpa only [add_zero] using
        tendsto_const_nhds.add hhr

    have hUr :
        Tendsto
          Ur
          l
          (𝓝 (U a)) := by
      dsimp only [Ur]
      exact hUcont.continuousAt.tendsto.comp har

    have hVr :
        Tendsto
          Vr
          l
          (𝓝 (V a)) := by
      dsimp only [Vr]
      exact hVcont.continuousAt.tendsto.comp har

    have hDyn :=
      tendsto_h3RawFinLerayOuterProductDivergenceHeatC3Representative_dynamic_zero_right
        hν
        τr
        Ur
        Vr
        (U a)
        (V a)
        hτ
        hτpos
        hUr
        hVr
        i
        x

    dsimp only [F, E, τr, Ur, Vr]
    simpa only [
      h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailKernel
    ] using hDyn

  have hDCT :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume)
      (a := (0 : ℝ))
      (b := 1)
      (F := F)
      (f := fun _r : ℝ => E)
      (bound := fun _r : ℝ => M)
      hF_meas
      h_bound
      hMInt
      h_lim

  have hConst :
      (∫ _r in (0 : ℝ)..1, E) = E := by
    simp

  rw [hConst] at hDCT
  dsimp only [l, F, E] at hDCT ⊢
  exact hDCT

/-- The normalized physical short tail itself tends to the instantaneous
unheated nonlinear forcing. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatC3NormalizedShortTail
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in (0 : ℝ)..h,
            h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν
              (h - s)
              (U (a + s))
              (V (a + s))
              i
              x))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (U a) (V a) i x)) := by
  let l : Filter ℝ :=
    𝓝[Set.Ioi (0 : ℝ)] 0

  let A : ℝ → ℂ :=
    fun h =>
      ∫ r in (0 : ℝ)..1,
        h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailKernel
          ν a h U V i x r

  let B : ℝ → ℂ :=
    fun h =>
      h⁻¹ •
        (∫ s in (0 : ℝ)..h,
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν
            (h - s)
            (U (a + s))
            (V (a + s))
            i
            x)

  have hA :
      Tendsto
        A
        l
        (𝓝
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (U a) (V a) i x)) := by
    dsimp only [A, l]
    exact
      tendsto_h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailIntegral
        hν hMU hMV U V hUcont hVcont hU hV i x

  have hBA :
      B =ᶠ[l] A := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := ne_of_gt hh

    let f : ℝ → ℂ :=
      fun s =>
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν
          (h - s)
          (U (a + s))
          (V (a + s))
          i
          x

    have hScale :=
      intervalIntegral.smul_integral_comp_mul_left
        (f := f)
        (a := (0 : ℝ))
        (b := 1)
        h

    have hScale' :
        h •
            (∫ r in (0 : ℝ)..1,
              h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailKernel
                ν a h U V i x r)
          =
        ∫ s in (0 : ℝ)..h,
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν
            (h - s)
            (U (a + s))
            (V (a + s))
            i
            x := by
      dsimp only [f] at hScale
      simpa only [
        h3RawFinLerayOuterProductDivergenceHeatC3RescaledShortTailKernel,
        mul_zero,
        mul_one
      ] using hScale

    dsimp only [B, A]
    rw [← hScale']
    rw [smul_smul]
    rw [inv_mul_cancel₀ hh0]
    simp

  exact hA.congr' hBA.symm

end

end Euclidean
end Bridge
end PrimeTensor

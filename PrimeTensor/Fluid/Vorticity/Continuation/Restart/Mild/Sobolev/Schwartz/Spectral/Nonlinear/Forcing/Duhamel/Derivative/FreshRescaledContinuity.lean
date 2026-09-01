import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.GeneratorIntegral
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.C0.Endpoint.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.C0.Time.Integrability

/-!
# Rescaled fresh Duhamel tail: endpoint continuity

For a positive increment `h`, the fresh Duhamel tail from `t` to `t+h`
becomes, after the affine rescaling `s = t + h u`,

    h ∫₀¹ H_{h(1-u)} F(W(t+hu),W(t+hu)) du.

Thus its derivative at `h = 0⁺` is reduced to convergence of a fixed-domain
integrand on `u ∈ [0,1]`.

This file establishes exactly the pointwise and domination inputs for that
fixed-domain dominated-convergence argument:

* the lag-uniform bilinear pointwise estimate is extended to zero heat lag;
* for every interior `u ∈ (0,1)`, the rescaled integrand tends to the
  instantaneous unheated forcing as `h ↓ 0`;
* along the selected restart extension, the complete rescaled integrand is
  uniformly bounded by the constant nonlinear forcing budget
  `C_force * (2A) * (2A)` for `h ≥ 0` and `u ∈ [0,1]`.

The endpoints in `u` are irrelevant to the upcoming Lebesgue dominated
convergence step, so the convergence theorem is stated on the open unit
interval while the domination theorem covers the closed interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3DuhamelFreshRescaledContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The unheated continuous nonlinear forcing representative obeys the same
bilinear pointwise bound as every positive heat lag. -/
theorem norm_h3RawFinLerayOuterProductDivergenceC0Representative_le_bilinear
    {ν : ℝ}
    (hν : 0 < ν)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceC0Representative U V i x‖
      ≤
    h3NonlinearForcingL1Coefficient * ‖U‖ * ‖V‖ := by
  let C : ℝ :=
    h3NonlinearForcingL1Coefficient * ‖U‖ * ‖V‖

  have hZero :=
    tendsto_h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero_right
      hν U V i x

  have hZeroOpen :
      Tendsto
        (fun τ : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ U V i x)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝
          (h3RawFinLerayOuterProductDivergenceC0Representative
            U V i x)) := by
    exact
      hZero.mono_left
        (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

  have hNorm :
      Tendsto
        (fun τ : ℝ =>
          ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ U V i x‖)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝
          ‖h3RawFinLerayOuterProductDivergenceC0Representative
            U V i x‖) :=
    hZeroOpen.norm

  have hBound :
      ∀ᶠ τ : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ U V i x‖
          ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    dsimp only [C]
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_le_bilinear
        hν hτ U V i x

  exact le_of_tendsto hNorm hBound

/-- Unified lag-nonnegative bilinear pointwise estimate. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_le_bilinear_of_nonneg
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i x‖
      ≤
    h3NonlinearForcingL1Coefficient * ‖U‖ * ‖V‖ := by
  rcases lt_or_eq_of_le hτ with hτpos | rfl
  · exact
      norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_le_bilinear
        hν hτpos U V i x
  · rw [h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero]
    exact
      norm_h3RawFinLerayOuterProductDivergenceC0Representative_le_bilinear
        hν U V i x

/-- Rescaled fresh-tail integrand on the fixed unit interval. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (u : ℝ) : ℂ :=
  h3RawFinLerayOuterProductDivergenceHeatC3Representative
    ν
    (h * (1 - u))
    (W (t + h * u))
    (W (t + h * u))
    i
    x

/-- For every interior unit parameter, the rescaled fresh-tail integrand tends
from the right to the instantaneous unheated nonlinear forcing. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand_zero_right
    {ν t u : ℝ}
    (hν : 0 < ν)
    (W : ℝ → H3SpectralFinVectorState)
    (hW : Continuous W)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
          ν t h W i x u)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i x)) := by
  let c : ℝ := h3NonlinearForcingL1Coefficient

  let E : ℂ :=
    h3RawFinLerayOuterProductDivergenceC0Representative
      (W t) (W t) i x

  let T : ℝ → ℂ :=
    fun h =>
      h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν (h * (1 - u)) (W t) (W t) i x

  let g : ℝ → ℝ :=
    fun h =>
      c * ‖W (t + h * u) - W t‖ * ‖W (t + h * u)‖
        +
      c * ‖W t‖ * ‖W (t + h * u) - W t‖
        +
      ‖T h - E‖

  have hhZero :
      Tendsto
        (fun h : ℝ => h)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds

  have hArg :
      Tendsto
        (fun h : ℝ => t + h * u)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 t) := by
    simpa only [zero_mul, add_zero] using
      tendsto_const_nhds.add (hhZero.mul_const u)

  have hWarg :
      Tendsto
        (fun h : ℝ => W (t + h * u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 (W t)) :=
    hW.continuousAt.tendsto.comp hArg

  have hWdiff :
      Tendsto
        (fun h : ℝ => ‖W (t + h * u) - W t‖)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _h : ℝ => W t)
          (𝓝[Set.Ici (0 : ℝ)] 0)
          (𝓝 (W t)) :=
      tendsto_const_nhds
    simpa using (hWarg.sub hConst).norm

  have hWnorm :
      Tendsto
        (fun h : ℝ => ‖W (t + h * u)‖)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 ‖W t‖) :=
    hWarg.norm

  have hLagFull :
      Tendsto
        (fun h : ℝ => h * (1 - u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa only [zero_mul] using
      hhZero.mul_const (1 - u)

  have hOneMinus : 0 ≤ 1 - u := by
    linarith [hu.2]

  have hLagMaps :
      MapsTo
        (fun h : ℝ => h * (1 - u))
        (Set.Ici (0 : ℝ))
        (Set.Ici (0 : ℝ)) := by
    intro h hh
    exact mul_nonneg hh hOneMinus

  have hLag :
      Tendsto
        (fun h : ℝ => h * (1 - u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝[Set.Ici (0 : ℝ)] 0) := by
    exact
      tendsto_inf.2
        ⟨hLagFull,
          tendsto_principal.2 <|
            mem_inf_of_right <|
              mem_principal.2 hLagMaps⟩

  have hFrozen :
      Tendsto
        T
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 E) := by
    have h0 :=
      (tendsto_h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero_right
        hν (W t) (W t) i x).comp hLag
    dsimp only [T, E]
    exact h0

  have hTdiff :
      Tendsto
        (fun h : ℝ => ‖T h - E‖)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    have hEConst :
        Tendsto
          (fun _h : ℝ => E)
          (𝓝[Set.Ici (0 : ℝ)] 0)
          (𝓝 E) :=
      tendsto_const_nhds
    simpa using (hFrozen.sub hEConst).norm

  have hc :
      Tendsto
        (fun _h : ℝ => c)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 c) :=
    tendsto_const_nhds

  have hWtNorm :
      Tendsto
        (fun _h : ℝ => ‖W t‖)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 ‖W t‖) :=
    tendsto_const_nhds

  have hA :
      Tendsto
        (fun h : ℝ =>
          c * ‖W (t + h * u) - W t‖ * ‖W (t + h * u)‖)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa using ((hc.mul hWdiff).mul hWnorm)

  have hB :
      Tendsto
        (fun h : ℝ =>
          c * ‖W t‖ * ‖W (t + h * u) - W t‖)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa using ((hc.mul hWtNorm).mul hWdiff)

  have hgZero :
      Tendsto
        g
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa only [g, zero_add] using
      ((hA.add hB).add hTdiff)

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        ‖h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
              ν t h W i x u
            -
          E‖
          ≤
        g h := by
    filter_upwards [self_mem_nhdsWithin] with h hh

    by_cases hh0 : h = 0

    · subst h
      unfold
        h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
      dsimp only [T, g, E]
      simp only [zero_mul, add_zero, sub_self, norm_zero,
        mul_zero, zero_mul, zero_add]
      rw [h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero]

    · have hhpos : 0 < h :=
        lt_of_le_of_ne hh (Ne.symm hh0)

      have hu1 : 0 < 1 - u := by
        linarith [hu.2]

      have hlag : 0 < h * (1 - u) :=
        mul_pos hhpos hu1

      let Wh : H3SpectralFinVectorState :=
        W (t + h * u)

      have hDiff :
          h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
                ν t h W i x u
              -
            E
            =
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
                ν (h * (1 - u)) (Wh - W t) Wh i x
            +
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
                ν (h * (1 - u)) (W t) (Wh - W t) i x
            +
          (T h - E) := by
        unfold
          h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
        dsimp only [Wh, T]

        have hLeft :=
          h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_left
            hν hlag Wh (W t) Wh i x

        have hRight :=
          h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_right
            hν hlag (W t) Wh (W t) i x

        rw [hLeft, hRight]
        abel

      rw [hDiff]

      have hAbound :
          ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (h * (1 - u)) (Wh - W t) Wh i x‖
            ≤
          c * ‖Wh - W t‖ * ‖Wh‖ := by
        dsimp only [c]
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_left_le
            hν hlag Wh (W t) Wh i x

      have hBbound :
          ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (h * (1 - u)) (W t) (Wh - W t) i x‖
            ≤
          c * ‖W t‖ * ‖Wh - W t‖ := by
        dsimp only [c]
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_right_le
            hν hlag (W t) Wh (W t) i x

      change
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (h * (1 - u)) (Wh - W t) Wh i x
            +
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (h * (1 - u)) (W t) (Wh - W t) i x
            +
          (T h - E)‖
          ≤
        g h

      calc
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
                ν (h * (1 - u)) (Wh - W t) Wh i x
            +
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
                ν (h * (1 - u)) (W t) (Wh - W t) i x
            +
          (T h - E)‖
            ≤
          (‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
                ν (h * (1 - u)) (Wh - W t) Wh i x‖
            +
          ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
                ν (h * (1 - u)) (W t) (Wh - W t) i x‖)
            +
          ‖T h - E‖ := by
            exact
              (norm_add_le _ _).trans
                (add_le_add
                  (norm_add_le _ _)
                  (le_refl _))
        _ ≤
          (c * ‖Wh - W t‖ * ‖Wh‖
            +
          c * ‖W t‖ * ‖Wh - W t‖)
            +
          ‖T h - E‖ := by
            exact
              add_le_add
                (add_le_add hAbound hBbound)
                (le_refl _)
        _ = g h := by
          rfl

  have hNonneg :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        0 ≤
          ‖h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
              ν t h W i x u
            -
          E‖ :=
    Eventually.of_forall fun h => norm_nonneg _

  have hToE :
      Tendsto
        (h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
          ν t · W i x u)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 E) := by
    exact
      (tendsto_iff_norm_sub_tendsto_zero).2
        (squeeze_zero' hNonneg hUpper hgZero)

  dsimp only [E] at hToE
  exact hToE

/-- Along the selected restart extension, the rescaled fresh-tail integrand has
a single constant majorant for every nonnegative increment and every
`u ∈ [0,1]`. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand_selectedRestart_le
    {ν A t h u : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hh : 0 ≤ h)
    (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
        ν t h W i x u‖
      ≤
    h3NonlinearForcingL1Coefficient * (2 * A) * (2 * A) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hLag : 0 ≤ h * (1 - u) := by
    have hOneMinus : 0 ≤ 1 - u := by
      linarith [hu.2]
    exact mul_nonneg hh hOneMinus

  have hBase :=
    norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_le_bilinear_of_nonneg
      hν hLag
      (W (t + h * u))
      (W (t + h * u))
      i x

  have hW :
      ‖W (t + h * u)‖ ≤ 2 * A := by
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ (t + h * u)

  have hC : 0 ≤ h3NonlinearForcingL1Coefficient :=
    h3NonlinearForcingL1Coefficient_nonneg

  unfold h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand

  calc
    ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν (h * (1 - u))
        (W (t + h * u))
        (W (t + h * u))
        i x‖
      ≤
    h3NonlinearForcingL1Coefficient *
      ‖W (t + h * u)‖ *
      ‖W (t + h * u)‖ :=
      hBase
    _ ≤
      h3NonlinearForcingL1Coefficient * (2 * A) * (2 * A) := by
      have h2A : 0 ≤ 2 * A := by positivity
      gcongr

end

end Euclidean
end Bridge
end PrimeTensor

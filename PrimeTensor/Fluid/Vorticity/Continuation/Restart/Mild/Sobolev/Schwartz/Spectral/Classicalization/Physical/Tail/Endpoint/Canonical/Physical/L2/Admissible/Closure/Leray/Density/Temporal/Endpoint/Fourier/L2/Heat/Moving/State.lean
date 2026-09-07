import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.RHS.UnitViscosity

/-!
# Physical L² temporal admissibility: heat acting on a moving raw L² state

The interaction-picture derivative needs one joint limiting fact that is not
automatic from separate strong continuity statements.

Suppose a raw Fourier `L²` velocity state `V(h)` converges strongly to `V₀`
while the heat time tends to zero from the right.  Then

    S(h) V(h) → V₀.

No operator-norm continuity of the heat semigroup is needed.  The proof uses
only:

* contraction of each fixed-time heat operator;
* strong continuity of `S(h)V₀` for the fixed limiting state;
* the triangle inequality.

This is exactly the estimate needed to transport a moving slope through the
heat factor in the forthcoming interaction-picture derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatMovingState
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Raw Fourier `L²` heat evolution is contractive coordinatewise. -/
theorem norm_h3RawFourierL2HeatApplyNN_le
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3RawFourierL2FinVectorState) :
    ‖h3RawFourierL2HeatApplyNN ν hν t U‖
      ≤
    ‖U‖ := by
  exact
    norm_h3SpectralVelocityHeatApplyNN_le
      ν hν t U

/-- Raw Fourier `L²` heat evolution is exactly the identity at elapsed zero. -/
@[simp]
theorem h3RawFourierL2HeatApplyNN_zero
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3RawFourierL2FinVectorState) :
    h3RawFourierL2HeatApplyNN
        ν hν 0 U
      =
    U := by
  funext i

  change
    h3HeatFrequencyApplyNN
        ν hν 0 (U i)
      =
    U i

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3HeatFrequencyApplyNN_coeFn
      ν hν 0 (U i)
  ] with ξ hξ

  rw [hξ]
  simp [h3HeatFourierSymbol]

/-- Strong convergence survives a simultaneously vanishing heat time.

The state is allowed to move with `h`; contraction controls that motion while
ordinary strong continuity handles the fixed limiting state. -/
theorem tendsto_h3RawFourierL2HeatApplyNN_moving_zero_right
    (ν : ℝ)
    (hν : 0 ≤ ν)
    {V : ℝ → H3RawFourierL2FinVectorState}
    {V₀ : H3RawFourierL2FinVectorState}
    (hV :
      Tendsto
        V
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 V₀)) :
    Tendsto
      (fun h : ℝ =>
        h3RawFourierL2HeatApplyNN
          ν hν (Real.toNNReal h) (V h))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 V₀) := by
  let l : Filter ℝ :=
    𝓝[Set.Ioi (0 : ℝ)] 0

  let S : ℝ → H3RawFourierL2FinVectorState →
      H3RawFourierL2FinVectorState :=
    fun h U =>
      h3RawFourierL2HeatApplyNN
        ν hν (Real.toNNReal h) U

  let g : ℝ → ℝ :=
    fun h =>
      ‖V h - V₀‖ +
        ‖S h V₀ - V₀‖

  have hConst :
      Tendsto
        (fun _h : ℝ => V₀)
        l
        (𝓝 V₀) :=
    tendsto_const_nhds

  have hVdiff :
      Tendsto
        (fun h : ℝ => ‖V h - V₀‖)
        l
        (𝓝 0) := by
    simpa only [l, sub_self, norm_zero] using
      (hV.sub hConst).norm

  have hHeatFixed :
      Tendsto
        (fun h : ℝ => S h V₀)
        l
        (𝓝 V₀) := by
    have hContinuous :
        Continuous
          (fun h : ℝ => S h V₀) := by
      dsimp only [S]
      exact
        (continuous_h3RawFourierL2HeatApplyNN
          ν hν V₀).comp
          continuous_real_toNNReal

    have hAt :
        Tendsto
          (fun h : ℝ => S h V₀)
          (𝓝 (0 : ℝ))
          (𝓝 (S 0 V₀)) :=
      hContinuous.continuousAt

    have hZero :
        S 0 V₀ = V₀ := by
      dsimp only [S]
      simp

    rw [hZero] at hAt

    exact
      hAt.mono_left
        (show
          l ≤ 𝓝 (0 : ℝ) by
            dsimp only [l]
            exact inf_le_left)

  have hHeatDiff :
      Tendsto
        (fun h : ℝ => ‖S h V₀ - V₀‖)
        l
        (𝓝 0) := by
    simpa using
      (hHeatFixed.sub hConst).norm

  have hgZero :
      Tendsto
        g
        l
        (𝓝 0) := by
    dsimp only [g]
    simpa using
      hVdiff.add hHeatDiff

  have hUpper :
      ∀ᶠ h : ℝ in l,
        ‖S h (V h) - V₀‖
          ≤
        g h := by
    refine Eventually.of_forall ?_
    intro h

    have hDiff :
        S h (V h) - V₀
          =
        S h (V h - V₀) +
          (S h V₀ - V₀) := by
      dsimp only [S]
      change
        h3RawFourierL2HeatCLM
              ν hν (Real.toNNReal h) (V h)
            - V₀
          =
        h3RawFourierL2HeatCLM
              ν hν (Real.toNNReal h) (V h - V₀)
          +
        (h3RawFourierL2HeatCLM
              ν hν (Real.toNNReal h) V₀
            - V₀)
      rw [
        map_sub
      ]
      abel

    rw [hDiff]

    calc
      ‖S h (V h - V₀) +
          (S h V₀ - V₀)‖
          ≤
        ‖S h (V h - V₀)‖ +
          ‖S h V₀ - V₀‖ :=
        norm_add_le _ _
      _ ≤
        ‖V h - V₀‖ +
          ‖S h V₀ - V₀‖ := by
        exact
          add_le_add
            (norm_h3RawFourierL2HeatApplyNN_le
              ν hν (Real.toNNReal h) (V h - V₀))
            (le_refl _)
      _ = g h := by
        rfl

  have hNonneg :
      ∀ᶠ h : ℝ in l,
        0 ≤ ‖S h (V h) - V₀‖ :=
    Eventually.of_forall fun h =>
      norm_nonneg _

  have hResult :
      Tendsto
        (fun h : ℝ => S h (V h))
        l
        (𝓝 V₀) := by
    exact
      (tendsto_iff_norm_sub_tendsto_zero).2
        (squeeze_zero'
          hNonneg
          hUpper
          hgZero)

  simpa only [l, S] using hResult

end

end Euclidean
end Bridge
end PrimeTensor

import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Variation.Of.Constants.Weighted.Forcing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Physical.Solution

/-!
# Classicalization: close the selected H³ mild state identity directly

The Fourier-mode variation-of-constants route has now been lifted all the way
back to the weighted spectral H³ state, and the selected specialization has
reduced its analytic hypotheses to raw-mode continuity and the concrete
Fourier-mode ODE.

For the actual Banach-selected restart path, however, those pointwise Fourier
hypotheses are not needed in order to recover the H³ mild identity itself.
The path was constructed as the fixed point of precisely that mild operator.

The modern physical-solution layer already transports the normalized fixed
point to physical time and proves, for every `q ∈ [0,τ]`,

    H_q U₀ - D_q(W,W) = W(q).

This file specializes that theorem to the canonical restart radius and the
modern physical extension introduced in
`SelectedVariationOfConstantsStateReduction`.

This distinction is useful downstream:

* the selected H³ mild identity is now unconditional inside the restart window;
* the remaining raw-mode continuity and mode-ODE obligations belong only to
  the independent pointwise Fourier/classicalization route, not to the
  existence of the selected mild state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedVariationOfConstantsStateClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The modern canonical restart-radius physical extension satisfies the
concrete signed heat--Leray mild equation at every physical time in the closed
restart interval. -/
theorem h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_satisfies_mild_at
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SpectralVelocityHeatApplyNN
        ν hν.le (NNReal.mk t ht) U₀
      -
    h3SpectralFinHeatLerayDuhamel
      ν t hν W W
      =
    W t := by
  dsimp only

  let q :
      Set.Icc (0 : ℝ) (h3FinHeatLerayRestartRadius ν A) :=
    ⟨t, ht, htR⟩

  have h :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀
      hA
      hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      q

  have hqNN :
      h3PhysicalTimePointNN q = NNReal.mk t ht := by
    apply Subtype.ext
    rfl

  rw [hqNN] at h
  rw [h3SpectralFinHeatLerayPhysicalMildSolution_apply] at h

  simpa only [
    q,
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension,
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius,
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
  ] using h

/-- Canonical selected H³ variation of constants, now with no pointwise
Fourier-mode hypotheses: the actual selected state at time `t` is exactly the
heat evolution of the restart datum minus its heat--Leray Duhamel term. -/
theorem h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_variationOfConstants_state
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    W t
      =
    h3SpectralVelocityHeatApplyNN
        ν hν.le (NNReal.mk t ht) U₀
      -
    h3SpectralFinHeatLerayDuhamel
      ν t hν W W := by
  exact
    (h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_satisfies_mild_at
      hν U₀ hA hU₀ ht htR).symm

end

end Euclidean
end Bridge
end PrimeTensor

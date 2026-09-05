import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarter.Frozen.Fubini

/-!
# Product integrability of the full selected nine-quarter terminal tail

The selected terminal-half `9/4` kernel has now been split into two pieces:

* the source-state variation
  `N(W(s), W(s)) - N(W(t), W(t))`, whose quarter-Hölder cancellation gives an
  integrable `-7/8` source-time majorant; and
* the frozen terminal forcing `N(W(t), W(t))`, whose source-time integral is
  handled by the already-closed second heat primitive and the frozen forcing
  quarter Fourier moment.

Both pieces are genuinely integrable on

    (t/2, t) × H3FourierPoint3.

This file recombines them into the actual weighted selected tail kernel

    |ξ|^(9/4) H_{t-s}(ξ) N(W(s), W(s))(ξ)

and records its product-space integrability.  No new estimate is introduced:
the proof is the algebraic identity

    variation + frozen = full

followed by `Integrable.add`.

The next checkpoint can integrate this full kernel in source time and package
the resulting `9/4` Fourier amplitude.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedNineQuarterFullFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual selected terminal-half Duhamel kernel after inserting the
complex `9/4` Fourier weight. -/
noncomputable def h3SelectedDuhamelTailNineQuarterComplexKernel
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3) : ℂ :=
  (h3FourierNineQuarterWeight p.2 : ℂ) *
    h3SelectedDuhamelTailComplexKernel
      ν A t hν U₀ hA hU₀ i p

/-- The full selected `9/4` kernel is exactly the sum of the varying and frozen
terminal pieces. -/
theorem h3SelectedDuhamelTailNineQuarterComplexKernel_eq_variation_add_frozen
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    h3SelectedDuhamelTailNineQuarterComplexKernel
        ν A t hν U₀ hA hU₀ i
      =
    (fun p : ℝ × H3FourierPoint3 =>
      h3SelectedDuhamelTailNineQuarterVariationComplexKernel
          ν A t hν U₀ hA hU₀ i p
        +
      h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
          ν A t hν U₀ hA hU₀ i p) := by
  funext p
  unfold
    h3SelectedDuhamelTailNineQuarterComplexKernel
    h3SelectedDuhamelTailNineQuarterVariationComplexKernel
    h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
    h3SelectedDuhamelTailComplexKernel
  dsimp only
  ring

/-- The actual selected `9/4` terminal-half kernel is genuinely integrable on
source-time × frequency. -/
theorem h3SelectedDuhamelTailNineQuarterComplexKernel_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailNineQuarterComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
        (volume : Measure H3FourierPoint3)) := by
  have hVariation :
      Integrable
        (h3SelectedDuhamelTailNineQuarterVariationComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3)) :=
    h3SelectedDuhamelTailNineQuarterVariationComplexKernel_fubini_integrable
      hν U₀ hA hU₀ ht htR i

  have hFrozen :
      Integrable
        (h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3)) :=
    h3SelectedDuhamelTailNineQuarterFrozenComplexKernel_fubini_integrable
      hν U₀ hA hU₀ ht htR i

  rw [
    h3SelectedDuhamelTailNineQuarterComplexKernel_eq_variation_add_frozen
      (ν := ν) (A := A) (t := t) hν U₀ hA hU₀ i
  ]

  exact hVariation.add hFrozen

end
end Euclidean
end Bridge
end PrimeTensor

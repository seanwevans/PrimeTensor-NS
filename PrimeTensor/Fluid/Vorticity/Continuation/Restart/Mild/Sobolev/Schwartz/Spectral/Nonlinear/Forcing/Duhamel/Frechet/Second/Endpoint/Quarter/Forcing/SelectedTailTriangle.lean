import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedBudget

/-!
# Selected quarter-Hölder forcing: terminal-tail triangle split

`Forcing.SelectedBudget` already controls the cancelled terminal tail and the
forcing frozen at the terminal time as two separate pieces.  To reconnect that
budget to the unsplit second-Duhamel kernel, we need the elementary pointwise
identity

    N(s) = (N(s) - N(t)) + N(t)

inside the retarded heat multiplier.

This file records the corresponding second-Fourier-moment triangle inequality
at each frequency.  It is deliberately kept pointwise: the following step can
push it under the frequency and source-time integrals using the integrability
machinery that is now available on both tail pieces.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedTailTriangle
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At a fixed frequency, the unsplit terminal forcing is bounded by the sum
of its endpoint-cancelled part and its terminally frozen part after applying
the retarded heat multiplier and the second Fourier moment. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_secondMoment_le_endpointDifference_add_frozen
    (ν t s : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν (t - s) ξ *
          h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖
      ≤
    ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν (t - s) ξ *
          (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
            h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖ +
      ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν (t - s) ξ *
          h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
  let H : ℂ := h3HeatFourierSymbol ν (t - s) ξ
  let Ns : ℂ :=
    h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ
  let Nt : ℂ :=
    h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ

  have hsplit : H * Ns = H * (Ns - Nt) + H * Nt := by
    ring

  rw [show
    h3HeatFourierSymbol ν (t - s) ξ *
        h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ = H * Ns by
      rfl]
  rw [show
    h3HeatFourierSymbol ν (t - s) ξ *
        (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
          h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ) =
      H * (Ns - Nt) by
      rfl]
  rw [show
    h3HeatFourierSymbol ν (t - s) ξ *
        h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ = H * Nt by
      rfl]
  rw [hsplit]

  calc
    ‖ξ‖ ^ 2 * ‖H * (Ns - Nt) + H * Nt‖
        ≤
      ‖ξ‖ ^ 2 * (‖H * (Ns - Nt)‖ + ‖H * Nt‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (norm_add_le (H * (Ns - Nt)) (H * Nt))
            (sq_nonneg ‖ξ‖)
    _ =
      ‖ξ‖ ^ 2 * ‖H * (Ns - Nt)‖ +
        ‖ξ‖ ^ 2 * ‖H * Nt‖ := by
          ring

end

end Euclidean
end Bridge
end PrimeTensor

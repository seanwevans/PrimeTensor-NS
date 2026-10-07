import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher

/-!
# Reciprocal width rate on the resolved canonical forcing intervals

The resolved canonical forcing package retains a positive numerator `δ` and
strictly forward terminal intervals `[s n, t n]`, with the left endpoints
converging to the terminal time and the right endpoints remaining below it.

Therefore the interval widths vanish and the canonical reciprocal-width scale

    δ / (12 * (t n - s n))

tends to `+∞`.

This isolates the quantitative hinge used by both surviving fixed-radial
forcing branches.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

theorem h3TerminalCanonicalReciprocalWidthRate_tendstoAtTop
    {T δ : ℝ}
    (hδ : 0 < δ)
    (s t : ℕ → ℝ)
    (hsTendsto :
      Tendsto s atTop (𝓝 T))
    (htUpper :
      ∀ n : ℕ,
        t n < T)
    (hForward :
      ∀ n : ℕ,
        s n < t n) :
    Tendsto
      (
        fun n : ℕ =>
          δ
            /
          (
            12
              *
            (
              t n
                -
              s n
            )
          )
      )
      atTop
      atTop := by

  refine
    tendsto_atTop.2
      ?_

  intro M

  let K : ℝ :=
    max M 0 + 1

  have hKPos :
      0 < K := by

    dsimp only [K]

    have hMax :
        0 ≤ max M 0 :=
      le_max_right
        M
        0

    linarith

  let c : ℝ :=
    δ / (12 * K)

  have hc :
      0 < c := by

    dsimp only [c]

    positivity

  have hsLate :
      ∀ᶠ n : ℕ in atTop,
        T - c < s n :=
    (tendsto_order.1 hsTendsto).1
      (T - c)
      (by linarith)

  filter_upwards [hsLate] with n hsLateN

  have hGapPos :
      0 < t n - s n :=
    sub_pos.mpr
      (hForward n)

  have hGapUpper :
      t n - s n < c := by

    have htN :
        t n < T :=
      htUpper n

    linarith

  have hDenKPos :
      0 < 12 * K := by

    positivity

  have hGapScaled :
      (t n - s n) * (12 * K)
        <
      δ := by

    exact
      (lt_div_iff₀ hDenKPos).1
        (by
          simpa only [c] using hGapUpper)

  have hDenGapPos :
      0 < 12 * (t n - s n) := by

    positivity

  have hKThreshold :
      K
        <
      δ / (12 * (t n - s n)) := by

    apply
      (lt_div_iff₀ hDenGapPos).2

    calc
      K * (12 * (t n - s n))
          =
        (t n - s n) * (12 * K) := by
          ring
      _ < δ :=
        hGapScaled

  have hMK :
      M < K := by

    dsimp only [K]

    have hMMax :
        M ≤ max M 0 :=
      le_max_left
        M
        0

    linarith

  exact
    le_of_lt
      (
        lt_trans
          hMK
          hKThreshold
      )

end

end Euclidean
end Bridge
end PrimeTensor

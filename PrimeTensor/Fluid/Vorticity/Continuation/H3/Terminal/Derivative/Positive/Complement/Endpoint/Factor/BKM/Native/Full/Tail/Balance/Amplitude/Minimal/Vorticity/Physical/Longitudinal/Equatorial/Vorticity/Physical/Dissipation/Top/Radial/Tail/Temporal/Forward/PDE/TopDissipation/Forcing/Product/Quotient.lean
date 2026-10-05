import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Velocity.Truncation.Convergence.Evolution
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Bound.Forcing.Moment
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Strong arbitrary-radial selected velocity slope errors

The arbitrary-radial temporal checkpoint proves, for every natural order
`m ≥ 2`, that the selected velocity path

    V_m(t) = |ξ|^m û_i(t)

has strong Fourier `L²` derivative

    G_m(t) = |ξ|^m R̂_i(t).

For the nonlinear forcing product rule we need this in the literal
difference-quotient form used by the bilinear estimate.  At a strict interior
base time `x`, define

    E_m(h)
      =
    h⁻¹ • (V_m(x+h) - V_m(x)) - G_m(x).

Mathlib's `HasDerivAt.tendsto_slope_zero` is exactly the assertion

    E_m(h) -> 0

on the punctured neighborhood `𝓝[≠] 0`.

This file packages that statement once at arbitrary radial order.  In
particular, the future forcing quotient can use orders

    2, 4, 6, 8, 10, 12, ...

without introducing any new temporal regularity argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedRadialSlopeError
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Generic radial slope error -/

/--
Order-`m` selected velocity difference-quotient error at one strict interior
point of the positive restart slab.
-/
noncomputable def h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
    (m : ℕ)
    (hm : 2 ≤ m)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ) :
    H3FourierComplexL2 :=
  h⁻¹ •
      (
        Set.IccExtend
            (by linarith : Q / 2 ≤ Q)
            (
              fun s : Set.Icc (Q / 2) Q =>
                h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
                  m hm
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState
                    hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  (by positivity : 0 < Q / 2)
                  hQR s i
            )
            (x + h)
          -
        Set.IccExtend
            (by linarith : Q / 2 ≤ Q)
            (
              fun s : Set.Icc (Q / 2) Q =>
                h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
                  m hm
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState
                    hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  (by positivity : 0 < Q / 2)
                  hQR s i
            )
            x
      )
    -
  h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
    m hNS ht₀ hE hTail hQ hQR i
    ⟨x, hx.1.le, hx.2.le⟩

/--
The arbitrary-radial selected velocity slope error converges strongly to zero
on the punctured increment neighborhood.
-/
theorem tendsto_h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_zero
    (m : ℕ)
    (hm : 2 ≤ m)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    Tendsto
      (fun h : ℝ =>
        h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
          m hm
          hNS ht₀ hE hTail hQ hQR i hx h)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (0 : H3FourierComplexL2)) := by

  have hDeriv :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnSlab_hasDerivAt
      m hm
      hNS ht₀ hE hTail
      hQ hQR i hx

  have hSlope :=
    hDeriv.tendsto_slope_zero

  have hErr :=
    hSlope.sub
      (tendsto_const_nhds :
        Tendsto
          (fun _h : ℝ =>
            h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
              m hNS ht₀ hE hTail hQ hQR i
              ⟨x, hx.1.le, hx.2.le⟩)
          (𝓝[≠] (0 : ℝ))
          (𝓝
            (
              h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
                m hNS ht₀ hE hTail hQ hQR i
                ⟨x, hx.1.le, hx.2.le⟩
            )))

  simpa only [
    h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab,
    sub_self
  ] using hErr

/--
Consequently the norm of the arbitrary-radial selected velocity slope error
also tends to zero.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_zero
    (m : ℕ)
    (hm : 2 ≤ m)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
          m hm
          hNS ht₀ hE hTail hQ hQR i hx h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  have hBase :=
    tendsto_h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_zero
      m hm
      hNS ht₀ hE hTail
      hQ hQR i hx

  have hNorm :=
    (continuous_norm.tendsto
      (0 : H3FourierComplexL2)).comp
      hBase

  change
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
          m hm
          hNS ht₀ hE hTail hQ hQR i hx h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ‖(0 : H3FourierComplexL2)‖)
    at hNorm

  simpa only [norm_zero] using hNorm

/-! ## Named endpoint orders -/

/--
Order-two slope error, used by the first weighted terminal forcing branch.
-/
noncomputable def h3PreterminalSelectedVelocitySecondRadialSlopeErrorFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ) :
    H3FourierComplexL2 :=
  h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
    2 (by norm_num)
    hNS ht₀ hE hTail hQ hQR i hx h

/--
Order-four slope error, used by the second weighted terminal forcing branch.
-/
noncomputable def h3PreterminalSelectedVelocityFourthRadialSlopeErrorFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ) :
    H3FourierComplexL2 :=
  h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
    4 (by norm_num)
    hNS ht₀ hE hTail hQ hQR i hx h

/--
Order-six slope error, the first high moment needed by the order-two forcing
product rule.
-/
noncomputable def h3PreterminalSelectedVelocitySixthRadialSlopeErrorFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ) :
    H3FourierComplexL2 :=
  h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
    6 (by norm_num)
    hNS ht₀ hE hTail hQ hQR i hx h

/--
Order-ten slope error, the first high moment needed by the order-four forcing
product rule.
-/
noncomputable def h3PreterminalSelectedVelocityTenthRadialSlopeErrorFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ) :
    H3FourierComplexL2 :=
  h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
    10 (by norm_num)
    hNS ht₀ hE hTail hQ hQR i hx h

end

end Euclidean
end Bridge
end PrimeTensor

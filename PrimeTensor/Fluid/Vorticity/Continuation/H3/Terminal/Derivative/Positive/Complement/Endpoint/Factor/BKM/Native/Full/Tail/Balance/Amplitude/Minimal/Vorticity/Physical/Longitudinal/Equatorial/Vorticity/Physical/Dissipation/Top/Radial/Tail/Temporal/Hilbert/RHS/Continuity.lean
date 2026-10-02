import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Sixth.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2.Continuity

/-!
# Strong Fourier L² continuity of the weighted top-tail PDE RHS

For the cutoff-independent Hilbert path

    q(ξ)² û_j(t,ξ),

the unit-viscosity Fourier Navier--Stokes equation gives the formal derivative

    -q(ξ)³ û_j(t,ξ)
      -
    q(ξ)² F_j(U(t),U(t))(ξ),

where

    q(ξ) = h3FourierGradientSquare ξ
         = (2π)² |ξ|².

The preceding checkpoint supplied strong continuity of the sixth Euclidean
radial velocity state on every positive compact restart slab.  The selected
forcing library already supplies strong continuity of the fourth Euclidean
radial forcing state on every positive terminal-half slab.

Since

    q³ = (2π)^6 |ξ|^6,
    q² = (2π)^4 |ξ|^4,

those two results are exactly the two terms above.

This file packages the weighted PDE right-hand side as a genuine
`H3FourierComplexL2` path on `[q/2,q]`, proves its strong continuity, and
identifies its almost-everywhere representative first in Euclidean radial
form and then in the intrinsic `h3FourierGradientSquare` form.

No temporal derivative theorem is asserted here.  The next step can combine
this continuous RHS with the already-existing raw Fourier integral evolution
to obtain the strong derivative of the global `q² û_j` Hilbert path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedRHS
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2000000

/-! ## Exact radial constants -/

/-- `q² = (2π)^4 |ξ|^4`. -/
theorem h3FourierGradientSquare_sq_eq_two_pi_four_mul_norm_four
    (ξ : H3FourierPoint3) :
    h3FourierGradientSquare ξ ^ 2
      =
    (2 * Real.pi) ^ 4 * ‖ξ‖ ^ 4 := by

  unfold h3FourierGradientSquare
  ring

/-- `q³ = (2π)^6 |ξ|^6`. -/
theorem h3FourierGradientSquare_cube_eq_two_pi_six_mul_norm_six
    (ξ : H3FourierPoint3) :
    h3FourierGradientSquare ξ ^ 3
      =
    (2 * Real.pi) ^ 6 * ‖ξ‖ ^ 6 := by

  unfold h3FourierGradientSquare
  ring

/-! ## Weighted PDE right-hand side on a terminal-half slab -/

/--
The cutoff-independent weighted Fourier RHS

    `-q³ û_j - q² F_j`

on one positive selected terminal-half slab `[q/2,q]`.

The definition is made from the quotient-safe sixth-radial velocity and
fourth-radial forcing states, with the exact `(2π)` conversion constants.
-/
noncomputable def h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (q / 2) q) :
    H3FourierComplexL2 :=
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail
  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE
  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail
  let hhalf : 0 < q / 2 := by
    positivity
  let c6 : ℝ := (2 * Real.pi) ^ 6
  let c4 : ℝ := (2 * Real.pi) ^ 4
  (-c6) •
      h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        hhalf hqR s i
    -
  c4 •
      h3SelectedRestartForcingRadialFourierL2OnSlab
        4
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        hq hqR.le
        i s

/-! ## Almost-everywhere representatives -/

/--
The weighted RHS has the literal Euclidean radial representative

    `-(2π)^6 |ξ|^6 û_j - (2π)^4 |ξ|^4 F_j`.
-/
theorem h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab_ae_radial
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (q / 2) q) :
    (
      (
        h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
          hNS ht₀ hE hTail hq hqR i s :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (-((2 * Real.pi) ^ 6 : ℝ)) •
          (
            ((‖ξ‖ ^ 6 : ℝ) : ℂ)
              *
            (
              (
                h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState
                    hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  (s : ℝ)
                  i :
                H3FourierComplexL2
              ) ξ
            )
          )
        -
      ((2 * Real.pi) ^ 4 : ℝ) •
          (
            ((‖ξ‖ ^ 4 : ℝ) : ℂ)
              *
            h3RawFinLerayOuterProductDivergence
              (
                h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState
                    hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  (s : ℝ)
              )
              (
                h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState
                    hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  (s : ℝ)
              )
              i ξ
          )) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let hhalf : 0 < q / 2 := by
    positivity

  let V6 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hhalf hqR s i

  let F4 : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      4
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hq hqR.le
      i s

  have hV6 :=
    h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact_ae
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hhalf hqR s i

  have hF4 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      4
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hq hqR.le
      i s

  have hSmul6 :=
    MeasureTheory.Lp.coeFn_smul
      (-((2 * Real.pi) ^ 6 : ℝ))
      V6

  have hSmul4 :=
    MeasureTheory.Lp.coeFn_smul
      ((2 * Real.pi) ^ 4 : ℝ)
      F4

  have hSub :=
    MeasureTheory.Lp.coeFn_sub
      ((-((2 * Real.pi) ^ 6 : ℝ)) • V6)
      (((2 * Real.pi) ^ 4 : ℝ) • F4)

  unfold
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab

  filter_upwards [
    hV6,
    hF4,
    hSmul6,
    hSmul4,
    hSub
  ] with ξ hV6ξ hF4ξ hSmul6ξ hSmul4ξ hSubξ

  rw [hSubξ]
  simp only [Pi.sub_apply]
  rw [hSmul6ξ, hSmul4ξ]
  simp only [Pi.smul_apply]
  rw [hV6ξ, hF4ξ]

/--
Intrinsic multiplier form of the same representative:

    `-q(ξ)^3 û_j - q(ξ)^2 F_j`.
-/
theorem h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab_ae_gradientSquare
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (q / 2) q) :
    (
      (
        h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
          hNS ht₀ hE hTail hq hqR i s :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
        *
      (
        (
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState
              hNS ht₀ hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht₀ hE hTail)
            (s : ℝ)
            i :
          H3FourierComplexL2
        ) ξ
      )
        -
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
        *
      h3RawFinLerayOuterProductDivergence
        (
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState
              hNS ht₀ hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht₀ hE hTail)
            (s : ℝ)
        )
        (
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState
              hNS ht₀ hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht₀ hE hTail)
            (s : ℝ)
        )
        i ξ) := by

  have hRadial :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab_ae_radial
      hNS ht₀ hE hTail hq hqR i s

  filter_upwards [hRadial] with ξ hξ

  rw [hξ]

  have hQ2 :=
    h3FourierGradientSquare_sq_eq_two_pi_four_mul_norm_four ξ

  have hQ3 :=
    h3FourierGradientSquare_cube_eq_two_pi_six_mul_norm_six ξ

  rw [hQ2, hQ3]

  simp only [
    Complex.real_smul,
    Complex.ofReal_neg,
    Complex.ofReal_mul,
    Complex.ofReal_pow,
    Complex.ofReal_ofNat
  ]

  ring

/-! ## Strong continuity -/

/--
The exact weighted top-tail Fourier RHS is strongly continuous in `L²` on
every positive selected terminal-half slab.
-/
theorem continuous_h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3) :
    Continuous
      (h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
        hNS ht₀ hE hTail hq hqR i) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  have hhalf :
      0 < q / 2 := by
    positivity

  have hhalfLe :
      q / 2 ≤ q := by
    linarith

  have hV6 :
      Continuous
        (fun s : Set.Icc (q / 2) q =>
          h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀
            hhalf hqR s i) := by

    dsimp only [U₀, hA, hU₀]

    exact
      continuous_h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
        hNS ht₀ hE hTail
        hhalf hhalfLe hqR i

  have hF4 :
      Continuous
        (h3SelectedRestartForcingRadialFourierL2OnSlab
          4
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀
          hq hqR.le
          i) :=
    continuous_h3SelectedRestartForcingFourthRadialFourierL2OnSlab
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hq hqR.le
      i

  unfold
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab

  dsimp only

  have hScaledV6 :
      Continuous
        (fun s : Set.Icc (q / 2) q =>
          (-((2 * Real.pi) ^ 6 : ℝ)) •
            h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              hhalf hqR s i) := by
    exact
      Continuous.smul
        (continuous_const :
          Continuous
            (fun _ : Set.Icc (q / 2) q =>
              (-((2 * Real.pi) ^ 6 : ℝ))))
        hV6

  have hScaledF4 :
      Continuous
        (fun s : Set.Icc (q / 2) q =>
          ((2 * Real.pi) ^ 4 : ℝ) •
            h3SelectedRestartForcingRadialFourierL2OnSlab
              4
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              hq hqR.le
              i s) := by
    exact
      Continuous.smul
        (continuous_const :
          Continuous
            (fun _ : Set.Icc (q / 2) q =>
              ((2 * Real.pi) ^ 4 : ℝ)))
        hF4

  exact
    hScaledV6.sub hScaledF4

end

end Euclidean
end Bridge
end PrimeTensor

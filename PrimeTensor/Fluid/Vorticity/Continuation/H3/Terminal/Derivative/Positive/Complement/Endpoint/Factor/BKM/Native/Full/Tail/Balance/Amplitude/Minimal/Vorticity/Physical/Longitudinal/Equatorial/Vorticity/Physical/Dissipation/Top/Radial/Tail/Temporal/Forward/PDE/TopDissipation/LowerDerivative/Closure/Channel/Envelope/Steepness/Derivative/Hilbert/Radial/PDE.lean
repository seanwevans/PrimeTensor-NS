import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Raw.Derivative

/-!
# Selected q³ velocity state and its continuous PDE RHS

The sixth-diffusion Hilbert obstruction is carried by

    q(ξ)³ û_j(t,ξ),

where

    q(ξ) = h3FourierGradientSquare ξ = (2π)² |ξ|².

Its unit-viscosity Fourier Navier--Stokes derivative candidate is

    -q(ξ)^4 û_j(t,ξ) - q(ξ)^3 F_j(t,ξ).

The preceding generic radial checkpoints now supply exactly the required
strong Fourier `L²` paths:

* radial order six for `q³ û_j`;
* radial order eight for `q⁴ û_j`;
* radial order six for `q³ F_j`.

This file packages the higher weighted velocity and RHS on a positive selected
terminal-half slab, proves strong continuity of both, gives their literal
Fourier representatives, and identifies the higher RHS almost everywhere with

    q³ × (unweighted projected Fourier RHS).

That last identity is the interface required by the next cutoff/FTC evolution
checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSixthDiffusionPDEState
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2200000

/-! ## Exact intrinsic/radial conversion constants -/

/-- `q³ = (2π)^6 |ξ|^6`. -/
theorem h3FourierGradientSquare_cube_eq_two_pi_six_mul_norm_six_high
    (ξ : H3FourierPoint3) :
    h3FourierGradientSquare ξ ^ 3
      =
    (2 * Real.pi) ^ 6 * ‖ξ‖ ^ 6 := by
  unfold h3FourierGradientSquare
  ring

/-- `q⁴ = (2π)^8 |ξ|^8`. -/
theorem h3FourierGradientSquare_fourth_eq_two_pi_eight_mul_norm_eight
    (ξ : H3FourierPoint3) :
    h3FourierGradientSquare ξ ^ 4
      =
    (2 * Real.pi) ^ 8 * ‖ξ‖ ^ 8 := by
  unfold h3FourierGradientSquare
  ring

/-! ## The selected q³ velocity state -/

/--
The selected intrinsic `q³ û_j` state on a positive terminal-half slab.
-/
noncomputable def h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    H3FourierComplexL2 :=
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail
  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE
  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail
  let hhalf : 0 < Q / 2 := by
    positivity
  ((2 * Real.pi) ^ 6 : ℝ) •
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      6 (by norm_num)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ hhalf hQR s j

/--
The selected higher weighted velocity has the literal intrinsic representative

    q³ û_j.
-/
theorem h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail
    (
      (
        h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR j s :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
        (
          (
            h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              (s : ℝ)
              j :
            H3FourierComplexL2
          ) ξ
        )) := by

  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let hhalf : 0 < Q / 2 := by
    positivity

  let V6 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      6 (by norm_num)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ hhalf hQR s j

  have hV6 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      6 (by norm_num)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ hhalf hQR s j

  have hSmul :=
    MeasureTheory.Lp.coeFn_smul
      ((2 * Real.pi) ^ 6 : ℝ)
      V6

  unfold
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab

  filter_upwards [hV6, hSmul]
    with ξ hV6ξ hSmulξ

  rw [hSmulξ]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hV6ξ]

  rw [
    h3FourierGradientSquare_cube_eq_two_pi_six_mul_norm_six_high
      ξ
  ]

  simp only [
    Complex.ofReal_mul,
    Complex.ofReal_pow,
    Complex.ofReal_ofNat
  ]

  ring

/--
The selected `q³ û_j` state is strongly continuous on the whole closed
terminal-half slab.
-/
theorem continuous_h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3) :
    Continuous
      (h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
        hNS ht₀ hE hTail hQ hQR j) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let hhalf : 0 < Q / 2 := by
    positivity

  have hRadial :
      Continuous
        (fun s : Set.Icc (Q / 2) Q =>
          h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
            6 (by norm_num)
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀ hhalf hQR s j) := by
    exact
      continuous_h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
        6 (by norm_num)
        hNS ht₀ hE hTail
        hhalf (by linarith : Q / 2 ≤ Q) hQR j

  unfold
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab

  exact
    Continuous.smul
      (continuous_const :
        Continuous
          (fun _ : Set.Icc (Q / 2) Q =>
            ((2 * Real.pi) ^ 6 : ℝ)))
      hRadial

/-! ## The selected higher weighted PDE RHS -/

/--
The exact selected higher weighted Fourier PDE RHS

    -q⁴ û_j - q³ F_j

on the same positive terminal-half slab.
-/
noncomputable def h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    H3FourierComplexL2 :=
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail
  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE
  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail
  let hhalf : 0 < Q / 2 := by
    positivity
  let V8 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      8 (by norm_num)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ hhalf hQR s j
  let F6 : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      6
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le
      j s
  (-((2 * Real.pi) ^ 8 : ℝ)) • V8
    -
  ((2 * Real.pi) ^ 6 : ℝ) • F6

/--
The higher weighted RHS has the literal radial representative

    -(2π)^8 |ξ|^8 û_j - (2π)^6 |ξ|^6 F_j.
-/
theorem h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab_ae_radial
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail
    (
      (
        h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR j s :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (-((2 * Real.pi) ^ 8 : ℝ)) •
        (
          ((‖ξ‖ ^ 8 : ℝ) : ℂ) *
          (
            (
              h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                (one_pos : (0 : ℝ) < 1)
                U₀ hA hU₀
                (s : ℝ)
                j :
              H3FourierComplexL2
            ) ξ
          )
        )
        -
      ((2 * Real.pi) ^ 6 : ℝ) •
        (
          ((‖ξ‖ ^ 6 : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence
            (
              h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                (one_pos : (0 : ℝ) < 1)
                U₀ hA hU₀
                (s : ℝ)
            )
            (
              h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                (one_pos : (0 : ℝ) < 1)
                U₀ hA hU₀
                (s : ℝ)
            )
            j ξ
        )) := by

  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let hhalf : 0 < Q / 2 := by
    positivity

  let V8 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      8 (by norm_num)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ hhalf hQR s j

  let F6 : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      6
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ hQ hQR.le j s

  have hV8 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      8 (by norm_num)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ hhalf hQR s j

  have hF6 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      6
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ hQ hQR.le j s

  have hSmul8 :=
    MeasureTheory.Lp.coeFn_smul
      (-((2 * Real.pi) ^ 8 : ℝ))
      V8

  have hSmul6 :=
    MeasureTheory.Lp.coeFn_smul
      ((2 * Real.pi) ^ 6 : ℝ)
      F6

  have hSub :=
    MeasureTheory.Lp.coeFn_sub
      ((-((2 * Real.pi) ^ 8 : ℝ)) • V8)
      (((2 * Real.pi) ^ 6 : ℝ) • F6)

  unfold
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab

  filter_upwards [
    hV8,
    hF6,
    hSmul8,
    hSmul6,
    hSub
  ] with ξ hV8ξ hF6ξ hSmul8ξ hSmul6ξ hSubξ

  rw [hSubξ]
  simp only [Pi.sub_apply]
  rw [hSmul8ξ, hSmul6ξ]
  simp only [Pi.smul_apply]
  rw [hV8ξ, hF6ξ]

/--
Intrinsic form of the higher weighted RHS:

    -q⁴ û_j - q³ F_j.
-/
theorem h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab_ae_gradientSquare
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
    (
      (
        h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR j s :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (-(h3FourierGradientSquare ξ ^ 4 : ℝ) : ℂ) *
        (
          (
            h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              (s : ℝ)
              j :
            H3FourierComplexL2
          ) ξ
        )
        -
      ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence
          (W (s : ℝ))
          (W (s : ℝ))
          j ξ) := by

  dsimp only

  have hRadial :=
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab_ae_radial
      hNS ht₀ hE hTail hQ hQR j s

  filter_upwards [hRadial]
    with ξ hξ

  rw [hξ]

  rw [
    h3FourierGradientSquare_fourth_eq_two_pi_eight_mul_norm_eight
      ξ,
    h3FourierGradientSquare_cube_eq_two_pi_six_mul_norm_six_high
      ξ
  ]

  simp only [
    Complex.real_smul,
    Complex.ofReal_neg,
    Complex.ofReal_mul,
    Complex.ofReal_pow,
    Complex.ofReal_ofNat
  ]

  ring

/--
The higher weighted PDE RHS is strongly continuous on the whole closed
terminal-half slab.
-/
theorem continuous_h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3) :
    Continuous
      (h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
        hNS ht₀ hE hTail hQ hQR j) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let hhalf : 0 < Q / 2 := by
    positivity

  let V8 :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    fun s =>
      h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
        8 (by norm_num)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ hhalf hQR s j

  let F6 :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      6
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ hQ hQR.le j

  have hV8 :
      Continuous V8 := by
    dsimp only [V8]
    exact
      continuous_h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
        8 (by norm_num)
        hNS ht₀ hE hTail
        hhalf (by linarith : Q / 2 ≤ Q) hQR j

  have hF6 :
      Continuous F6 := by
    dsimp only [F6]
    exact
      continuous_h3SelectedRestartForcingRadialFourierL2OnSlab
        6
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        hQ hQR.le j

  unfold
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab

  exact
    (Continuous.smul
      (continuous_const :
        Continuous
          (fun _ : Set.Icc (Q / 2) Q =>
            (-((2 * Real.pi) ^ 8 : ℝ))))
      hV8).sub
    (Continuous.smul
      (continuous_const :
        Continuous
          (fun _ : Set.Icc (Q / 2) Q =>
            ((2 * Real.pi) ^ 6 : ℝ)))
      hF6)

/-! ## Exact q³ multiplier relation to the raw projected RHS -/

/--
On the terminal-half slab, the higher weighted PDE RHS is almost everywhere
`q³` times the already-constructed unweighted projected Fourier RHS.

This is the exact bridge needed by the next truncation/FTC evolution proof.
-/
theorem h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab_ae_eq_qcube_projectedRHS
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let qRadius :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨
        (s : ℝ),
        (
          lt_of_lt_of_le
            (by positivity : 0 < Q / 2)
            s.property.1
        ).le,
        (
          lt_of_le_of_lt
            s.property.2
            hQR
        ).le
      ⟩
    (
      (
        h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR j s :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
        (
          (
            h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
              hNS ht₀ hE hTail qRadius j :
            H3FourierComplexL2
          ) ξ
        )) := by

  dsimp only

  let qRadius :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨
      (s : ℝ),
      (
        lt_of_lt_of_le
          (by positivity : 0 < Q / 2)
          s.property.1
      ).le,
      (
        lt_of_le_of_lt
          s.property.2
          hQR
      ).le
    ⟩

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht₀ hE hTail qRadius

  have hProjected :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_ae_eq_unitPDE
      hNS ht₀ hE hTail qRadius j

  have hWeighted :=
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab_ae_gradientSquare
      hNS ht₀ hE hTail hQ hQR j s

  filter_upwards [hProjected, hWeighted]
    with ξ hProjectedξ hWeightedξ

  rw [hWeightedξ, hProjectedξ]

  dsimp only [U, qRadius] at *

  unfold
    h3PreterminalSelectedUnitSpectralStateOnRadius
    at *

  simp only [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2,
    h3SpectralFinCoordinateRawFourierL2CLM_apply,
    Complex.ofReal_neg,
    Complex.ofReal_mul,
    Complex.ofReal_pow
  ] at *

  ring

end

end Euclidean
end Bridge
end PrimeTensor

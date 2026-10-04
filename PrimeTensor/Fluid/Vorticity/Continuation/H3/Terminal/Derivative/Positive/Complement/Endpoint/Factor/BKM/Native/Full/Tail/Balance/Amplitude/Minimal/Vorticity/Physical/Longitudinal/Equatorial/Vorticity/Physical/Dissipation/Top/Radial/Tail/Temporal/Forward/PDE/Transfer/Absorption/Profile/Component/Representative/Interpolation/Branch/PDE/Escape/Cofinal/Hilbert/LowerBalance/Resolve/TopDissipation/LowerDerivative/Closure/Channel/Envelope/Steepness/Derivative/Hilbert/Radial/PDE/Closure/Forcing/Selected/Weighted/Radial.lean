import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2.Continuity

/-!
# Arbitrary radial L² regularity of the selected projected RHS

The genuine H³ encoder for the selected velocity derivative uses only the
unweighted and `q²`-weighted projected right-hand side.  The nonlinear product
rule that follows needs more: the encoded derivative must inherit the
positive-time spatial smoothing already present in the selected solution.

For every natural radial order `m`, the unit-viscosity projected Fourier RHS is

    R_j = -q û_j - F_j,

so

    |ξ|^m R_j
      =
    -(2π)² |ξ|^(m+2) û_j - |ξ|^m F_j.

Both terms are already available generically:

* selected velocity radial `L²` at every order `m+2 ≥ 2`;
* selected forcing radial `L²` at every finite order `m`.

This file packages their difference as one canonical quotient-safe state,
proves its exact representative, and proves strong continuity on every
positive compact selected restart slab.

Thus the raw derivative carrier `R̂` now has every finite radial Fourier `L²`
weight, without reopening the Navier--Stokes or Duhamel arguments.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedProjectedRHSArbitraryRadial
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2200000

/--
Order-`m` Euclidean radial Fourier `L²` package of the selected projected RHS
on one positive compact slab.
-/
noncomputable def h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
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
  (-((2 * Real.pi) ^ 2 : ℝ)) •
      h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
        (m + 2) (by omega)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        hhalf hQR s i
    -
  h3SelectedRestartForcingRadialFourierL2OnSlab
    m
    (one_pos : (0 : ℝ) < 1)
    U₀ hA hU₀
    hQ hQR.le
    i s

/--
Literal PDE representative of the arbitrary radial package:

    `|ξ|^m (-q û_j - F_j)`.
-/
theorem h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab_ae_pde
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
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
        h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
          m hNS ht₀ hE hTail hQ hQR i s :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (
          -(h3FourierGradientSquare ξ : ℂ) *
              (
                (
                  h3SpectralScalarRawFourierL2
                    (W (s : ℝ) i) :
                  H3FourierComplexL2
                ) ξ
              )
            -
          h3RawFinLerayOuterProductDivergence
            (W (s : ℝ)) (W (s : ℝ)) i ξ
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

  have hhalf :
      0 < Q / 2 := by
    positivity

  let V : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      (m + 2) (by omega)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hhalf hQR s i

  let F : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      m
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le
      i s

  have hV :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      (m + 2) (by omega)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hhalf hQR s i

  have hF :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      m
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le
      i s

  have hScaled :=
    MeasureTheory.Lp.coeFn_smul
      (-((2 * Real.pi) ^ 2 : ℝ))
      V

  have hSub :=
    MeasureTheory.Lp.coeFn_sub
      ((-((2 * Real.pi) ^ 2 : ℝ)) • V)
      F

  have hRaw :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
      (t := (s : ℝ))
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ i

  have hStateRaw :=
    h3SpectralScalarRawFourierL2_ae
      (
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀
          (s : ℝ)
          i
      )

  unfold
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab

  filter_upwards [
    hV,
    hF,
    hScaled,
    hSub,
    hRaw,
    hStateRaw
  ] with ξ hVξ hFξ hScaledξ hSubξ hRawξ hStateRawξ

  rw [hSubξ]
  simp only [Pi.sub_apply]
  rw [hScaledξ]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hVξ, hFξ, hRawξ, hStateRawξ]

  rw [pow_add]

  unfold h3FourierGradientSquare

  simp only [
    Complex.ofReal_neg,
    Complex.ofReal_mul,
    Complex.ofReal_pow,
    Complex.ofReal_ofNat
  ]

  ring

/--
The generic radial package is exactly `|ξ|^m` times the canonical unweighted
selected projected-RHS coordinate.
-/
theorem h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab_ae_eq_radial_projectedRHS
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let qRadius :=
      h3SelectedProjectedRHSSlabRadius hE hQ hQR s
    (
      (
        h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
          m hNS ht₀ hE hTail hQ hQR i s :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (
          (
            h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
              hNS ht₀ hE hTail qRadius i :
            H3FourierComplexL2
          ) ξ
        )) := by

  dsimp only

  let qRadius :=
    h3SelectedProjectedRHSSlabRadius hE hQ hQR s

  have hRadial :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab_ae_pde
      m hNS ht₀ hE hTail hQ hQR i s

  have hProjected :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_ae_eq_unitPDE
      hNS ht₀ hE hTail qRadius i

  filter_upwards [hRadial, hProjected]
    with ξ hRadialξ hProjectedξ

  rw [hRadialξ, hProjectedξ]

  dsimp only [
    qRadius,
    h3SelectedProjectedRHSSlabRadius
  ] at *

  unfold
    h3PreterminalSelectedUnitSpectralStateOnRadius
    at *

  simp only [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2,
    h3SpectralFinCoordinateRawFourierL2CLM_apply
  ] at *

/--
Every finite radial projected-RHS state is strongly continuous on the selected
positive compact slab.
-/
theorem continuous_h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3) :
    Continuous
      (h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
        m hNS ht₀ hE hTail hQ hQR i) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  have hhalf :
      0 < Q / 2 := by
    positivity

  have hhalfLe :
      Q / 2 ≤ Q := by
    linarith

  have hV :
      Continuous
        (fun s : Set.Icc (Q / 2) Q =>
          h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
            (m + 2) (by omega)
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀
            hhalf hQR s i) := by
    dsimp only [U₀, hA, hU₀]
    exact
      continuous_h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
        (m + 2) (by omega)
        hNS ht₀ hE hTail
        hhalf hhalfLe hQR i

  have hF :
      Continuous
        (h3SelectedRestartForcingRadialFourierL2OnSlab
          m
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀
          hQ hQR.le
          i) :=
    continuous_h3SelectedRestartForcingRadialFourierL2OnSlab
      m
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le
      i

  unfold
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab

  dsimp only

  have hScaled :
      Continuous
        (fun s : Set.Icc (Q / 2) Q =>
          (-((2 * Real.pi) ^ 2 : ℝ)) •
            h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
              (m + 2) (by omega)
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              hhalf hQR s i) := by
    exact
      Continuous.smul
        (continuous_const :
          Continuous
            (fun _ : Set.Icc (Q / 2) Q =>
              (-((2 * Real.pi) ^ 2 : ℝ))))
        hV

  exact
    hScaled.sub hF

/-! ## Orders needed by the forcing-time product rule -/

/-- Sixth radial selected projected RHS, enough for the order-two forcing
product-rule input moments after one additional moment conversion. -/
noncomputable def h3PreterminalSelectedProjectedRHSSixthRadialFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    H3FourierComplexL2 :=
  h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
    6 hNS ht₀ hE hTail hQ hQR i s

/-- Tenth radial selected projected RHS, reserved for the order-four forcing
product-rule input moments. -/
noncomputable def h3PreterminalSelectedProjectedRHSTenthRadialFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    H3FourierComplexL2 :=
  h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
    10 hNS ht₀ hE hTail hQ hQR i s

end

end Euclidean
end Bridge
end PrimeTensor

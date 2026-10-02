import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Closure

/-!
# Restricted Hilbert pairing for the weighted top-tail PDE

The cutoff-independent strong derivative is now closed.  The remaining scalar
step is static.

For one global Fourier `L²` pair with almost-everywhere representatives

    X(ξ) = q(ξ)^2 u(ξ),
    Y(ξ) = -q(ξ)^3 u(ξ) - q(ξ)^2 F(ξ),

restrict both states to the sharp radial tail.  Their real Hilbert pairing is

    2 ⟪X,Y⟫_ℝ
      =
    ∫tail
      [-2 q^5 |u|^2
       -2 q^4 Re ⟪u,F⟫_ℂ].

This is exactly the coordinatewise diffusion-plus-transfer algebra needed by
the final physical pairing identification.

No temporal derivative or selected/old argument appears here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedPairingIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1400000

/-! ## Generic real pairing after restriction -/

/--
The real Hilbert pairing of two globally defined Fourier `L²` states after
restriction to a measurable radial tail is the integral of the real part of
their pointwise complex pairing.
-/
theorem inner_h3TerminalPhysicalTopDissipationRadialTailRestrictCLM_eq_integral_re_inner
    (R : ℝ)
    (F G : H3FourierComplexL2) :
    inner ℝ
        (h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R F)
        (h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R G)
      =
    ∫ ξ : H3FourierPoint3,
      Complex.re
        (inner ℂ (F ξ) (G ξ))
      ∂(
        (volume : Measure H3FourierPoint3).restrict
          (h3TerminalRadialFrequencyBelow R)ᶜ
      ) := by

  let S : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow R)ᶜ

  let RF :
      Lp ℂ 2
        ((volume : Measure H3FourierPoint3).restrict S) :=
    h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R F

  let RG :
      Lp ℂ 2
        ((volume : Measure H3FourierPoint3).restrict S) :=
    h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R G

  have hRF :
      ((RF :
          Lp ℂ 2
            ((volume : Measure H3FourierPoint3).restrict S)) :
        H3FourierPoint3 → ℂ)
        =ᵐ[
          (volume : Measure H3FourierPoint3).restrict S
        ]
      F := by

    dsimp only [RF, S]

    unfold
      h3TerminalPhysicalTopDissipationRadialTailRestrictCLM

    exact
      MeasureTheory.LpToLpRestrictCLM_coeFn
        ℝ
        (h3TerminalRadialFrequencyBelow R)ᶜ
        F

  have hRG :
      ((RG :
          Lp ℂ 2
            ((volume : Measure H3FourierPoint3).restrict S)) :
        H3FourierPoint3 → ℂ)
        =ᵐ[
          (volume : Measure H3FourierPoint3).restrict S
        ]
      G := by

    dsimp only [RG, S]

    unfold
      h3TerminalPhysicalTopDissipationRadialTailRestrictCLM

    exact
      MeasureTheory.LpToLpRestrictCLM_coeFn
        ℝ
        (h3TerminalRadialFrequencyBelow R)ᶜ
        G

  change
    inner ℝ RF RG
      =
    ∫ ξ : H3FourierPoint3,
      Complex.re
        (inner ℂ (F ξ) (G ξ))
      ∂((volume : Measure H3FourierPoint3).restrict S)

  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [hRF, hRG] with ξ hRFξ hRGξ

  rw [hRFξ, hRGξ]

  simp only [
    Complex.inner,
    RCLike.inner_apply
  ]

/-! ## Weighted PDE pointwise pairing -/

/--
For one scalar Fourier coordinate, if

    `X = q² u`
    `Y = -q³ u - q² F`

almost everywhere, then the restricted real Hilbert pairing expands exactly
into its diffusion and nonlinear-transfer integrands.
-/
theorem two_mul_inner_restrict_eq_weightedPDE_integral
    (R : ℝ)
    (X Y U F : H3FourierComplexL2)
    (hX :
      ((X : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        U ξ))
    (hY :
      ((Y : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
            *
          U ξ
          -
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          F ξ)) :
    2 *
      inner ℝ
        (h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R X)
        (h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R Y)
      =
    ∫ ξ : H3FourierPoint3,
      (
        (-2 : ℝ)
          *
        h3FourierGradientSquare ξ ^ 5
          *
        ‖U ξ‖ ^ 2
      )
        +
      (
        (-2 : ℝ)
          *
        h3FourierGradientSquare ξ ^ 4
          *
        (
          inner ℂ
            (U ξ)
            (F ξ)
        ).re
      )
      ∂(
        (volume : Measure H3FourierPoint3).restrict
          (h3TerminalRadialFrequencyBelow R)ᶜ
      ) := by

  rw [
    inner_h3TerminalPhysicalTopDissipationRadialTailRestrictCLM_eq_integral_re_inner
      R X Y
  ]

  rw [← integral_const_mul]

  apply integral_congr_ae

  have hXr :
      ((X : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        U ξ) :=
    ae_restrict_of_ae
      (s := (h3TerminalRadialFrequencyBelow R)ᶜ)
      hX

  have hYr :
      ((Y : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ]
      (fun ξ : H3FourierPoint3 =>
        (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
            *
          U ξ
          -
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          F ξ) :=
    ae_restrict_of_ae
      (s := (h3TerminalRadialFrequencyBelow R)ᶜ)
      hY

  filter_upwards [hXr, hYr] with ξ hXξ hYξ

  rw [hXξ, hYξ]

  let q : ℝ :=
    h3FourierGradientSquare ξ

  let z : ℂ :=
    U ξ

  let f : ℂ :=
    F ξ

  change
    2 *
      Complex.re
        (
          inner ℂ
            (((q ^ 2 : ℝ) : ℂ) * z)
            (
              ((-(q ^ 3 : ℝ) : ℂ) * z)
                -
              (((q ^ 2 : ℝ) : ℂ) * f)
            )
        )
      =
    (-2 : ℝ) * q ^ 5 * ‖z‖ ^ 2
      +
    (-2 : ℝ) * q ^ 4 * (inner ℂ z f).re

  have hComplex :
      inner ℂ
          (((q ^ 2 : ℝ) : ℂ) * z)
          (
            ((-(q ^ 3 : ℝ) : ℂ) * z)
              -
            (((q ^ 2 : ℝ) : ℂ) * f)
          )
        =
      ((-(q ^ 5 : ℝ)) : ℂ)
          *
        ((‖z‖ ^ 2 : ℝ) : ℂ)
        +
      ((-(q ^ 4 : ℝ)) : ℂ)
          *
        inner ℂ z f := by

    rw [inner_sub_right]

    simp only [
      RCLike.inner_apply,
      map_mul,
      Complex.conj_ofReal,
      Complex.ofReal_neg
    ]

    have hz :
        z * (starRingEnd ℂ) z
          =
        ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      simpa using
        (RCLike.mul_conj z)

    rw [← hz]

    push_cast

    ring

  rw [hComplex]

  simp only [
    Complex.add_re,
    Complex.mul_re,
    Complex.neg_re,
    Complex.neg_im,
    Complex.ofReal_re,
    Complex.ofReal_im,
    neg_zero,
    zero_mul,
    mul_zero,
    sub_zero
  ]

  ring

end

end Euclidean
end Bridge
end PrimeTensor

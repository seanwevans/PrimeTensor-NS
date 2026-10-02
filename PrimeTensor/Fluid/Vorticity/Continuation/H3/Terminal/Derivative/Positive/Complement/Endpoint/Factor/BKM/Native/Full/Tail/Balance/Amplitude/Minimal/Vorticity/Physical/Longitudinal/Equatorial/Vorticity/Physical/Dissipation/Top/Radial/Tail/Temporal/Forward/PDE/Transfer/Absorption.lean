import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Majorant
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.Moment.Cauchy

/-!
# Absorb the sharp-tail nonlinear transfer into cubic forcing mass

The full-space absolute-transfer checkpoint removed the cutoff but discarded the
favorable viscous term.  A sharper reduction keeps that negative diffusion.

For one coordinate and one frequency, writing

    q = h3FourierGradientSquare ξ,
    z = raw(U_j)(ξ),
    f = F_j(U,U)(ξ),

the exact localized PDE density is

    -2 q^5 |z|^2 - 2 q^4 Re ⟪z,f⟫.

Since

    -Re ⟪z,f⟫ ≤ |z| |f|

and

    2 q^4 |z| |f|
      ≤ q^5 |z|^2 + q^3 |f|^2,

one full copy of the fifth-radial diffusion is absorbed and therefore

    -2 q^5 |z|^2 - 2 q^4 Re ⟪z,f⟫
      ≤ q^3 |f|^2.

The remaining cubic forcing density is genuinely integrable at every strict
time.  No new restart transport is needed: unweighted forcing is already
Fourier `L²`, while the preceding weighted-factor theorem gives `q² f ∈ L²`.
Thus both `|f|²` and `q⁴ |f|²` are integrable, and

    q³ ≤ 1 + q⁴

for `q ≥ 0`.

This file packages exactly those two ingredients.  The next layer only has to
integrate the pointwise inequality and sum over the three coordinates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailTransferAbsorption
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2200000

/-! ## Cubic weighted forcing density -/

/--
One coordinate of the full-space cubic weighted forcing square density.
-/
noncomputable def h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (ξ : H3FourierPoint3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  h3FourierGradientSquare ξ ^ 3
    *
  ‖h3RawFinLerayOuterProductDivergence
      U U j ξ‖ ^ 2

/--
For every nonnegative scalar frequency weight,

    q³ ≤ 1 + q⁴.

This elementary interpolation is the only weight comparison needed below.
-/
theorem pow_three_le_one_add_pow_four_of_nonneg
    (q : ℝ)
    (hq : 0 ≤ q) :
    q ^ 3 ≤ 1 + q ^ 4 := by

  by_cases hqOne : q ≤ 1

  · have hPow :
        q ^ 3 ≤ 1 :=
      pow_le_one₀ hq hqOne

    have hFour :
        0 ≤ q ^ 4 :=
      pow_nonneg hq 4

    linarith

  · have hOne :
        1 ≤ q := by
      exact
        le_of_lt
          (lt_of_not_ge hqOne)

    have hProd :
        0 ≤ q ^ 3 * (q - 1) :=
      mul_nonneg
        (pow_nonneg hq 3)
        (sub_nonneg.mpr hOne)

    nlinarith [hProd]

/--
The cubic weighted forcing square density is integrable on the full Fourier
space at every strict physical time.
-/
theorem integrable_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    Integrable
      (h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClass ht j)
      (volume : Measure H3FourierPoint3) := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      U U j

  have hN2 :
      MemLp
        N
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_memLp2
        U U j

  let Fraw : H3FourierComplexL2 :=
    hN2.toLp N

  have hFrawAE :
      ((Fraw : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      N := by

    dsimp only [Fraw]

    exact
      MeasureTheory.MemLp.coeFn_toLp
        hN2

  obtain
    ⟨
      _V3,
      F2,
      _hV3,
      hF2
    ⟩ :=
    exists_h3TerminalPhysicalTopDissipationStrictTimeWeightedPDEFactors
      hH3 hClass ht j

  have hF2' :
      ((F2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        N ξ) := by

    simpa only [htAbs, U, N] using
      hF2

  have hZeroLp :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖Fraw ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp Fraw).norm.integrable_sq

  have hZero :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    refine
      hZeroLp.congr ?_

    filter_upwards [hFrawAE] with ξ hξ

    rw [hξ]

  have hFourLp :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖F2 ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp F2).norm.integrable_sq

  have hFour :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 4
            *
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    refine
      hFourLp.congr ?_

    filter_upwards [hF2'] with ξ hξ

    rw [hξ]

    have hq :
        0 ≤ h3FourierGradientSquare ξ :=
      h3FourierGradientSquare_nonneg ξ

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg
        (pow_nonneg hq 2)
    ]

    ring

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖N ξ‖ ^ 2
            +
          h3FourierGradientSquare ξ ^ 4
            *
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    hZero.add hFour

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 3
            *
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    exact
      (h3FourierGradientSquare_aestronglyMeasurable.pow 3).mul
        (
          (hN2.1.norm.aemeasurable.pow_const 2).aestronglyMeasurable
        )

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 3
            *
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    refine
      hMajor.mono'
        hTargetMeas
        ?_

    filter_upwards with ξ

    let q : ℝ :=
      h3FourierGradientSquare ξ

    let m : ℝ :=
      ‖N ξ‖ ^ 2

    have hq :
        0 ≤ q := by
      dsimp only [q]
      exact
        h3FourierGradientSquare_nonneg ξ

    have hm :
        0 ≤ m := by
      dsimp only [m]
      positivity

    have hWeight :
        q ^ 3 ≤ 1 + q ^ 4 :=
      pow_three_le_one_add_pow_four_of_nonneg
        q hq

    have hMul :
        q ^ 3 * m
          ≤
        (1 + q ^ 4) * m :=
      mul_le_mul_of_nonneg_right
        hWeight
        hm

    rw [
      Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg
          (pow_nonneg hq 3)
          hm)
    ]

    dsimp only [q, m]

    nlinarith [hMul]

  unfold
    h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt

  dsimp only [htAbs, U, N] at hTarget ⊢

  exact
    hTarget

/-! ## Pointwise weighted-Young absorption -/

/--
Abstract scalar form of the weighted-Young absorption used by the localized
top-tail PDE density.
-/
theorem topDissipationPDEDensity_le_cubicForcing_of_nonneg
    (q : ℝ)
    (hq : 0 ≤ q)
    (z f : ℂ) :
    (-2 : ℝ)
          *
        (q ^ 5 * ‖z‖ ^ 2)
      +
    (-2 : ℝ)
          *
        (q ^ 4 * (inner ℂ z f).re)
      ≤
    q ^ 3 * ‖f‖ ^ 2 := by

  have hNegRe :
      -(inner ℂ z f).re
        ≤
      ‖z‖ * ‖f‖ := by

    calc
      -(inner ℂ z f).re
          ≤
        abs ((inner ℂ z f).re) :=
        neg_le_abs _
      _ ≤
        ‖inner ℂ z f‖ := by
        exact
          Complex.abs_re_le_norm
            (inner ℂ z f)
      _ ≤
        ‖z‖ * ‖f‖ :=
        norm_inner_le_norm z f

  have hq4 :
      0 ≤ 2 * q ^ 4 := by
    positivity

  have hNonlinear :
      (-2 : ℝ)
            *
          (q ^ 4 * (inner ℂ z f).re)
        ≤
      2 * q ^ 4 * (‖z‖ * ‖f‖) := by

    calc
      (-2 : ℝ)
            *
          (q ^ 4 * (inner ℂ z f).re)
          =
        (2 * q ^ 4)
          *
        (-(inner ℂ z f).re) := by
        ring
      _ ≤
        (2 * q ^ 4)
          *
        (‖z‖ * ‖f‖) :=
        mul_le_mul_of_nonneg_left
          hNegRe
          hq4

  have hWeightedSquare :
      0
        ≤
      q ^ 3
        *
      (q * ‖z‖ - ‖f‖) ^ 2 :=
    mul_nonneg
      (pow_nonneg hq 3)
      (sq_nonneg _)

  have hYoung :
      2 * q ^ 4 * (‖z‖ * ‖f‖)
        ≤
      q ^ 5 * ‖z‖ ^ 2
        +
      q ^ 3 * ‖f‖ ^ 2 := by

    nlinarith [hWeightedSquare]

  have hDiffusionNonneg :
      0 ≤ q ^ 5 * ‖z‖ ^ 2 :=
    mul_nonneg
      (pow_nonneg hq 5)
      (sq_nonneg _)

  calc
    (-2 : ℝ)
          *
        (q ^ 5 * ‖z‖ ^ 2)
      +
    (-2 : ℝ)
          *
        (q ^ 4 * (inner ℂ z f).re)
        ≤
      (-2 : ℝ)
          *
        (q ^ 5 * ‖z‖ ^ 2)
      +
      2 * q ^ 4 * (‖z‖ * ‖f‖) := by
      exact
        add_le_add
          le_rfl
          hNonlinear
    _ ≤
      (-2 : ℝ)
          *
        (q ^ 5 * ‖z‖ ^ 2)
      +
      (
        q ^ 5 * ‖z‖ ^ 2
          +
        q ^ 3 * ‖f‖ ^ 2
      ) := by
      exact
        add_le_add
          le_rfl
          hYoung
    _ ≤
      q ^ 3 * ‖f‖ ^ 2 := by
      linarith

/--
Specialized pointwise bound for the canonical terminal state: the exact
diffusion-plus-nonlinear coordinate density is bounded above by the cubic
weighted forcing square density.
-/
theorem h3TerminalPhysicalTopDissipationPDECoordinateDensity_le_forcingCubic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (-2 : ℝ)
          *
        (
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2
              (U j) ξ‖ ^ 2
        )
      +
    (-2 : ℝ)
          *
        (
          h3FourierGradientSquare ξ ^ 4
            *
          (
            inner ℂ
              (h3SpectralScalarRawFourierL2
                (U j) ξ)
              (h3RawFinLerayOuterProductDivergence
                U U j ξ)
          ).re
        )
      ≤
    h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
      hH3 hClass ht j ξ := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  have hq :
      0 ≤ h3FourierGradientSquare ξ :=
    h3FourierGradientSquare_nonneg ξ

  have h :=
    topDissipationPDEDensity_le_cubicForcing_of_nonneg
      (h3FourierGradientSquare ξ)
      hq
      (h3SpectralScalarRawFourierL2
        (U j) ξ)
      (h3RawFinLerayOuterProductDivergence
        U U j ξ)

  unfold
    h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt

  simpa only [htAbs, U] using
    h

/-! ## Full cubic forcing mass -/

/--
The full-space cubic weighted forcing square mass at one strict physical time.
-/
noncomputable def h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) : ℝ :=
  ∑ j : Fin 3,
    ∫ ξ : H3FourierPoint3,
      h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClass ht j ξ
      ∂(volume : Measure H3FourierPoint3)

/--
The strict-time full cubic forcing mass is nonnegative.
-/
theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    0
      ≤
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
      hH3 hClass ht := by

  unfold
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt

  apply
    Finset.sum_nonneg

  intro j hj

  apply
    integral_nonneg

  intro ξ

  unfold
    h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt

  exact
    mul_nonneg
      (pow_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        3)
      (sq_nonneg _)

end

end Euclidean
end Bridge
end PrimeTensor

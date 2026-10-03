import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Escape

/-!
# Adjacent radial forcing masses around the cubic obstruction

The fixed physical forcing channel isolated above carries the cubic
square-gradient mass

    M₃(t) = ∫ q(ξ)³ |F_j(t,ξ)|² dξ,

where `q(ξ) = (2π)² |ξ|²`.

The fourth-radial PDE representative uses the stronger forcing factor
`q² F_j`, whose squared Hilbert norm is

    M₄(t) = ∫ q(ξ)⁴ |F_j(t,ξ)|² dξ.

To enter that PDE branch without silently spending an extra Fourier power,
retain the neighboring lower mass

    M₂(t) = ∫ q(ξ)² |F_j(t,ξ)|² dξ.

At every strict physical time both neighboring masses are finite, and the
elementary pointwise inequality

    q³ ≤ q² + q⁴,   q ≥ 0,

gives

    M₃ ≤ M₂ + M₄.

Consequently, whenever the cubic forcing mass is above `2M`, at least one
neighboring mass is above `M`.  The next checkpoint can freeze this binary
order branch along a terminal subsequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailForcingAdjacentInterpolation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1400000

/-! ## Neighboring physical forcing densities and masses -/

noncomputable def h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
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
  h3FourierGradientSquare ξ ^ 2
    *
  ‖h3RawFinLerayOuterProductDivergence U U j ξ‖ ^ 2

noncomputable def h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
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
  h3FourierGradientSquare ξ ^ 4
    *
  ‖h3RawFinLerayOuterProductDivergence U U j ξ‖ ^ 2

noncomputable def h3TerminalPhysicalTopDissipationForcingSecondQMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
      hH3 hClass ht j ξ
    ∂(volume : Measure H3FourierPoint3)

noncomputable def h3TerminalPhysicalTopDissipationForcingFourthQMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
      hH3 hClass ht j ξ
    ∂(volume : Measure H3FourierPoint3)

/-! ## Strict-time finiteness -/

theorem integrable_h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    Integrable
      (h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
        hH3 hClass ht j)
      (volume : Measure H3FourierPoint3) := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence U U j

  obtain
    ⟨_V3, F2, _hV3, hF2⟩ :=
    exists_h3TerminalPhysicalTopDissipationStrictTimeWeightedPDEFactors
      hH3 hClass ht j

  have hF2' :
      ((F2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ) * N ξ) := by

    simpa only [htAbs, U, N] using hF2

  have hLp :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖F2 ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp F2).norm.integrable_sq

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 4
            *
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    refine hLp.congr ?_

    filter_upwards [hF2'] with ξ hξ

    rw [hξ]

    have hq :
        0 ≤ h3FourierGradientSquare ξ :=
      h3FourierGradientSquare_nonneg ξ

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hq 2)
    ]

    ring

  unfold
    h3TerminalPhysicalTopDissipationForcingFourthQDensityAt

  dsimp only [htAbs, U, N] at hTarget ⊢

  exact hTarget

private theorem pow_two_le_one_add_pow_four
    (q : ℝ) :
    q ^ 2 ≤ 1 + q ^ 4 := by

  nlinarith [sq_nonneg (q ^ 2 - 1)]

theorem integrable_h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    Integrable
      (h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
        hH3 hClass ht j)
      (volume : Measure H3FourierPoint3) := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence U U j

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

    refine hZeroLp.congr ?_

    filter_upwards [hFrawAE] with ξ hξ

    rw [hξ]

  have hFourRaw :=
    integrable_h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
      hH3 hClass ht j

  unfold
    h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
    at hFourRaw

  dsimp only at hFourRaw

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 4
          *
        ‖h3RawFinLerayOuterProductDivergence
            (h3TerminalVelocitySpectralStateAt hH3 t htAbs)
            (h3TerminalVelocitySpectralStateAt hH3 t htAbs)
            j ξ‖ ^ 2)
      (volume : Measure H3FourierPoint3)
    at hFourRaw

  have hFour :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 4
            *
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    simpa only [U, N] using hFourRaw

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
          h3FourierGradientSquare ξ ^ 2
            *
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    exact
      (h3FourierGradientSquare_aestronglyMeasurable.pow 2).mul
        (
          (hN2.1.norm.aemeasurable.pow_const 2).aestronglyMeasurable
        )

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 2
            *
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    refine hMajor.mono' hTargetMeas ?_

    filter_upwards with ξ

    let q : ℝ :=
      h3FourierGradientSquare ξ

    let m : ℝ :=
      ‖N ξ‖ ^ 2

    have hq :
        0 ≤ q := by
      dsimp only [q]
      exact h3FourierGradientSquare_nonneg ξ

    have hm :
        0 ≤ m := by
      dsimp only [m]
      positivity

    have hWeight :
        q ^ 2 ≤ 1 + q ^ 4 :=
      pow_two_le_one_add_pow_four q

    have hMul :
        q ^ 2 * m
          ≤
        (1 + q ^ 4) * m :=
      mul_le_mul_of_nonneg_right hWeight hm

    rw [
      Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg (pow_nonneg hq 2) hm)
    ]

    dsimp only [q, m]

    nlinarith [hMul]

  unfold
    h3TerminalPhysicalTopDissipationForcingSecondQDensityAt

  dsimp only [htAbs, U, N] at hTarget ⊢

  exact hTarget

/-! ## Cubic mass lies between the two neighboring orders -/

private theorem pow_three_le_pow_two_add_pow_four_of_nonneg
    (q : ℝ)
    (hq : 0 ≤ q) :
    q ^ 3 ≤ q ^ 2 + q ^ 4 := by

  by_cases hqOne : q ≤ 1

  · have hAux :
        0 ≤ q ^ 2 * (1 - q) :=
      mul_nonneg
        (pow_nonneg hq 2)
        (sub_nonneg.mpr hqOne)

    nlinarith [hAux]

  · have hOne :
        1 ≤ q :=
      le_of_lt (lt_of_not_ge hqOne)

    have hAux :
        0 ≤ q ^ 3 * (q - 1) :=
      mul_nonneg
        (pow_nonneg hq 3)
        (sub_nonneg.mpr hOne)

    nlinarith [hAux]

theorem integral_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt_le_secondQ_add_fourthQ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    (
      ∫ ξ : H3FourierPoint3,
        h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
          hH3 hClass ht j ξ
        ∂(volume : Measure H3FourierPoint3)
    )
      ≤
    h3TerminalPhysicalTopDissipationForcingSecondQMassAt
        hH3 hClass ht j
      +
    h3TerminalPhysicalTopDissipationForcingFourthQMassAt
        hH3 hClass ht j := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence U U j

  have hThird :
      Integrable
        (h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
          hH3 hClass ht j)
        (volume : Measure H3FourierPoint3) :=
    integrable_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
      hH3 hClass ht j

  have hSecond :
      Integrable
        (h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
          hH3 hClass ht j)
        (volume : Measure H3FourierPoint3) :=
    integrable_h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
      hH3 hClass ht j

  have hFourth :
      Integrable
        (h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
          hH3 hClass ht j)
        (volume : Measure H3FourierPoint3) :=
    integrable_h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
      hH3 hClass ht j

  have hMajor :
      Integrable
        (
          (h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
            hH3 hClass ht j)
            +
          (h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
            hH3 hClass ht j)
        )
        (volume : Measure H3FourierPoint3) :=
    hSecond.add hFourth

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
          h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
            hH3 hClass ht j ξ)
        ≤
      ∫ ξ : H3FourierPoint3,
        (
          h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
            hH3 hClass ht j
          +
          h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
            hH3 hClass ht j
        ) ξ := by

    apply integral_mono hThird hMajor

    intro ξ

    unfold
      h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
      h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
      h3TerminalPhysicalTopDissipationForcingFourthQDensityAt

    dsimp only

    let q : ℝ :=
      h3FourierGradientSquare ξ

    let m : ℝ :=
      ‖h3RawFinLerayOuterProductDivergence
          (h3TerminalVelocitySpectralStateAt
            hH3 t
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
          (h3TerminalVelocitySpectralStateAt
            hH3 t
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
          j ξ‖ ^ 2

    have hq :
        0 ≤ q := by
      dsimp only [q]
      exact h3FourierGradientSquare_nonneg ξ

    have hm :
        0 ≤ m := by
      dsimp only [m]
      positivity

    have hWeight :
        q ^ 3 ≤ q ^ 2 + q ^ 4 :=
      pow_three_le_pow_two_add_pow_four_of_nonneg
        q hq

    have hMul :
        q ^ 3 * m
          ≤
        (q ^ 2 + q ^ 4) * m :=
      mul_le_mul_of_nonneg_right hWeight hm

    change
      q ^ 3 * m
        ≤
      q ^ 2 * m + q ^ 4 * m

    calc
      q ^ 3 * m
          ≤
        (q ^ 2 + q ^ 4) * m :=
        hMul
      _ =
        q ^ 2 * m + q ^ 4 * m := by
        ring

  have hSplit :
      (∫ ξ : H3FourierPoint3,
        (
          h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
            hH3 hClass ht j
          +
          h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
            hH3 hClass ht j
        ) ξ)
        =
      (∫ ξ : H3FourierPoint3,
        h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
          hH3 hClass ht j ξ)
        +
      ∫ ξ : H3FourierPoint3,
        h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
          hH3 hClass ht j ξ := by

    simpa only [Pi.add_apply] using
      (integral_add hSecond hFourth)

  unfold
    h3TerminalPhysicalTopDissipationForcingSecondQMassAt
    h3TerminalPhysicalTopDissipationForcingFourthQMassAt

  exact
    hIntegral.trans_eq hSplit

/--
If one coordinate's cubic forcing mass is larger than `2M`, then at least one
adjacent square-gradient order has mass larger than `M`.
-/
theorem h3TerminalPhysicalTopDissipationForcingSecondQMassAt_or_fourthQMassAt_gt_of_two_mul_lt_cubic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (hLarge :
      2 * M
        <
      ∫ ξ : H3FourierPoint3,
        h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
          hH3 hClass ht j ξ
        ∂(volume : Measure H3FourierPoint3)) :
    M
        <
      h3TerminalPhysicalTopDissipationForcingSecondQMassAt
        hH3 hClass ht j
      ∨
    M
        <
      h3TerminalPhysicalTopDissipationForcingFourthQMassAt
        hH3 hClass ht j := by

  have hBound :=
    integral_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt_le_secondQ_add_fourthQ
      hH3 hClass ht j

  by_cases hSecond :
      M
        <
      h3TerminalPhysicalTopDissipationForcingSecondQMassAt
        hH3 hClass ht j

  · exact Or.inl hSecond

  · right

    have hSecondLe :
        h3TerminalPhysicalTopDissipationForcingSecondQMassAt
            hH3 hClass ht j
          ≤
        M :=
      le_of_not_gt hSecond

    by_contra hFourth

    have hFourthLe :
        h3TerminalPhysicalTopDissipationForcingFourthQMassAt
            hH3 hClass ht j
          ≤
        M :=
      le_of_not_gt hFourth

    linarith

/--
The existing Euclidean third-radial raw mass is exactly the cubic
square-gradient coordinate mass after multiplication by `(2π)^6`.
-/
theorem integral_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt_eq_two_pi_six_mul_rawThirdRadialMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    (
      ∫ ξ : H3FourierPoint3,
        h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
          hH3 hClass ht j ξ
        ∂(volume : Measure H3FourierPoint3)
    )
      =
    (2 * Real.pi) ^ 6
      *
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt
      hH3 hClass ht j := by

  rw [
    integral_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt_eq_norm_sq
      hH3 hClass ht j,
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt_eq_norm_sq
      hH3 hClass ht j
  ]

end

end Euclidean
end Bridge
end PrimeTensor

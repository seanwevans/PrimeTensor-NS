import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher

/-!
# Direct forcing-rate lower bounds on higher radial moments

The higher-dominated branch currently retains two inequalities at the same
selected time:

* the reciprocal-width rate is below a canonical quartic function of one
  radial-square channel `S`;
* a normalized copy of `S` is below the corresponding extended higher-radial
  moment.

For positive rate these combine algebraically.  The quartic square-root bound

    rate < C * (B * (2 * sqrt S))^4

is exactly

    rate < (16 * C * B^4) * S^2.

Since the left side is positive, the full coefficient is automatically
positive on any realized branch, even though the inverse-Bessel factor was
previously packaged only as nonnegative.  Thus

    sqrt (rate / (16 * C * B^4)) < S,

and the existing normalized channel domination gives a direct ENNReal lower
bound on the higher-radial moment.

This removes the intermediate radial-square channel from the quantitative
forcing-rate conclusion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

private theorem ofReal_scaled_sqrt_rate_div_quarticCoefficient_le_of_rate_lt_quarticSqrt_of_scaled_le
    {rate C B scale S : ℝ}
    {H : ℝ≥0∞}
    (hRatePos : 0 < rate)
    (hC0 : 0 ≤ C)
    (hB0 : 0 ≤ B)
    (hScale0 : 0 ≤ scale)
    (hS0 : 0 ≤ S)
    (hRate :
      rate
        <
      C * (B * (2 * Real.sqrt S)) ^ 4)
    (hDom :
      ENNReal.ofReal (scale * S)
        ≤
      H) :
    ENNReal.ofReal
        (
          scale
            *
          Real.sqrt
            (
              rate
                /
              (16 * C * B ^ 4)
            )
        )
      ≤
    H := by

  let K : ℝ :=
    16 * C * B ^ 4

  have hRoot4 :
      (Real.sqrt S) ^ 4
        =
      S ^ 2 := by

    calc
      (Real.sqrt S) ^ 4
          =
        ((Real.sqrt S) ^ 2) ^ 2 := by
          ring
      _ = S ^ 2 := by
        rw [Real.sq_sqrt hS0]

  have hQuartic :
      C * (B * (2 * Real.sqrt S)) ^ 4
        =
      K * S ^ 2 := by

    dsimp only [K]

    calc
      C * (B * (2 * Real.sqrt S)) ^ 4
          =
        C * (B ^ 4 * (2 * Real.sqrt S) ^ 4) := by
          rw [mul_pow]
      _ =
        C * (B ^ 4 * (16 * (Real.sqrt S) ^ 4)) := by
          ring
      _ =
        (16 * C * B ^ 4) * S ^ 2 := by
          rw [hRoot4]
          ring

  have hRateSimple :
      rate < K * S ^ 2 := by

    rw [← hQuartic]

    exact
      hRate

  have hK0 :
      0 ≤ K := by

    dsimp only [K]

    positivity

  have hKSqPos :
      0 < K * S ^ 2 :=
    lt_trans
      hRatePos
      hRateSimple

  have hKPos :
      0 < K := by

    by_contra hNot

    have hKLe :
        K ≤ 0 :=
      le_of_not_gt hNot

    have hKZero :
        K = 0 :=
      le_antisymm
        hKLe
        hK0

    rw [hKZero, zero_mul] at hKSqPos

    exact
      (lt_irrefl (0 : ℝ))
        hKSqPos

  have hRatio0 :
      0 ≤ rate / K :=
    div_nonneg
      hRatePos.le
      hKPos.le

  have hRatioLt :
      rate / K < S ^ 2 := by

    apply
      (div_lt_iff₀ hKPos).2

    nlinarith [hRateSimple]

  have hRootSq :
      (Real.sqrt (rate / K)) ^ 2
        =
      rate / K :=
    Real.sq_sqrt
      hRatio0

  have hRoot0 :
      0 ≤ Real.sqrt (rate / K) :=
    Real.sqrt_nonneg _

  have hRootLt :
      Real.sqrt (rate / K) < S := by

    nlinarith [hRootSq, hRatioLt]

  have hScaled :
      scale * Real.sqrt (rate / K)
        ≤
      scale * S :=
    mul_le_mul_of_nonneg_left
      (le_of_lt hRootLt)
      hScale0

  have hOfReal :
      ENNReal.ofReal
          (scale * Real.sqrt (rate / K))
        ≤
      ENNReal.ofReal (scale * S) :=
    ENNReal.ofReal_le_ofReal
      hScaled

  dsimp only [K] at hOfReal

  exact
    hOfReal.trans
      hDom

/-! ## Channel nonnegativity and normalization positivity -/

theorem h3TerminalForcingThirdQMoment14RadialSquareChannelAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (q : Fin 2) :
    0 ≤
      h3TerminalForcingThirdQMoment14RadialSquareChannelAt
        hH3 hClass ht j q := by

  fin_cases q

  · simp only [
      h3TerminalForcingThirdQMoment14RadialSquareChannelAt,
      Fin.isValue,
      Fin.zero_eta,
      ↓reduceIte
    ]

    exact
      h3TerminalForcingThirdQRawRadialSquareMassAt_nonneg
        hH3 hClass ht 14 j

  · simp only [
      h3TerminalForcingThirdQMoment14RadialSquareChannelAt,
      Fin.isValue,
      Fin.zero_eta,
      reduceCtorEq,
      ↓reduceIte
    ]

    exact
      h3TerminalForcingThirdQRawRadialSquareMassAt_nonneg
        hH3 hClass ht 16 j

theorem h3TerminalForcingFourthQMoment10RadialSquareChannelAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (q : Fin 2) :
    0 ≤
      h3TerminalForcingFourthQMoment10RadialSquareChannelAt
        hH3 hClass ht j q := by

  fin_cases q

  · simp only [
      h3TerminalForcingFourthQMoment10RadialSquareChannelAt,
      Fin.isValue,
      Fin.zero_eta,
      ↓reduceIte
    ]

    exact
      h3TerminalForcingFourthQRawRadialSquareMassAt_nonneg
        hH3 hClass ht 10 j

  · simp only [
      h3TerminalForcingFourthQMoment10RadialSquareChannelAt,
      Fin.isValue,
      Fin.zero_eta,
      reduceCtorEq,
      ↓reduceIte
    ]

    exact
      h3TerminalForcingFourthQRawRadialSquareMassAt_nonneg
        hH3 hClass ht 12 j

theorem h3TerminalForcingThirdQMoment14RadialSquareHigherScale_pos
    (q : Fin 2) :
    0 <
      h3TerminalForcingThirdQMoment14RadialSquareHigherScale q := by

  fin_cases q <;>
    simp [
      h3TerminalForcingThirdQMoment14RadialSquareHigherScale
    ] <;>
    positivity

theorem h3TerminalForcingFourthQMoment10RadialSquareHigherScale_pos
    (q : Fin 2) :
    0 <
      h3TerminalForcingFourthQMoment10RadialSquareHigherScale q := by

  fin_cases q <;>
    simp [
      h3TerminalForcingFourthQMoment10RadialSquareHigherScale
    ] <;>
    positivity

/-! ## Canonical direct rate coefficients -/

/--
Coefficient converting the resolved second-q quartic radial-square rate bound
into a square lower bound.
-/
noncomputable def h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient :
    ℝ :=
  16
    *
  (
    (
      (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
        *
      (2 * h3FourierMomentSplitCoefficient (6 : ℝ))
    )
      *
    256
  )
    *
  h3StandardInverseBesselWeightL2Factor ^ 4

/--
Coefficient converting the resolved fourth-q quartic radial-square rate bound
into a square lower bound.
-/
noncomputable def h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient :
    ℝ :=
  16
    *
  (
    (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
      *
    (2 * h3FourierMomentSplitCoefficient (10 : ℝ))
  )
    *
  h3StandardInverseBesselWeightL2Factor ^ 4

/-! ## Direct same-time rate-to-higher-moment bounds -/

/--
A positive resolved second-q reciprocal-width rate directly forces a lower
bound on the selected same-time extended higher-radial moment.
-/
theorem ofReal_thirdQHigherScale_mul_sqrt_secondQResolvedRate_le_extendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t rate : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (q : Fin 2)
    (hRatePos : 0 < rate)
    (hRate :
      rate
        <
      (
        (
          (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
            *
          (2 * h3FourierMomentSplitCoefficient (6 : ℝ))
        )
          *
        256
      )
        *
      (
        h3StandardInverseBesselWeightL2Factor
          *
        (
          2
            *
          Real.sqrt
            (
              h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                hH3 hClass ht j q
            )
        )
      ) ^ 4) :
    ENNReal.ofReal
        (
          h3TerminalForcingThirdQMoment14RadialSquareHigherScale q
            *
          Real.sqrt
            (
              rate
                /
              h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
            )
        )
      ≤
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass
      (h3TerminalForcingThirdQHigherRadialShift q)
      t
      ht := by

  let C : ℝ :=
    (
      (
        (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
          *
        (2 * h3FourierMomentSplitCoefficient (6 : ℝ))
      )
        *
      256
    )

  let B : ℝ :=
    h3StandardInverseBesselWeightL2Factor

  let scale : ℝ :=
    h3TerminalForcingThirdQMoment14RadialSquareHigherScale q

  let S : ℝ :=
    h3TerminalForcingThirdQMoment14RadialSquareChannelAt
      hH3 hClass ht j q

  have hSplit0 :
      0 ≤ h3FourierMomentSplitCoefficient (6 : ℝ) :=
    h3FourierMomentSplitCoefficient_nonneg
      (6 : ℝ)

  have hC0 :
      0 ≤ C := by

    dsimp only [C]

    positivity

  have hB0 :
      0 ≤ B := by

    dsimp only [B]

    exact
      h3StandardInverseBesselWeightL2Factor_nonneg

  have hScale0 :
      0 ≤ scale := by

    dsimp only [scale]

    exact
      (h3TerminalForcingThirdQMoment14RadialSquareHigherScale_pos q).le

  have hS0 :
      0 ≤ S := by

    dsimp only [S]

    exact
      h3TerminalForcingThirdQMoment14RadialSquareChannelAt_nonneg
        hH3 hClass ht j q

  have hDom :
      ENNReal.ofReal (scale * S)
        ≤
      h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass
        (h3TerminalForcingThirdQHigherRadialShift q)
        t
        ht := by

    dsimp only [scale, S]

    exact
      ofReal_scaled_h3TerminalForcingThirdQMoment14RadialSquareChannelAt_le_extendedHigherRadial
        hH3 hClass ht j q

  have hDirect :=
    ofReal_scaled_sqrt_rate_div_quarticCoefficient_le_of_rate_lt_quarticSqrt_of_scaled_le
      hRatePos
      hC0
      hB0
      hScale0
      hS0
      (by
        simpa only [C, B, S] using hRate)
      hDom

  simpa only [
    C,
    B,
    scale,
    S,
    h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient
  ] using
    hDirect

/--
A positive resolved fourth-q reciprocal-width rate directly forces a lower
bound on the selected same-time extended higher-radial moment.
-/
theorem ofReal_fourthQHigherScale_mul_sqrt_fourthQResolvedRate_le_extendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t rate : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (q : Fin 2)
    (hRatePos : 0 < rate)
    (hRate :
      rate
        <
      (
        (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
          *
        (2 * h3FourierMomentSplitCoefficient (10 : ℝ))
      )
        *
      (
        h3StandardInverseBesselWeightL2Factor
          *
        (
          2
            *
          Real.sqrt
            (
              h3TerminalForcingFourthQMoment10RadialSquareChannelAt
                hH3 hClass ht j q
            )
        )
      ) ^ 4) :
    ENNReal.ofReal
        (
          h3TerminalForcingFourthQMoment10RadialSquareHigherScale q
            *
          Real.sqrt
            (
              rate
                /
              h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
            )
        )
      ≤
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass
      (h3TerminalForcingFourthQHigherRadialShift q)
      t
      ht := by

  let C : ℝ :=
    (
      (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
        *
      (2 * h3FourierMomentSplitCoefficient (10 : ℝ))
    )

  let B : ℝ :=
    h3StandardInverseBesselWeightL2Factor

  let scale : ℝ :=
    h3TerminalForcingFourthQMoment10RadialSquareHigherScale q

  let S : ℝ :=
    h3TerminalForcingFourthQMoment10RadialSquareChannelAt
      hH3 hClass ht j q

  have hSplit0 :
      0 ≤ h3FourierMomentSplitCoefficient (10 : ℝ) :=
    h3FourierMomentSplitCoefficient_nonneg
      (10 : ℝ)

  have hC0 :
      0 ≤ C := by

    dsimp only [C]

    positivity

  have hB0 :
      0 ≤ B := by

    dsimp only [B]

    exact
      h3StandardInverseBesselWeightL2Factor_nonneg

  have hScale0 :
      0 ≤ scale := by

    dsimp only [scale]

    exact
      (h3TerminalForcingFourthQMoment10RadialSquareHigherScale_pos q).le

  have hS0 :
      0 ≤ S := by

    dsimp only [S]

    exact
      h3TerminalForcingFourthQMoment10RadialSquareChannelAt_nonneg
        hH3 hClass ht j q

  have hDom :
      ENNReal.ofReal (scale * S)
        ≤
      h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass
        (h3TerminalForcingFourthQHigherRadialShift q)
        t
        ht := by

    dsimp only [scale, S]

    exact
      ofReal_scaled_h3TerminalForcingFourthQMoment10RadialSquareChannelAt_le_extendedHigherRadial
        hH3 hClass ht j q

  have hDirect :=
    ofReal_scaled_sqrt_rate_div_quarticCoefficient_le_of_rate_lt_quarticSqrt_of_scaled_le
      hRatePos
      hC0
      hB0
      hScale0
      hS0
      (by
        simpa only [C, B, S] using hRate)
      hDom

  simpa only [
    C,
    B,
    scale,
    S,
    h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient
  ] using
    hDirect

end

end Euclidean
end Bridge
end PrimeTensor

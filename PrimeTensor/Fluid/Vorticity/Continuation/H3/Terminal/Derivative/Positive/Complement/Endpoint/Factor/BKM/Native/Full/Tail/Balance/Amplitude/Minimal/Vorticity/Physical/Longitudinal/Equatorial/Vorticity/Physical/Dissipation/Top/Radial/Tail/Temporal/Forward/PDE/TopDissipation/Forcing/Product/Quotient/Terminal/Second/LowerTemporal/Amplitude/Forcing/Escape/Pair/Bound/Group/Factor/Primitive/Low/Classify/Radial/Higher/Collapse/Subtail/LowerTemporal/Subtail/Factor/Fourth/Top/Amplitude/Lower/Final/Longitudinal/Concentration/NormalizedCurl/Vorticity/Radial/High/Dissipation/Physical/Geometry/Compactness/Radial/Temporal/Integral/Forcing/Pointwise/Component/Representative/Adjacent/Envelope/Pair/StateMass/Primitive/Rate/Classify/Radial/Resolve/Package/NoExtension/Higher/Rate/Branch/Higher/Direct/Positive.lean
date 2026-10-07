import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct

/-!
# Strict positivity of the direct higher-radial rate coefficients

The direct rate-to-higher-moment estimates divide by two canonical real
coefficients.  Their definitions contain the standard inverse-Bessel `L²`
factor, which had previously only been packaged as nonnegative.

The inverse-Bessel weight is continuous and strictly positive everywhere.
Its canonical Fourier `L²` representative is therefore nonzero, and its norm
square is exactly the integral appearing under the square root in the
inverse-Bessel factor.  Hence that factor is strictly positive.

This makes both direct forcing-rate coefficients strictly positive
independently of any realized branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3DirectHigherRatePositive
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-- The standard inverse-Bessel weight is strictly positive pointwise. -/
theorem h3StandardInverseBesselWeight_pos
    (ξ : H3FourierPoint3) :
    0 < h3StandardInverseBesselWeight ξ := by

  unfold h3StandardInverseBesselWeight

  exact
    inv_pos.mpr
      (by positivity)

/--
Canonical Fourier `L²` representative of the complex standard inverse-Bessel
weight.
-/
noncomputable def h3StandardInverseBesselWeightComplexL2 :
    H3FourierComplexL2 :=
  h3StandardInverseBesselWeightComplex_memLp2.toLp
    h3StandardInverseBesselWeightComplex

theorem h3StandardInverseBesselWeightComplexL2_ae :
    (h3StandardInverseBesselWeightComplexL2 :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3StandardInverseBesselWeightComplex := by

  exact
    MemLp.coeFn_toLp
      h3StandardInverseBesselWeightComplex_memLp2

/--
The canonical inverse-Bessel Fourier `L²` state is nonzero.
-/
theorem h3StandardInverseBesselWeightComplexL2_ne_zero :
    h3StandardInverseBesselWeightComplexL2 ≠ 0 := by

  intro hZero

  have hRep :=
    h3StandardInverseBesselWeightComplexL2_ae

  rw [hZero] at hRep

  have hContinuous :
      Continuous h3StandardInverseBesselWeightComplex := by

    unfold h3StandardInverseBesselWeightComplex

    exact
      Complex.continuous_ofReal.comp
        continuous_h3StandardInverseBesselWeight

  have hAeRaw :
      h3StandardInverseBesselWeightComplex
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (0 : H3FourierPoint3 → ℂ) := by

    exact
      hRep.symm.trans
        (
          Lp.coeFn_zero
            ℂ
            2
            (volume : Measure H3FourierPoint3)
        )

  have hEverywhere :
      h3StandardInverseBesselWeightComplex
        =
      (0 : H3FourierPoint3 → ℂ) := by

    exact
      (
        hContinuous.ae_eq_iff_eq
          (volume : Measure H3FourierPoint3)
          continuous_zero
      ).1
        hAeRaw

  have hValueNe :
      h3StandardInverseBesselWeightComplex
          (0 : H3FourierPoint3)
        ≠
      0 := by

    unfold
      h3StandardInverseBesselWeightComplex
      h3StandardInverseBesselWeight

    norm_num

  have hValueZero :
      h3StandardInverseBesselWeightComplex
          (0 : H3FourierPoint3)
        =
      0 := by

    have hAt :=
      congrFun
        hEverywhere
        (0 : H3FourierPoint3)

    simpa using
      hAt

  exact
    hValueNe
      hValueZero

/--
The integral under the inverse-Bessel `L²` factor is the squared norm of its
canonical Fourier `L²` representative.
-/
theorem integral_h3StandardInverseBesselWeight_sq_eq_norm_sq :
    (∫ ξ : H3FourierPoint3,
        h3StandardInverseBesselWeight ξ ^ 2
      ∂volume)
      =
    ‖h3StandardInverseBesselWeightComplexL2‖ ^ 2 := by

  calc
    (∫ ξ : H3FourierPoint3,
        h3StandardInverseBesselWeight ξ ^ 2
      ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3StandardInverseBesselWeightComplexL2 ξ‖ ^ 2
      ∂volume := by

        apply integral_congr_ae

        filter_upwards [
          h3StandardInverseBesselWeightComplexL2_ae
        ] with ξ hξ

        rw [hξ]

        unfold h3StandardInverseBesselWeightComplex

        simp only [
          Complex.norm_real,
          Real.norm_eq_abs,
          abs_of_pos (h3StandardInverseBesselWeight_pos ξ)
        ]

    _ =
      ‖h3StandardInverseBesselWeightComplexL2‖ ^ 2 := by

        exact
          (
            h3FourierComplexL2_norm_sq_eq_integral_norm_sq
              h3StandardInverseBesselWeightComplexL2
          ).symm

/--
The numerical `L²` factor of the standard inverse-Bessel weight is strictly
positive.
-/
theorem h3StandardInverseBesselWeightL2Factor_pos :
    0 < h3StandardInverseBesselWeightL2Factor := by

  unfold h3StandardInverseBesselWeightL2Factor

  rw [
    integral_h3StandardInverseBesselWeight_sq_eq_norm_sq
  ]

  have hNormPos :
      0 < ‖h3StandardInverseBesselWeightComplexL2‖ :=
    norm_pos_iff.mpr
      h3StandardInverseBesselWeightComplexL2_ne_zero

  exact
    Real.sqrt_pos.2
      (by nlinarith)

/-- Every generic Fourier moment split coefficient is strictly positive. -/
theorem h3FourierMomentSplitCoefficient_pos
    (q : ℝ) :
    0 < h3FourierMomentSplitCoefficient q := by

  unfold h3FourierMomentSplitCoefficient

  exact
    Real.rpow_pos_of_pos
      (by norm_num)
      q

/--
The direct second-q higher-radial rate coefficient is strictly positive.
-/
theorem h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient_pos :
    0 <
      h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient := by

  have hPair :
      0 <
        (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) :=
    h3TerminalForcingSecondQFixedPairCoefficient_pos

  have hSplit :
      0 <
        h3FourierMomentSplitCoefficient (6 : ℝ) :=
    h3FourierMomentSplitCoefficient_pos
      (6 : ℝ)

  have hBessel :
      0 <
        h3StandardInverseBesselWeightL2Factor :=
    h3StandardInverseBesselWeightL2Factor_pos

  unfold
    h3TerminalForcingSecondQResolvedHigherRadialRateCoefficient

  apply mul_pos

  · apply mul_pos
    · norm_num
    · apply mul_pos
      · apply mul_pos
        · exact pow_pos hPair 2
        · exact
            mul_pos
              (by norm_num)
              hSplit
      · norm_num

  · exact
      pow_pos
        hBessel
        4

/--
The direct fourth-q higher-radial rate coefficient is strictly positive.
-/
theorem h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient_pos :
    0 <
      h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient := by

  have hPair :
      0 <
        (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) :=
    h3TerminalForcingFourthQFixedPairCoefficient_pos

  have hSplit :
      0 <
        h3FourierMomentSplitCoefficient (10 : ℝ) :=
    h3FourierMomentSplitCoefficient_pos
      (10 : ℝ)

  have hBessel :
      0 <
        h3StandardInverseBesselWeightL2Factor :=
    h3StandardInverseBesselWeightL2Factor_pos

  unfold
    h3TerminalForcingFourthQResolvedHigherRadialRateCoefficient

  apply mul_pos

  · apply mul_pos
    · norm_num
    · exact
        mul_pos
          (pow_pos hPair 2)
          (
            mul_pos
              (by norm_num)
              hSplit
          )

  · exact
      pow_pos
        hBessel
        4

end

end Euclidean
end Bridge
end PrimeTensor

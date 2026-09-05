import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentMild

/-!
# Fréchet endpoint induction: all-orders positive-time free heat

The generic mild assembly isolates one analytic fact which was not previously
available in the repository: positive heat time must supply arbitrarily high
Fourier moments, not merely the existing moments through order three.

We prove this by a genuine semigroup induction.  For the successor step split

    H_t = H_{t/2} H_{t/2}.

The first heat half carries the already-proved `n` powers.  The second heat
half absorbs one additional radial power using the existing one-moment heat
bound.  Thus every natural Fourier moment has a finite explicit coefficient.

The bootstrap also needs the intermediate exponent `n + 3/4`.  That follows
from the same all-orders natural bound on one half of the heat time and the
already-compiled residual `3/4` bound on the other half.

Finally these multiplier bounds are transferred to the selected initial
free-heat raw Fourier `L²` package, with quantitative bounds in terms of the
restart-radius parameter `A`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentFreeHeat
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Recursive all-orders positive-time heat coefficient.

At a successor stage the heat time is split in half.  The first half carries
the existing `n` powers and the second half contributes one new radial power.
The one-power coefficient is the already-compiled order-one specialization of
`h3HeatFourierMomentMultiplier_le_three`. -/
noncomputable def h3HeatNatMomentCoefficient :
    ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | n + 1, ν, t =>
      h3HeatNatMomentCoefficient n ν (t / 2) *
        (Real.sqrt (ν * ((t / 2) / 3)))⁻¹

/-- The recursive all-orders heat coefficient is nonnegative. -/
theorem h3HeatNatMomentCoefficient_nonneg
    (n : ℕ)
    (ν t : ℝ) :
    0 ≤ h3HeatNatMomentCoefficient n ν t := by
  induction n generalizing t with
  | zero =>
      simp [h3HeatNatMomentCoefficient]
  | succ n ih =>
      simp only [h3HeatNatMomentCoefficient]
      exact
        mul_nonneg
          (ih (t / 2))
          (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- Every natural radial Fourier moment is uniformly absorbed by positive heat
time.  This removes the old `n ≤ 3` ceiling. -/
theorem h3HeatFourierMomentMultiplier_le_nat
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (n : ℕ)
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight (n : ℝ) ξ *
        ‖h3HeatFourierSymbol ν t ξ‖
      ≤
    h3HeatNatMomentCoefficient n ν t := by
  induction n generalizing t with
  | zero =>
      rw [h3FourierMomentWeight_natCast]
      simp only [pow_zero, one_mul, h3HeatNatMomentCoefficient]
      exact
        norm_h3HeatFourierSymbol_le_one
          hν.le ht.le ξ

  | succ n ih =>
      have hhalf : 0 < t / 2 := by
        positivity

      have hNat :
          h3FourierMomentWeight (n : ℝ) ξ *
              ‖h3HeatFourierSymbol ν (t / 2) ξ‖
            ≤
          h3HeatNatMomentCoefficient n ν (t / 2) :=
        ih (t := t / 2) hhalf

      have hNatPow :
          ‖ξ‖ ^ n *
              ‖h3HeatFourierSymbol ν (t / 2) ξ‖
            ≤
          h3HeatNatMomentCoefficient n ν (t / 2) := by
        simpa only [h3FourierMomentWeight_natCast] using hNat

      have hOneRaw :=
        h3HeatFourierMomentMultiplier_le_three
          hν hhalf 1 (by norm_num) ξ

      have hOne :
          ‖ξ‖ *
              ‖h3HeatFourierSymbol ν (t / 2) ξ‖
            ≤
          (Real.sqrt (ν * ((t / 2) / 3)))⁻¹ := by
        simpa only [pow_one] using hOneRaw

      have hSplit :
          ‖h3HeatFourierSymbol ν t ξ‖
            =
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖ *
            ‖h3HeatFourierSymbol ν (t / 2) ξ‖ := by
        have htSplit :
            (t / 2) + (t / 2) = t := by
          ring
        calc
          ‖h3HeatFourierSymbol ν t ξ‖
              =
            ‖h3HeatFourierSymbol ν ((t / 2) + (t / 2)) ξ‖ := by
              rw [htSplit]
          _ =
            ‖h3HeatFourierSymbol ν (t / 2) ξ *
              h3HeatFourierSymbol ν (t / 2) ξ‖ := by
              rw [h3HeatFourierSymbol_add]
          _ =
            ‖h3HeatFourierSymbol ν (t / 2) ξ‖ *
              ‖h3HeatFourierSymbol ν (t / 2) ξ‖ := by
              rw [norm_mul]

      have hNatCoeff0 :
          0 ≤ h3HeatNatMomentCoefficient n ν (t / 2) :=
        h3HeatNatMomentCoefficient_nonneg n ν (t / 2)

      have hOneLhs0 :
          0 ≤
            ‖ξ‖ *
              ‖h3HeatFourierSymbol ν (t / 2) ξ‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)

      rw [
        h3FourierMomentWeight_natCast,
        hSplit
      ]

      simp only [h3HeatNatMomentCoefficient]

      rw [pow_succ]

      calc
        (‖ξ‖ ^ n * ‖ξ‖) *
            (‖h3HeatFourierSymbol ν (t / 2) ξ‖ *
              ‖h3HeatFourierSymbol ν (t / 2) ξ‖)
            =
          (‖ξ‖ ^ n *
              ‖h3HeatFourierSymbol ν (t / 2) ξ‖) *
            (‖ξ‖ *
              ‖h3HeatFourierSymbol ν (t / 2) ξ‖) := by
          ring
        _ ≤
          h3HeatNatMomentCoefficient n ν (t / 2) *
            (Real.sqrt (ν * ((t / 2) / 3)))⁻¹ := by
          exact
            mul_le_mul
              hNatPow
              hOne
              hOneLhs0
              hNatCoeff0

/-- Explicit coefficient for the intermediate `n + 3/4` free-heat moment. -/
noncomputable def h3HeatNatAddThreeQuarterMomentCoefficient
    (n : ℕ)
    (ν t : ℝ) : ℝ :=
  h3HeatNatMomentCoefficient n ν (t / 2) *
    h3HeatThreeQuarterMomentCoefficient ν (t / 2)

/-- The intermediate free-heat coefficient is nonnegative. -/
theorem h3HeatNatAddThreeQuarterMomentCoefficient_nonneg
    (n : ℕ)
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t) :
    0 ≤ h3HeatNatAddThreeQuarterMomentCoefficient n ν t := by
  unfold h3HeatNatAddThreeQuarterMomentCoefficient
  exact
    mul_nonneg
      (h3HeatNatMomentCoefficient_nonneg n ν (t / 2))
      (h3HeatThreeQuarterMomentCoefficient_nonneg
        hν (by positivity))

/-- Positive heat time also absorbs the fractional intermediate moment
`n + 3/4`, using one half for the natural `n` powers and one half for the
residual `3/4` power. -/
theorem h3HeatFourierMomentMultiplier_le_nat_add_threeQuarter
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (n : ℕ)
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight
        ((n : ℝ) + (3 : ℝ) / 4) ξ *
        ‖h3HeatFourierSymbol ν t ξ‖
      ≤
    h3HeatNatAddThreeQuarterMomentCoefficient n ν t := by
  have hhalf : 0 < t / 2 := by
    positivity

  have hNat :=
    h3HeatFourierMomentMultiplier_le_nat
      hν hhalf n ξ

  have hNatPow :
      ‖ξ‖ ^ n *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖
        ≤
      h3HeatNatMomentCoefficient n ν (t / 2) := by
    simpa only [h3FourierMomentWeight_natCast] using hNat

  have hThreeQuarter :=
    norm_h3HeatFourierSymbol_threeQuarter_le
      hν hhalf ξ

  have hThreeQuarterPow :
      ‖ξ‖ ^ ((3 : ℝ) / 4) *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖
        ≤
      h3HeatThreeQuarterMomentCoefficient ν (t / 2) := by
    simpa only [h3FourierThreeQuarterWeight] using hThreeQuarter

  have hSplit :
      ‖h3HeatFourierSymbol ν t ξ‖
        =
      ‖h3HeatFourierSymbol ν (t / 2) ξ‖ *
        ‖h3HeatFourierSymbol ν (t / 2) ξ‖ := by
    have htSplit :
        (t / 2) + (t / 2) = t := by
      ring
    calc
      ‖h3HeatFourierSymbol ν t ξ‖
          =
        ‖h3HeatFourierSymbol ν ((t / 2) + (t / 2)) ξ‖ := by
          rw [htSplit]
      _ =
        ‖h3HeatFourierSymbol ν (t / 2) ξ *
          h3HeatFourierSymbol ν (t / 2) ξ‖ := by
          rw [h3HeatFourierSymbol_add]
      _ =
        ‖h3HeatFourierSymbol ν (t / 2) ξ‖ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖ := by
          rw [norm_mul]

  have hFactor :
      h3FourierMomentWeight
          ((n : ℝ) + (3 : ℝ) / 4) ξ
        =
      h3FourierMomentWeight (n : ℝ) ξ *
        h3FourierMomentWeight ((3 : ℝ) / 4) ξ :=
    h3FourierMomentWeight_add
      (by positivity)
      (by norm_num)
      ξ

  have hNatCoeff0 :
      0 ≤ h3HeatNatMomentCoefficient n ν (t / 2) :=
    h3HeatNatMomentCoefficient_nonneg n ν (t / 2)

  have hThreeQuarterLhs0 :
      0 ≤
        h3FourierMomentWeight ((3 : ℝ) / 4) ξ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖ :=
    mul_nonneg
      (h3FourierMomentWeight_nonneg ((3 : ℝ) / 4) ξ)
      (norm_nonneg _)

  unfold h3HeatNatAddThreeQuarterMomentCoefficient

  rw [
    hFactor,
    h3FourierMomentWeight_natCast,
    hSplit
  ]

  unfold h3FourierMomentWeight

  have hThreeQuarterPowLhs0 :
      0 ≤
        ‖ξ‖ ^ ((3 : ℝ) / 4) *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖ := by
    exact
      mul_nonneg
        (Real.rpow_nonneg (norm_nonneg ξ) _)
        (norm_nonneg _)

  calc
    (‖ξ‖ ^ n * ‖ξ‖ ^ ((3 : ℝ) / 4)) *
        (‖h3HeatFourierSymbol ν (t / 2) ξ‖ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖)
        =
      (‖ξ‖ ^ n *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖) *
        (‖ξ‖ ^ ((3 : ℝ) / 4) *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖) := by
      ring
    _ ≤
      h3HeatNatMomentCoefficient n ν (t / 2) *
        h3HeatThreeQuarterMomentCoefficient ν (t / 2) := by
      exact
        mul_le_mul
          hNatPow
          hThreeQuarterPow
          hThreeQuarterPowLhs0
          hNatCoeff0

/-!
## Generic multiplier-to-free-heat transfer
-/

/-- Any nonnegative pointwise heat multiplier bound at exponent `p` gives an
integrable `p` moment of the explicit scalar free-heat representative. -/
theorem h3SpectralScalarHeatRawRepresentative_moment_integrable_of_multiplier
    {p ν t C : ℝ}
    (hp : 0 ≤ p)
    (hC : 0 ≤ C)
    (hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
            ‖h3HeatFourierSymbol ν t ξ‖
          ≤
        C)
    (G : H3SpectralScalarState) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRaw.norm.const_mul C

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ *
            ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight hp).aestronglyMeasurable.mul
      (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
        ν t G).norm

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hw :
      0 ≤ h3FourierMomentWeight p ξ :=
    h3FourierMomentWeight_nonneg p ξ

  have hTarget0 :
      0 ≤
        h3FourierMomentWeight p ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  have hMajor0 :
      0 ≤ C * ‖h3SpectralScalarRawFourier G ξ‖ :=
    mul_nonneg hC (norm_nonneg _)

  have hPoint :
      h3FourierMomentWeight p ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖
        ≤
      C * ‖h3SpectralScalarRawFourier G ξ‖ := by
    unfold h3SpectralScalarHeatRawRepresentative
    rw [norm_mul]

    calc
      h3FourierMomentWeight p ξ *
          (‖h3HeatFourierSymbol ν t ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)
          =
        (h3FourierMomentWeight p ξ *
          ‖h3HeatFourierSymbol ν t ξ‖) *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
        ring
      _ ≤
        C * ‖h3SpectralScalarRawFourier G ξ‖ :=
        mul_le_mul_of_nonneg_right
          (hHeat ξ)
          (norm_nonneg _)

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTarget0,
    abs_of_nonneg hMajor0
  ] using hPoint

/-- Quantitative scalar free-heat moment bound from a pointwise multiplier
bound. -/
theorem h3SpectralScalarHeatRawRepresentative_moment_integral_le_rawL1_of_multiplier
    {p ν t C : ℝ}
    (hp : 0 ≤ p)
    (hC : 0 ≤ C)
    (hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
            ‖h3HeatFourierSymbol ν t ξ‖
          ≤
        C)
    (G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
      ≤
    C * h3SpectralScalarRawFourierL1Mass G := by
  have hTarget :=
    h3SpectralScalarHeatRawRepresentative_moment_integrable_of_multiplier
      hp hC hHeat G

  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRaw.norm.const_mul C

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
            ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖
          ≤
        C * ‖h3SpectralScalarRawFourier G ξ‖ := by
    intro ξ
    unfold h3SpectralScalarHeatRawRepresentative
    rw [norm_mul]

    calc
      h3FourierMomentWeight p ξ *
          (‖h3HeatFourierSymbol ν t ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)
          =
        (h3FourierMomentWeight p ξ *
          ‖h3HeatFourierSymbol ν t ξ‖) *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
        ring
      _ ≤
        C * ‖h3SpectralScalarRawFourier G ξ‖ :=
        mul_le_mul_of_nonneg_right
          (hHeat ξ)
          (norm_nonneg _)

  have hIntegral :=
    integral_mono hTarget hMajor hPoint

  unfold h3SpectralScalarRawFourierL1Mass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        C * ‖h3SpectralScalarRawFourier G ξ‖ :=
      hIntegral
    _ =
      C *
        ∫ ξ : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier G ξ‖ := by
      rw [integral_const_mul]

/-- Generic pointwise multiplier bound transferred to the named selected
initial free-heat raw Fourier `L²` package. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_moment_integrable_of_multiplier
    {p ν t C : ℝ}
    (hp : 0 ≤ p)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (i : Fin 3)
    (hC : 0 ≤ C)
    (hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
            ‖h3HeatFourierSymbol ν t ξ‖
          ≤
        C) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hBase :=
    h3SpectralScalarHeatRawRepresentative_moment_integrable_of_multiplier
      hp hC hHeat (U₀ i)

  have hRep :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht i

  have hWeighted :
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  exact hBase.congr hWeighted.symm

/-- Quantitative generic free-heat bound on the named selected initial heat
coordinate, directly in terms of the restart-radius parameter `A`. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_moment_integral_le_of_multiplier
    {p ν A t C : ℝ}
    (hp : 0 ≤ p)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hC : 0 ≤ C)
    (hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
            ‖h3HeatFourierSymbol ν t ξ‖
          ≤
        C) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    C * h3RawFourierL1DeweightingCoefficient * A := by
  have hRep :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
                hν U₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖ := by
    apply integral_congr_ae
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hBase :=
    h3SpectralScalarHeatRawRepresentative_moment_integral_le_rawL1_of_multiplier
      hp hC hHeat (U₀ i)

  have hRaw :=
    h3SpectralScalarRawFourierL1Mass_le_norm (U₀ i)

  have hCoord :
      ‖U₀ i‖ ≤ A :=
    le_trans
      (h3SpectralVelocity_coordinate_norm_le U₀ i)
      hU₀

  have hDeweight0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient :=
    h3RawFourierL1DeweightingCoefficient_nonneg

  rw [hIntegralEq]

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖)
        ≤
      C * h3SpectralScalarRawFourierL1Mass (U₀ i) :=
      hBase
    _ ≤
      C *
        (h3RawFourierL1DeweightingCoefficient * ‖U₀ i‖) :=
      mul_le_mul_of_nonneg_left hRaw hC
    _ ≤
      C *
        (h3RawFourierL1DeweightingCoefficient * A) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hCoord hDeweight0)
          hC
    _ =
      C * h3RawFourierL1DeweightingCoefficient * A := by
      ring

/-!
## All natural moments of the named free heat
-/

/-- Every natural moment of the named selected initial free heat is
integrable. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_natMoment_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (n : ℕ)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight (n : ℝ) ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  exact
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_moment_integrable_of_multiplier
      (by positivity)
      hν U₀ ht i
      (h3HeatNatMomentCoefficient_nonneg n ν t)
      (h3HeatFourierMomentMultiplier_le_nat hν ht n)

/-- Quantitative natural free-heat moment bound. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_natMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (n : ℕ)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (n : ℝ) ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3HeatNatMomentCoefficient n ν t *
      h3RawFourierL1DeweightingCoefficient *
      A := by
  exact
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_moment_integral_le_of_multiplier
      (by positivity)
      hν U₀ hA hU₀ ht i
      (h3HeatNatMomentCoefficient_nonneg n ν t)
      (h3HeatFourierMomentMultiplier_le_nat hν ht n)

/-!
## Intermediate natural-plus-three-quarter free heat
-/

/-- The intermediate `n + 3/4` free-heat moment is integrable for every
natural `n`. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_natAddThreeQuarterMoment_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (n : ℕ)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight
            ((n : ℝ) + (3 : ℝ) / 4) ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  exact
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_moment_integrable_of_multiplier
      (by positivity)
      hν U₀ ht i
      (h3HeatNatAddThreeQuarterMomentCoefficient_nonneg
        n hν.le ht.le)
      (h3HeatFourierMomentMultiplier_le_nat_add_threeQuarter
        hν ht n)

/-- Quantitative `n + 3/4` free-heat moment bound. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_natAddThreeQuarterMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (n : ℕ)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight
            ((n : ℝ) + (3 : ℝ) / 4) ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3HeatNatAddThreeQuarterMomentCoefficient n ν t *
      h3RawFourierL1DeweightingCoefficient *
      A := by
  exact
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_moment_integral_le_of_multiplier
      (by positivity)
      hν U₀ hA hU₀ ht i
      (h3HeatNatAddThreeQuarterMomentCoefficient_nonneg
        n hν.le ht.le)
      (h3HeatFourierMomentMultiplier_le_nat_add_threeQuarter
        hν ht n)

end
end Euclidean
end Bridge
end PrimeTensor

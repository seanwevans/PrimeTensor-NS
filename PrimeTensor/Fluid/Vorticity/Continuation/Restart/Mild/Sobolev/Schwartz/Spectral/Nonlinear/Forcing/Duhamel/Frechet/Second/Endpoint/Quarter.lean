import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Local
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Quarter-Hölder endpoint cancellation for the second Duhamel derivative

The localized endpoint layer was initially stated with a `1/2`-Hölder
modulus.  That exponent is sufficient but stronger than necessary.

For the second spatial derivative the raw heat singularity is

    (t - s)^(-1).

Any positive endpoint Hölder exponent therefore makes the cancelled kernel
integrable.  We choose the concrete exponent `1/4`:

    ‖N(s) - N(t)‖_{L¹_ξ} ≤ K (t - s)^(1/4).

The resulting scalar singularity is

    (t - s)^(-3/4),

which is interval-integrable because `-3/4 > -1`.

This is the right exponent for the next positive-time semigroup bootstrap:
it asks only for a fractional gain and does not silently assume a full extra
spatial derivative of the H³ state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingSecondEndpointQuarter
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Local terminal `1/4`-Hölder modulus of a spectral H³ path. -/
def H3SpectralEndpointQuarterHolderOn
    (W : ℝ → H3SpectralFinVectorState)
    (a t L : ℝ) : Prop :=
  ∀ s ∈ Set.Ioo a t,
    ‖W s - W t‖
      ≤ L * (t - s) ^ ((1 : ℝ) / 4)

/-- Local terminal `L¹` `1/4`-Hölder modulus of the raw nonlinear forcing. -/
def H3NonlinearForcingEndpointQuarterHolderL1On
    (U V : ℝ → H3SpectralFinVectorState)
    (a t K : ℝ)
    (i : Fin 3) : Prop :=
  ∀ s ∈ Set.Ioo a t,
    h3RawFinLerayOuterProductDivergenceEndpointDifferenceL1Mass
        U V t s i
      ≤ K * (t - s) ^ ((1 : ℝ) / 4)

/-- Scalar majorant after a second heat moment is paired with a
quarter-Hölder endpoint difference. -/
noncomputable def h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
    (ν t K s : ℝ) : ℝ :=
  (3 * ν⁻¹ * K) *
    (t - s) ^ (-(3 : ℝ) / 4)

/-- The quarter-Hölder cancellation kernel is interval-integrable on every
finite terminal interval. -/
theorem h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant_intervalIntegrable
    {ν a t K : ℝ} :
    IntervalIntegrable
      (h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
        ν t K)
      volume
      a
      t := by
  have hPow :
      IntervalIntegrable
        (fun q : ℝ => q ^ (-(3 : ℝ) / 4))
        volume
        0
        (t - a) := by
    exact
      intervalIntegral.intervalIntegrable_rpow'
        (by norm_num)

  have hShift :
      IntervalIntegrable
        (fun s : ℝ =>
          (t - s) ^ (-(3 : ℝ) / 4))
        volume
        a
        t := by
    have hComp := hPow.comp_sub_left t
    simpa only [sub_zero, sub_sub_cancel] using hComp.symm

  unfold
    h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
  exact hShift.const_mul (3 * ν⁻¹ * K)

/-- For positive lag, the square of the second-moment heat coefficient has
the exact elementary form `3 / (ν (t-s))`. -/
theorem h3NonlinearForcingHeatSecondMomentCoefficient_sq_eq
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t) :
    ((Real.sqrt (ν * ((t - s) / 3)))⁻¹) ^ 2
      =
    3 * ν⁻¹ * (t - s)⁻¹ := by
  have hτ : 0 < t - s := sub_pos.mpr hs
  have hbase : 0 < ν * ((t - s) / 3) := by
    positivity
  have hν0 : ν ≠ 0 := ne_of_gt hν
  have hτ0 : t - s ≠ 0 := ne_of_gt hτ

  rw [inv_pow]
  rw [Real.sq_sqrt hbase.le]
  field_simp [hν0, hτ0]

/-- The inverse lag times a quarter power is exactly the `-3/4` real power. -/
theorem inv_mul_quarter_rpow_eq_neg_three_quarter_rpow
    {q : ℝ}
    (hq : 0 < q) :
    q⁻¹ * q ^ ((1 : ℝ) / 4)
      =
    q ^ (-(3 : ℝ) / 4) := by
  calc
    q⁻¹ * q ^ ((1 : ℝ) / 4)
        =
      q ^ (-(1 : ℝ)) * q ^ ((1 : ℝ) / 4) := by
        rw [Real.rpow_neg_one]
    _ =
      q ^ (-(1 : ℝ) + (1 : ℝ) / 4) := by
        rw [Real.rpow_add hq]
    _ =
      q ^ (-(3 : ℝ) / 4) := by
        congr 1
        ring

/-- Localized second-Fourier-moment estimate under only a quarter-Hölder
endpoint modulus of the nonlinear forcing. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_le_quarter
    {ν a t K s : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo a t)
    (hHolder :
      H3NonlinearForcingEndpointQuarterHolderL1On
        U V a t K i) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
              h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ)‖)
      ≤
    h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
      ν t K s := by
  have hτ : 0 < t - s := sub_pos.mpr hs.2

  let C : ℝ :=
    (Real.sqrt (ν * ((t - s) / 3)))⁻¹

  let D : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
        h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ

  have hDs :
      Integrable
        (h3RawFinLerayOuterProductDivergence (U s) (V s) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable (U s) (V s) i

  have hDt :
      Integrable
        (h3RawFinLerayOuterProductDivergence (U t) (V t) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable (U t) (V t) i

  have hD :
      Integrable D (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hDs.sub hDt

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C ^ 2 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hD.norm.const_mul (C ^ 2)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 2).aestronglyMeasurable).mul
        ((continuous_h3HeatFourierSymbol ν (t - s)).aestronglyMeasurable.mul
          hD.aestronglyMeasurable).norm

  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajorantInt.mono' hTargetMeas ?_
    filter_upwards with ξ
    have hMoment :=
      h3HeatFourierMomentMultiplier_le_three
        hν hτ 2 (by norm_num) ξ
    have hNonneg :
        0 ≤
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖ := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    rw [norm_mul]
    calc
      ‖ξ‖ ^ 2 *
          (‖h3HeatFourierSymbol ν (t - s) ξ‖ * ‖D ξ‖)
          =
        (‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ‖) * ‖D ξ‖ := by
            ring
      _ ≤ C ^ 2 * ‖D ξ‖ := by
        dsimp only [C]
        exact
          mul_le_mul_of_nonneg_right
            hMoment
            (norm_nonneg _)

  have hIntegralBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
        ≤
      C ^ 2 *
        (∫ ξ : H3FourierPoint3, ‖D ξ‖) := by
    calc
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
          ≤
        ∫ ξ : H3FourierPoint3,
          C ^ 2 * ‖D ξ‖ := by
        refine integral_mono_ae hTargetInt hMajorantInt ?_
        filter_upwards with ξ
        have hMoment :=
          h3HeatFourierMomentMultiplier_le_three
            hν hτ 2 (by norm_num) ξ
        rw [norm_mul]
        calc
          ‖ξ‖ ^ 2 *
              (‖h3HeatFourierSymbol ν (t - s) ξ‖ * ‖D ξ‖)
              =
            (‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ‖) * ‖D ξ‖ := by
                ring
          _ ≤ C ^ 2 * ‖D ξ‖ := by
            dsimp only [C]
            exact
              mul_le_mul_of_nonneg_right
                hMoment
                (norm_nonneg _)
      _ =
        C ^ 2 *
          (∫ ξ : H3FourierPoint3, ‖D ξ‖) := by
        rw [integral_const_mul]

  have hHolderAt :
      (∫ ξ : H3FourierPoint3, ‖D ξ‖)
        ≤
      K * (t - s) ^ ((1 : ℝ) / 4) := by
    simpa only [
      D,
      h3RawFinLerayOuterProductDivergenceEndpointDifferenceL1Mass
    ] using hHolder s hs

  have hCsq :
      C ^ 2 =
        3 * ν⁻¹ * (t - s)⁻¹ := by
    dsimp only [C]
    exact
      h3NonlinearForcingHeatSecondMomentCoefficient_sq_eq
        hν hs.2

  have hLag :
      (t - s)⁻¹ *
          (t - s) ^ ((1 : ℝ) / 4)
        =
      (t - s) ^ (-(3 : ℝ) / 4) :=
    inv_mul_quarter_rpow_eq_neg_three_quarter_rpow hτ

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
              h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ)‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖ := by
      rfl
    _ ≤
      C ^ 2 *
        (∫ ξ : H3FourierPoint3, ‖D ξ‖) :=
      hIntegralBound
    _ ≤
      C ^ 2 *
        (K * (t - s) ^ ((1 : ℝ) / 4)) := by
      exact
        mul_le_mul_of_nonneg_left
          hHolderAt
          (sq_nonneg C)
    _ =
      (3 * ν⁻¹ * K) *
        (t - s) ^ (-(3 : ℝ) / 4) := by
      rw [hCsq]
      calc
        (3 * ν⁻¹ * (t - s)⁻¹) *
            (K * (t - s) ^ ((1 : ℝ) / 4))
            =
          (3 * ν⁻¹ * K) *
            ((t - s)⁻¹ *
              (t - s) ^ ((1 : ℝ) / 4)) := by
          ring
        _ =
          (3 * ν⁻¹ * K) *
            (t - s) ^ (-(3 : ℝ) / 4) := by
          rw [hLag]
    _ =
      h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
        ν t K s := by
      rfl

/-- A bounded locally quarter-Hölder path transfers its modulus to the
diagonal nonlinear forcing. -/
theorem h3NonlinearForcingEndpointQuarterHolderL1On_of_path
    {W : ℝ → H3SpectralFinVectorState}
    {a t M L : ℝ}
    (hM : 0 ≤ M)
    (hL : 0 ≤ L)
    (hWs : ∀ s ∈ Set.Ioo a t, ‖W s‖ ≤ M)
    (hWt : ‖W t‖ ≤ M)
    (hHolder : H3SpectralEndpointQuarterHolderOn W a t L)
    (i : Fin 3) :
    H3NonlinearForcingEndpointQuarterHolderL1On
      W W a t
      (2 * h3NonlinearForcingL1Coefficient * M * L)
      i := by
  intro s hs

  have hDiff :
      ‖W s - W t‖
        ≤
      L * (t - s) ^ ((1 : ℝ) / 4) :=
    hHolder s hs

  have hC : 0 ≤ h3NonlinearForcingL1Coefficient :=
    h3NonlinearForcingL1Coefficient_nonneg

  have hPow :
      0 ≤ (t - s) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _

  have hLPow :
      0 ≤ L * (t - s) ^ ((1 : ℝ) / 4) :=
    mul_nonneg hL hPow

  unfold
    h3RawFinLerayOuterProductDivergenceEndpointDifferenceL1Mass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
          h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        ≤
      h3NonlinearForcingL1Coefficient * ‖W s - W t‖ * ‖W s‖ +
        h3NonlinearForcingL1Coefficient * ‖W t‖ * ‖W s - W t‖ :=
      h3RawFinLerayOuterProductDivergence_diagonal_differenceL1Mass_le
        (W s) (W t) i
    _ ≤
      h3NonlinearForcingL1Coefficient *
            (L * (t - s) ^ ((1 : ℝ) / 4)) * M +
        h3NonlinearForcingL1Coefficient * M *
            (L * (t - s) ^ ((1 : ℝ) / 4)) := by
      apply add_le_add
      · calc
          h3NonlinearForcingL1Coefficient * ‖W s - W t‖ * ‖W s‖
              ≤
            h3NonlinearForcingL1Coefficient *
                (L * (t - s) ^ ((1 : ℝ) / 4)) * ‖W s‖ := by
              exact
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hDiff hC)
                  (norm_nonneg _)
          _ ≤
            h3NonlinearForcingL1Coefficient *
                (L * (t - s) ^ ((1 : ℝ) / 4)) * M := by
              exact
                mul_le_mul_of_nonneg_left
                  (hWs s hs)
                  (mul_nonneg hC hLPow)
      · calc
          h3NonlinearForcingL1Coefficient * ‖W t‖ * ‖W s - W t‖
              ≤
            h3NonlinearForcingL1Coefficient * M * ‖W s - W t‖ := by
              exact
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hWt hC)
                  (norm_nonneg _)
          _ ≤
            h3NonlinearForcingL1Coefficient * M *
                (L * (t - s) ^ ((1 : ℝ) / 4)) := by
              exact
                mul_le_mul_of_nonneg_left
                  hDiff
                  (mul_nonneg hC hM)
    _ =
      (2 * h3NonlinearForcingL1Coefficient * M * L) *
        (t - s) ^ ((1 : ℝ) / 4) := by
      ring

/-- Selected-restart specialization of the quarter-Hölder nonlinear transfer
theorem. -/
theorem h3NonlinearForcingEndpointQuarterHolderL1On_selectedRestart_of_path
    {ν A a t L : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (_ha : 0 ≤ a)
    (_hat : a ≤ t)
    (_htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hL : 0 ≤ L)
    (hHolder :
      let W : ℝ → H3SpectralFinVectorState :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀
      H3SpectralEndpointQuarterHolderOn W a t L)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    H3NonlinearForcingEndpointQuarterHolderL1On
      W W a t
      (4 * h3NonlinearForcingL1Coefficient * A * L)
      i := by
  dsimp only at hHolder ⊢

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hWs :
      ∀ s ∈ Set.Ioo a t,
        ‖W s‖ ≤ 2 * A := by
    intro s _hs
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have hWt :
      ‖W t‖ ≤ 2 * A := by
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ t

  have h :=
    h3NonlinearForcingEndpointQuarterHolderL1On_of_path
      h2A hL hWs hWt hHolder i

  have hCoeff :
      2 * h3NonlinearForcingL1Coefficient * (2 * A) * L
        =
      4 * h3NonlinearForcingL1Coefficient * A * L := by
    ring

  change
    H3NonlinearForcingEndpointQuarterHolderL1On
      W W a t
      (4 * h3NonlinearForcingL1Coefficient * A * L)
      i
  rw [← hCoeff]
  exact h

end

end Euclidean
end Bridge
end PrimeTensor

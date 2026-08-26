import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Forcing.HalfHolder
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Head.Real.C3.Bridge

/-!
# Local endpoint Hölder control for the second Duhamel derivative

A global `1/2`-Hölder estimate all the way back to the restart time is stronger
than H³ data alone should provide.  It is also unnecessary.

At a fixed positive target time `t`, the Duhamel integral naturally splits into

    [0,a] ∪ [a,t],   0 ≤ a < t.

The old head `[0,a]` has a fixed positive heat lag and is already handled by
the positive-time `C³` reconstruction machinery.  Endpoint cancellation is
needed only on the terminal tail `[a,t]`.

This file therefore localizes the previous endpoint predicates and estimates
to `s ∈ (a,t)`.

The key consequences are:

* only a terminal `1/2`-Hölder modulus of the path is required;
* the nonlinear forcing inherits the localized endpoint modulus with the same
  bilinear constant;
* the cancelled second Fourier moment has the same integrable
  `(t-s)^(-1/2)` majorant on the terminal interval; and
* the majorant is interval-integrable on `a..t` by restriction of the already
  proved `0..t` estimate.

This is the correct interface for positive-time parabolic bootstrap of the
selected mild solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingSecondEndpointLocal
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Local terminal `1/2`-Hölder modulus of a spectral H³ path on `(a,t)`. -/
def H3SpectralEndpointHalfHolderOn
    (W : ℝ → H3SpectralFinVectorState)
    (a t L : ℝ) : Prop :=
  ∀ s ∈ Set.Ioo a t,
    ‖W s - W t‖ ≤ L * Real.sqrt (t - s)

/-- Local terminal `L¹` endpoint modulus of the raw nonlinear forcing. -/
def H3NonlinearForcingEndpointHalfHolderL1On
    (U V : ℝ → H3SpectralFinVectorState)
    (a t K : ℝ)
    (i : Fin 3) : Prop :=
  ∀ s ∈ Set.Ioo a t,
    h3RawFinLerayOuterProductDivergenceEndpointDifferenceL1Mass
        U V t s i
      ≤ K * Real.sqrt (t - s)

/-- The cancellation majorant remains interval-integrable on every terminal
subinterval `a..t`. -/
theorem h3NonlinearForcingHeatSecondDerivativeCancellationMajorant_intervalIntegrable_on
    {ν a t K : ℝ}
    (hν : 0 < ν)
    (ha : 0 ≤ a)
    (hat : a ≤ t) :
    IntervalIntegrable
      (h3NonlinearForcingHeatSecondDerivativeCancellationMajorant ν t K)
      volume
      a
      t := by
  have ht : 0 ≤ t := le_trans ha hat
  have hFull :=
    h3NonlinearForcingHeatSecondDerivativeCancellationMajorant_intervalIntegrable
      (K := K) hν ht
  have haMem : a ∈ Set.uIcc (0 : ℝ) t := by
    rw [Set.uIcc_of_le ht]
    exact ⟨ha, hat⟩
  exact ((IntervalIntegrable.trans_iff haMem).1 hFull).2

/-- Localized fixed-lag second-moment estimate.  Only the endpoint modulus at
the particular source time `s` is used. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_le_on
    {ν a t K s : ℝ}
    (hν : 0 < ν)
    (ha : 0 ≤ a)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo a t)
    (hHolder : H3NonlinearForcingEndpointHalfHolderL1On U V a t K i) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
              h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ)‖)
      ≤
    h3NonlinearForcingHeatSecondDerivativeCancellationMajorant
      ν t K s := by
  have hs0 : s ∈ Set.Ioo (0 : ℝ) t := by
    exact ⟨lt_of_le_of_lt ha hs.1, hs.2⟩

  have hτ : 0 < t - s := sub_pos.mpr hs.2

  let C : ℝ := (Real.sqrt (ν * ((t - s) / 3)))⁻¹
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

  have hD : Integrable D (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hDs.sub hDt

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 => C ^ 2 * ‖D ξ‖)
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
        ∫ ξ : H3FourierPoint3, C ^ 2 * ‖D ξ‖ := by
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
        ≤ K * Real.sqrt (t - s) := by
    simpa only [
      D,
      h3RawFinLerayOuterProductDivergenceEndpointDifferenceL1Mass
    ] using hHolder s hs

  have hCoeff :
      C * Real.sqrt (t - s)
        =
      (Real.sqrt (ν / 3))⁻¹ := by
    dsimp only [C]
    simpa only [
      h3NonlinearForcingHeatFirstMomentRetardedCoefficient,
      h3NonlinearForcingHeatFirstMomentCoefficient
    ] using
      (h3NonlinearForcingHeatFirstMomentRetardedCoefficient_mul_sqrt_eq
        hν hs0)

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
      C ^ 2 * (∫ ξ : H3FourierPoint3, ‖D ξ‖) :=
        hIntegralBound
    _ ≤
      C ^ 2 * (K * Real.sqrt (t - s)) := by
        exact
          mul_le_mul_of_nonneg_left
            hHolderAt
            (sq_nonneg C)
    _ =
      (Real.sqrt (ν / 3))⁻¹ *
        (C * K) := by
      calc
        C ^ 2 * (K * Real.sqrt (t - s))
            =
          (C * Real.sqrt (t - s)) * (C * K) := by
              ring
        _ =
          (Real.sqrt (ν / 3))⁻¹ * (C * K) := by
              rw [hCoeff]
    _ =
      h3NonlinearForcingHeatSecondDerivativeCancellationMajorant
        ν t K s := by
      unfold h3NonlinearForcingHeatSecondDerivativeCancellationMajorant
      unfold h3NonlinearForcingHeatFirstMomentTimeMajorant
      unfold h3NonlinearForcingHeatFirstMomentRetardedCoefficient
      unfold h3NonlinearForcingHeatFirstMomentCoefficient
      dsimp only [C]

/-- A bounded locally half-Hölder path transfers its terminal modulus to the
diagonal nonlinear forcing. -/
theorem h3NonlinearForcingEndpointHalfHolderL1On_of_path
    {W : ℝ → H3SpectralFinVectorState}
    {a t M L : ℝ}
    (hM : 0 ≤ M)
    (hL : 0 ≤ L)
    (hWs : ∀ s ∈ Set.Ioo a t, ‖W s‖ ≤ M)
    (hWt : ‖W t‖ ≤ M)
    (hHolder : H3SpectralEndpointHalfHolderOn W a t L)
    (i : Fin 3) :
    H3NonlinearForcingEndpointHalfHolderL1On
      W W a t
      (2 * h3NonlinearForcingL1Coefficient * M * L)
      i := by
  intro s hs

  have hDiff :
      ‖W s - W t‖ ≤ L * Real.sqrt (t - s) :=
    hHolder s hs

  have hC : 0 ≤ h3NonlinearForcingL1Coefficient :=
    h3NonlinearForcingL1Coefficient_nonneg

  have hSqrt : 0 ≤ Real.sqrt (t - s) :=
    Real.sqrt_nonneg _

  have hLs : 0 ≤ L * Real.sqrt (t - s) :=
    mul_nonneg hL hSqrt

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
            (L * Real.sqrt (t - s)) * M +
        h3NonlinearForcingL1Coefficient * M *
            (L * Real.sqrt (t - s)) := by
      apply add_le_add
      · calc
          h3NonlinearForcingL1Coefficient * ‖W s - W t‖ * ‖W s‖
              ≤
            h3NonlinearForcingL1Coefficient *
                (L * Real.sqrt (t - s)) * ‖W s‖ := by
              exact
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hDiff hC)
                  (norm_nonneg _)
          _ ≤
            h3NonlinearForcingL1Coefficient *
                (L * Real.sqrt (t - s)) * M := by
              exact
                mul_le_mul_of_nonneg_left
                  (hWs s hs)
                  (mul_nonneg hC hLs)
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
                (L * Real.sqrt (t - s)) := by
              exact
                mul_le_mul_of_nonneg_left
                  hDiff
                  (mul_nonneg hC hM)
    _ =
      (2 * h3NonlinearForcingL1Coefficient * M * L) *
        Real.sqrt (t - s) := by
      ring

/-- Selected-restart specialization of the localized transfer theorem. -/
theorem h3NonlinearForcingEndpointHalfHolderL1On_selectedRestart_of_path
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
      H3SpectralEndpointHalfHolderOn W a t L)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    H3NonlinearForcingEndpointHalfHolderL1On
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
    h3NonlinearForcingEndpointHalfHolderL1On_of_path
      h2A hL hWs hWt hHolder i

  have hCoeff :
      2 * h3NonlinearForcingL1Coefficient * (2 * A) * L
        =
      4 * h3NonlinearForcingL1Coefficient * A * L := by
    ring

  change
    H3NonlinearForcingEndpointHalfHolderL1On
      W W a t
      (4 * h3NonlinearForcingL1Coefficient * A * L)
      i
  rw [← hCoeff]
  exact h

end

end Euclidean
end Bridge
end PrimeTensor

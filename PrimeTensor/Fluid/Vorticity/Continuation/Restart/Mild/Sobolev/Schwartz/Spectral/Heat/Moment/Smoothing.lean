import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Heat.Derivative.Continuity
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Positive-time third Fourier moments for weighted H³ restart states

The classicalization frontier asks for a real spatial `C³` representative of
our selected mild restart path.  The first genuinely analytic input is that a
positive amount of heat evolution upgrades the deweighted H³ Fourier amplitude
from bare `L¹` to `L¹` with three polynomial moments.

We prove this directly from the already-established one-gradient heat bound.
Split a positive time `t` into three equal pieces.  The heat semigroup gives

    H_t = H_{t/3}^3.

One factor of `‖ξ‖` can be absorbed into each heat factor, while each remaining
heat factor has norm at most one.  Thus moments of orders zero through three
are bounded by an `L¹` multiple of the original raw Fourier amplitude.

Mathlib's `Real.contDiff_fourier` then turns these moment estimates into a
spatial `C³` Fourier reconstruction.  This is deliberately a scalar theorem;
the finite velocity lift is componentwise.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatMomentSmoothing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
The ordinary Fourier amplitude obtained by deweighting a spectral H³ state and
then applying positive-time heat evolution.
-/
def h3SpectralScalarHeatRawRepresentative
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℂ :=
  h3HeatFourierSymbol ν t ξ *
    h3SpectralScalarRawFourier G ξ

/-- The positive-time raw heat representative is strongly measurable. -/
theorem h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
    (ν t : ℝ)
    (G : H3SpectralScalarState) :
    AEStronglyMeasurable
      (h3SpectralScalarHeatRawRepresentative ν t G)
      (volume : Measure H3FourierPoint3) := by
  unfold h3SpectralScalarHeatRawRepresentative
  exact
    (continuous_h3HeatFourierSymbol ν t).aestronglyMeasurable.mul
      (h3SpectralScalarRawFourier_memLp1 G).1

/--
The geometric Fourier norm is bounded by the radial derivative multiplier
`2π ‖ξ‖`.
-/
theorem h3Fourier_norm_le_gradientMagnitude
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ≤ h3FourierGradientMagnitude ξ := by
  unfold h3FourierGradientMagnitude
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hnorm : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  nlinarith

/-- Norm form of the one-gradient heat multiplier. -/
theorem norm_h3HeatGradientMagnitudeSymbol_eq_mul
    (ν t : ℝ)
    (ξ : H3FourierPoint3) :
    ‖h3HeatGradientMagnitudeSymbol ν t ξ‖
      =
    h3FourierGradientMagnitude ξ *
      ‖h3HeatFourierSymbol ν t ξ‖ := by
  unfold h3HeatGradientMagnitudeSymbol
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (h3FourierGradientMagnitude_nonneg ξ)]

/--
At positive time, moments through order three of the scalar heat multiplier
are uniformly bounded.  The explicit constant is obtained by splitting `t`
into three equal heat steps.
-/
theorem h3HeatFourierMomentMultiplier_le_three
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (n : ℕ)
    (hn : n ≤ 3)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ n * ‖h3HeatFourierSymbol ν t ξ‖
      ≤
    ((Real.sqrt (ν * (t / 3)))⁻¹) ^ n := by
  let s : ℝ := t / 3
  let C : ℝ := (Real.sqrt (ν * s))⁻¹
  let a : ℝ := ‖h3HeatFourierSymbol ν s ξ‖
  let r : ℝ := ‖ξ‖

  change
    r ^ n * ‖h3HeatFourierSymbol ν t ξ‖ ≤ C ^ n

  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact norm_nonneg _
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact norm_h3HeatFourierSymbol_le_one hν.le hs.le ξ
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact norm_nonneg _

  have hHeatCube :
      ‖h3HeatFourierSymbol ν t ξ‖ = a ^ 3 := by
    have htSplit : t = (s + s) + s := by
      dsimp [s]
      ring
    dsimp [a]
    rw [htSplit, h3HeatFourierSymbol_add, norm_mul]
    rw [h3HeatFourierSymbol_add, norm_mul]
    ring

  have hra : r * a ≤ C := by
    have hnormGrad :
        r ≤ h3FourierGradientMagnitude ξ := by
      dsimp [r]
      exact h3Fourier_norm_le_gradientMagnitude ξ
    calc
      r * a
          ≤ h3FourierGradientMagnitude ξ * a :=
        mul_le_mul_of_nonneg_right hnormGrad ha0
      _ = ‖h3HeatGradientMagnitudeSymbol ν s ξ‖ := by
        dsimp [a]
        symm
        exact norm_h3HeatGradientMagnitudeSymbol_eq_mul ν s ξ
      _ ≤ C := by
        dsimp [C]
        exact norm_h3HeatGradientMagnitudeSymbol_le hν hs ξ

  have ha2 : a ^ 2 ≤ 1 := by
    simpa using
      (pow_le_pow_left₀ ha0 ha1 2)

  have hnCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
    omega
  rcases hnCases with rfl | rfl | rfl | rfl
  · simp only [pow_zero, one_mul]
    rw [hHeatCube]
    have ha3 : a ^ 3 ≤ (1 : ℝ) ^ 3 :=
      pow_le_pow_left₀ ha0 ha1 3
    simpa using ha3
  · simp only [pow_one]
    rw [hHeatCube]
    calc
      r * a ^ 3 = (r * a) * a ^ 2 := by ring
      _ ≤ C * a ^ 2 :=
        mul_le_mul_of_nonneg_right hra (pow_nonneg ha0 2)
      _ ≤ C * 1 :=
        mul_le_mul_of_nonneg_left ha2 hC
      _ = C := by ring
  · rw [hHeatCube]
    have hra2 : (r * a) ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hr0 ha0) hra 2
    calc
      r ^ 2 * a ^ 3 = (r * a) ^ 2 * a := by ring
      _ ≤ C ^ 2 * a :=
        mul_le_mul_of_nonneg_right hra2 ha0
      _ ≤ C ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left ha1 (pow_nonneg hC 2)
      _ = C ^ 2 := by ring
  · rw [hHeatCube]
    have hra3 : (r * a) ^ 3 ≤ C ^ 3 :=
      pow_le_pow_left₀ (mul_nonneg hr0 ha0) hra 3
    calc
      r ^ 3 * a ^ 3 = (r * a) ^ 3 := by ring
      _ ≤ C ^ 3 := hra3

/--
Every Fourier moment through order three of the positive-time raw heat
representative is integrable.
-/
theorem h3SpectralScalarHeatRawRepresentative_moment_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (n : ℕ)
    (hn : n ≤ 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ n *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ := (Real.sqrt (ν * (t / 3)))⁻¹

  have hRawInt :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C ^ n * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRawInt.norm.const_mul (C ^ n)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ n *
            ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow n).aestronglyMeasurable).mul
        (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
          ν t G).norm

  refine hMajorant.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hMoment :=
    h3HeatFourierMomentMultiplier_le_three
      hν ht n hn ξ

  have hPoint :
      ‖ξ‖ ^ n *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖
        ≤
      C ^ n * ‖h3SpectralScalarRawFourier G ξ‖ := by
    unfold h3SpectralScalarHeatRawRepresentative
    rw [norm_mul]
    calc
      ‖ξ‖ ^ n *
          (‖h3HeatFourierSymbol ν t ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)
          =
        (‖ξ‖ ^ n * ‖h3HeatFourierSymbol ν t ξ‖) *
          ‖h3SpectralScalarRawFourier G ξ‖ := by ring
      _ ≤
        C ^ n * ‖h3SpectralScalarRawFourier G ξ‖ := by
        dsimp [C]
        exact
          mul_le_mul_of_nonneg_right
            hMoment
            (norm_nonneg _)

  have hTargetNonneg :
      0 ≤
        ‖ξ‖ ^ n *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖ :=
    mul_nonneg (pow_nonneg (norm_nonneg _) n) (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  exact hPoint

/--
The positive-time heat-smoothed raw spectral amplitude reconstructs a `C³`
complex spatial function by the ordinary Fourier transform.
-/
theorem h3SpectralScalarHeatRawRepresentative_fourier_contDiff_three
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    ContDiff ℝ 3
      (FourierTransform.fourier
        (h3SpectralScalarHeatRawRepresentative ν t G)) := by
  apply Real.contDiff_fourier
  intro n hn
  have hn' : n ≤ 3 := by
    simpa using hn
  exact
    h3SpectralScalarHeatRawRepresentative_moment_integrable
      hν ht G n hn'

/--
The ordinary inverse Fourier reconstruction is also `C³`, by the real Fourier
reflection identity.
-/
theorem h3SpectralScalarHeatRawRepresentative_fourierInv_contDiff_three
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    ContDiff ℝ 3
      (FourierTransformInv.fourierInv
        (h3SpectralScalarHeatRawRepresentative ν t G)) := by
  have hFourier :=
    h3SpectralScalarHeatRawRepresentative_fourier_contDiff_three
      hν ht G
  have hEq :
      FourierTransformInv.fourierInv
          (h3SpectralScalarHeatRawRepresentative ν t G)
        =
      fun x : H3FourierPoint3 =>
        FourierTransform.fourier
          (h3SpectralScalarHeatRawRepresentative ν t G) (-x) := by
    funext x
    exact
      Real.fourierInv_eq_fourier_neg
        (h3SpectralScalarHeatRawRepresentative ν t G) x
  rw [hEq]
  exact hFourier.comp (by fun_prop)

end
end Euclidean
end Bridge
end PrimeTensor

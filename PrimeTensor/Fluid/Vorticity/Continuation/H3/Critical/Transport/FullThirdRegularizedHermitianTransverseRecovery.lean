import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdHermitianSmoothCompactSpectralDensity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
# Smooth origin-regularized transverse recovery of real Schwartz velocities

The exact Leray symbol has a denominator |ξ|², which is singular at ξ = 0.
Instead of asserting Schwartz regularity of the measurable L² projection,
we replace the inverse squared radius by (2 (|ξ|² + δ))⁻¹, for δ > 0.

For a smooth complex input U, this is a globally smooth multiplier. Combining
it with the existing polynomial transverse numerator and compact real cutoff
produces an actual smooth compact Hermitian Fourier packet, and hence an
actual real, physically divergence-free Schwartz velocity.

For input U which is already Hermitian and transverse and for an even cutoff,
its Fourier transform is exactly

  χ(ξ) [ |ξ|² / (|ξ|² + δ) ] U(ξ).

The radial factor is nonnegative and at most one. There is no singularity
at zero frequency, no axiom granting a Schwartz representative to an L²
projection, and no claim of strong convergence as δ tends to zero in this
module. The next step is the genuine L² dominated-convergence theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff FourierTransform ComplexConjugate

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev CPol244 := A3 → ℂ
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeRegularizedRecovery244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The real frequency square is nonnegative, including at the origin. -/
theorem thirdFullRadialSquare_nonneg244 (ξ : Freq244) :
    0 ≤ thirdTriadAxisDot244 ξ ξ := by
  unfold thirdTriadAxisDot244
  apply Finset.sum_nonneg
  intro j _
  exact mul_self_nonneg (ξ j)

/-- The positive regularization removes the zero-frequency denominator. -/
theorem thirdFullRegularizedRadialDen_pos244
    (δ : ℝ) (hδ : 0 < δ) (ξ : Freq244) :
    0 < thirdTriadAxisDot244 ξ ξ + δ :=
  add_pos_of_nonneg_of_pos (thirdFullRadialSquare_nonneg244 ξ) hδ

/-- Smooth reciprocal of twice the shifted square radius. -/
noncomputable def thirdFullRegularizedInverseRadius244
    (δ : ℝ) (ξ : Freq244) : ℝ :=
  (2 * (thirdTriadAxisDot244 ξ ξ + δ))⁻¹

/-- The inverse-radius multiplier is smooth globally; no puncturing of ℝ³
and no value chosen by a discontinuous branch are needed. -/
theorem thirdFullRegularizedInverseRadius_contDiff244
    (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (thirdFullRegularizedInverseRadius244 δ) := by
  have hSq : ContDiff ℝ ∞
      (fun ξ : Freq244 => thirdTriadAxisDot244 ξ ξ) := by
    change ContDiff ℝ ∞ (fun ξ : Freq244 =>
      ∑ j : A3, ξ j * ξ j)
    exact ContDiff.sum (s := Finset.univ)
      (fun j _ => (contDiff_apply ℝ ℝ j).mul (contDiff_apply ℝ ℝ j))
  change ContDiff ℝ ∞ (fun ξ : Freq244 =>
    (2 * (thirdTriadAxisDot244 ξ ξ + δ))⁻¹)
  apply (contDiff_const.mul (hSq.add contDiff_const)).inv
  intro ξ
  exact ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2)
    (thirdFullRegularizedRadialDen_pos244 δ hδ ξ))

/-- Reflection preserves the regularized inverse radius. -/
theorem thirdFullRegularizedInverseRadius_even244
    (δ : ℝ) (ξ : Freq244) :
    thirdFullRegularizedInverseRadius244 δ (fun j => -ξ j) =
      thirdFullRegularizedInverseRadius244 δ ξ := by
  have hSq : thirdTriadAxisDot244 (fun j => -ξ j) (fun j => -ξ j) =
      thirdTriadAxisDot244 ξ ξ := by
    unfold thirdTriadAxisDot244
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [thirdFullRegularizedInverseRadius244, hSq]

/-- The input polarization rescaled by the smooth positive radial inverse. -/
noncomputable def thirdFullRegularizedTransverseInput244
    (δ : ℝ) (U : Freq244 → CPol244)
    (ξ : Freq244) (j : A3) : ℂ :=
  (thirdFullRegularizedInverseRadius244 δ ξ : ℂ) * U ξ j

/-- Multiplying the Fourier polarization by the regularized radial reciprocal
preserves global smoothness of any smooth complex vector profile. -/
theorem thirdFullRegularizedTransverseInput_contDiff244
    (δ : ℝ) (hδ : 0 < δ)
    (U : Freq244 → CPol244) (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (thirdFullRegularizedTransverseInput244 δ U) := by
  have hScalar : ContDiff ℝ ∞
      (fun ξ : Freq244 =>
        (thirdFullRegularizedInverseRadius244 δ ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (thirdFullRegularizedInverseRadius_contDiff244 δ hδ)
  apply contDiff_pi'
  intro j
  change ContDiff ℝ ∞ (fun ξ : Freq244 =>
    (thirdFullRegularizedInverseRadius244 δ ξ : ℂ) * U ξ j)
  exact hScalar.mul ((contDiff_apply ℝ ℂ j).comp hU)

/-- Hermitian reality is preserved by the REAL, EVEN radial regularization. -/
theorem thirdFullRegularizedTransverseInput_reality244
    (δ : ℝ) (U : Freq244 → CPol244)
    (hU : H3ComplexHermitianPolarizationProfile244 U) :
    H3ComplexHermitianPolarizationProfile244
      (thirdFullRegularizedTransverseInput244 δ U) := by
  intro ξ
  funext j
  change
    (thirdFullRegularizedInverseRadius244 δ (fun k => -ξ k) : ℂ) *
        U (fun k => -ξ k) j =
      (starRingEnd ℂ)
        ((thirdFullRegularizedInverseRadius244 δ ξ : ℂ) * U ξ j)
  rw [thirdFullRegularizedInverseRadius_even244, hU ξ, map_mul]
  have hc : (starRingEnd ℂ)
        (thirdFullRegularizedInverseRadius244 δ ξ : ℂ) =
      (thirdFullRegularizedInverseRadius244 δ ξ : ℂ) := by
    simpa only [starRingEnd_apply] using
      (Complex.conj_ofReal (thirdFullRegularizedInverseRadius244 δ ξ))
  rw [hc] <;> simp only [starRingEnd_apply]

/-- The transverse polynomial is homogeneous of degree one in a COMPLEX
polarization, for every real frequency (including the origin). -/
theorem thirdFullComplexTransverseNumerator_const_mul244
    (ξ : Freq244) (A : CPol244) (c : ℂ) :
    thirdFullComplexTransverseNumerator244 ξ (fun j => c * A j) =
      fun j => c * thirdFullComplexTransverseNumerator244 ξ A j := by
  have hDot : mixedDot ξ (fun j => c * A j) = c * mixedDot ξ A := by
    unfold mixedDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  funext j
  change
    (thirdTriadAxisDot244 ξ ξ : ℂ) * (c * A j) -
      mixedDot ξ (fun k => c * A k) * (ξ j : ℂ) =
    c * ((thirdTriadAxisDot244 ξ ξ : ℂ) * A j -
      mixedDot ξ A * (ξ j : ℂ))
  rw [hDot]
  ring

/-- The regularized complex transverse numerator is the ordinary numerator
multiplied by the true globally smooth radial reciprocal. -/
theorem thirdFullRegularizedTransverseInput_numerator244
    (δ : ℝ) (U : Freq244 → CPol244)
    (ξ : Freq244) (j : A3) :
    thirdFullComplexTransverseNumerator244 ξ
      (thirdFullRegularizedTransverseInput244 δ U ξ) j =
    (thirdFullRegularizedInverseRadius244 δ ξ : ℂ) *
      thirdFullComplexTransverseNumerator244 ξ (U ξ) j := by
  exact congrFun (thirdFullComplexTransverseNumerator_const_mul244
    ξ (U ξ) (thirdFullRegularizedInverseRadius244 δ ξ : ℂ)) j

/-- On an exactly divergence-free complex Fourier profile, the polynomial
numerator reduces to scalar radial suppression, without a hidden projection
hypothesis. -/
theorem thirdFullRegularizedTransverseInput_numerator_solenoidal244
    (δ : ℝ) (U : Freq244 → CPol244)
    (hUdiv : ∀ ξ, mixedDot ξ (U ξ) = 0)
    (ξ : Freq244) (j : A3) :
    thirdFullComplexTransverseNumerator244 ξ
      (thirdFullRegularizedTransverseInput244 δ U ξ) j =
    (thirdFullRegularizedInverseRadius244 δ ξ : ℂ) *
      (thirdTriadAxisDot244 ξ ξ : ℂ) * U ξ j := by
  rw [thirdFullRegularizedTransverseInput_numerator244]
  rw [congrFun (thirdFullComplexTransverseNumerator_at_transverse244
    ξ (U ξ) (hUdiv ξ)) j]
  ring

/-- The regularized radial recovery multiplier is nonnegative everywhere. -/
theorem thirdFullRegularizedRadialFactor_nonneg244
    (δ : ℝ) (hδ : 0 < δ) (ξ : Freq244) :
    0 ≤ thirdTriadAxisDot244 ξ ξ /
      (thirdTriadAxisDot244 ξ ξ + δ) :=
  div_nonneg (thirdFullRadialSquare_nonneg244 ξ)
    (le_of_lt (thirdFullRegularizedRadialDen_pos244 δ hδ ξ))

/-- The regularized radial recovery multiplier has pointwise norm at most one.
This bound is uniform in the positive regularization parameter. -/
theorem thirdFullRegularizedRadialFactor_le_one244
    (δ : ℝ) (hδ : 0 < δ) (ξ : Freq244) :
    thirdTriadAxisDot244 ξ ξ /
      (thirdTriadAxisDot244 ξ ξ + δ) ≤ 1 := by
  apply (div_le_iff₀ (thirdFullRegularizedRadialDen_pos244 δ hδ ξ)).2
  linarith

/-- The pointwise loss is exactly δ/(|ξ|²+δ), rather than an unspecified
projection error. This identity enables a later dominated-convergence step. -/
theorem thirdFullRegularizedRadialFactor_error244
    (δ : ℝ) (hδ : 0 < δ) (ξ : Freq244) :
    1 - thirdTriadAxisDot244 ξ ξ /
      (thirdTriadAxisDot244 ξ ξ + δ) =
      δ / (thirdTriadAxisDot244 ξ ξ + δ) := by
  have hn : thirdTriadAxisDot244 ξ ξ + δ ≠ 0 :=
    ne_of_gt (thirdFullRegularizedRadialDen_pos244 δ hδ ξ)
  field_simp [hn]
  <;> ring

/-- The radial normalization cancels the extra factor two from
Hermitianization of a profile that is already Hermitian. -/
theorem thirdFullRegularizedInverseRadius_twice_square244
    (δ : ℝ) (_hδ : 0 < δ) (ξ : Freq244) :
    2 * thirdFullRegularizedInverseRadius244 δ ξ *
        thirdTriadAxisDot244 ξ ξ =
      thirdTriadAxisDot244 ξ ξ /
        (thirdTriadAxisDot244 ξ ξ + δ) := by
  unfold thirdFullRegularizedInverseRadius244
  rw [mul_inv_rev]
  norm_num <;> ring

/-- EXACT radial Fourier profile of the smooth compact Hermitianized
transverse construction. For Hermitian, solenoidal U and even χ the result is
χ |ξ|²/(|ξ|²+δ) U. No normalization factor is missing. -/
theorem thirdFullRegularizedHermitianProfile_exact244
    (δ : ℝ) (hδ : 0 < δ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hUdiv : ∀ ξ, mixedDot ξ (U ξ) = 0)
    (ξ : Freq244) (j : A3) :
    thirdFullCompactHermitianTransverseProfile244 χ
      (thirdFullRegularizedTransverseInput244 δ U) ξ j =
      ((χ ξ * (thirdTriadAxisDot244 ξ ξ /
          (thirdTriadAxisDot244 ξ ξ + δ)) : ℝ) : ℂ) * U ξ j := by
  let W := thirdFullRegularizedTransverseInput244 δ U
  let G := thirdFullComplexCutoffTransverseProfile244 χ W
  have hWHerm : H3ComplexHermitianPolarizationProfile244 W :=
    thirdFullRegularizedTransverseInput_reality244 δ U hUherm
  have hGHerm : H3ComplexHermitianPolarizationProfile244 G :=
    thirdFullComplexCutoffTransverseProfile_reality244 χ W hχeven hWHerm
  have hGneg : G (-ξ) j = star (G ξ j) := congrFun (hGHerm ξ) j
  have hGat : G ξ j =
      (χ ξ : ℂ) *
        ((thirdFullRegularizedInverseRadius244 δ ξ : ℂ) *
          (thirdTriadAxisDot244 ξ ξ : ℂ) * U ξ j) := by
    change (χ ξ : ℂ) *
      thirdFullComplexTransverseNumerator244 ξ (W ξ) j = _
    rw [thirdFullRegularizedTransverseInput_numerator_solenoidal244
      δ U hUdiv ξ j]
  have hScale : 2 * χ ξ * thirdFullRegularizedInverseRadius244 δ ξ *
      thirdTriadAxisDot244 ξ ξ =
      χ ξ * (thirdTriadAxisDot244 ξ ξ /
        (thirdTriadAxisDot244 ξ ξ + δ)) := by
    calc
      _ = χ ξ * (2 * thirdFullRegularizedInverseRadius244 δ ξ *
          thirdTriadAxisDot244 ξ ξ) := by ring
      _ = _ := by rw [thirdFullRegularizedInverseRadius_twice_square244 δ hδ ξ]
  change G ξ j + star (G (-ξ) j) = _
  rw [hGneg, star_star, hGat]
  rw [← hScale]
  push_cast
  ring

/-- Genuine REAL, divergence-free Schwartz velocity for every positive
regularization. This delegates the exact inverse transform, pointwise
reality, and physical divergence calculation to the previously compiled
compact-Hermitian Schwartz construction. -/
noncomputable def thirdFullRegularizedRealSolenoidalSchwartz244
    (δ : ℝ) (hδ : 0 < δ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) :
    A3 → 𝓢(V3, ℝ) :=
  thirdFullCompactRealSolenoidalSchwartz244 χ
    (thirdFullRegularizedTransverseInput244 δ U)
    hχsmooth hχcompact
    (thirdFullRegularizedTransverseInput_contDiff244 δ hδ U hUsmooth)

/-- The full Fourier transform of the ACTUAL real Schwartz velocity is
exactly the smooth regularized transverse Hermitian profile. -/
theorem thirdFullRegularizedRealSolenoidalSchwartz_fourier244
    (δ : ℝ) (hδ : 0 < δ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (ξ : V3) :
    (fun j : A3 => 𝓕 (h3SchwartzComplexify
      (thirdFullRegularizedRealSolenoidalSchwartz244 δ hδ χ U
        hχsmooth hχcompact hUsmooth j)) ξ) =
    thirdFullCompactHermitianTransverseProfile244 χ
      (thirdFullRegularizedTransverseInput244 δ U) (WithLp.ofLp ξ) := by
  exact thirdFullCompactRealSolenoidalSchwartz_fourier_vector244 χ
    (thirdFullRegularizedTransverseInput244 δ U)
    hχsmooth hχcompact
    (thirdFullRegularizedTransverseInput_contDiff244 δ hδ U hUsmooth) ξ

/-- For Hermitian, solenoidal U and an even cutoff the physical Fourier
amplitude is precisely χ |ξ|²/(|ξ|²+δ) U. -/
theorem thirdFullRegularizedRealSolenoidalSchwartz_fourier_exact244
    (δ : ℝ) (hδ : 0 < δ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hUdiv : ∀ ξ, mixedDot ξ (U ξ) = 0)
    (ξ : V3) (j : A3) :
    𝓕 (h3SchwartzComplexify
      (thirdFullRegularizedRealSolenoidalSchwartz244 δ hδ χ U
        hχsmooth hχcompact hUsmooth j)) ξ =
      ((χ (WithLp.ofLp ξ) *
        (thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) /
          (thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) + δ)) : ℝ) : ℂ) *
        U (WithLp.ofLp ξ) j := by
  have h := congrFun (thirdFullRegularizedRealSolenoidalSchwartz_fourier244
    δ hδ χ U hχsmooth hχcompact hUsmooth ξ) j
  rw [h]
  exact thirdFullRegularizedHermitianProfile_exact244 δ hδ χ U
    hχeven hUherm hUdiv (WithLp.ofLp ξ) j

/-- Each regularized real Schwartz vector is physically divergence-free at
EVERY spatial point, not only a.e. in spectral L². -/
theorem thirdFullRegularizedRealSolenoidalSchwartz_physical_divergence244
    (δ : ℝ) (hδ : 0 < δ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) :
    ∀ x : V3, ∑ j : A3,
      fderiv ℝ (h3SchwartzComplexify
        (thirdFullRegularizedRealSolenoidalSchwartz244 δ hδ χ U
          hχsmooth hχcompact hUsmooth j))
        x (h3FourierAxisDirection j) = 0 := by
  exact thirdFullCompactRealSolenoidalSchwartz_physical_divergence244 χ
    (thirdFullRegularizedTransverseInput244 δ U)
    hχsmooth hχcompact
    (thirdFullRegularizedTransverseInput_contDiff244 δ hδ U hUsmooth)

/-- The full-third complex six-symbol is exactly the sixth-power flux for
all momentum-conserving Fourier triads of the actual real Schwartz velocity. -/
theorem thirdFullRegularizedRealSolenoidalSchwartz_six_eq_flux244
    (δ : ℝ) (hδ : 0 < δ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (p q r : V3)
    (hm : ∀ j : A3,
      (WithLp.ofLp p) j + (WithLp.ofLp q) j + (WithLp.ofLp r) j = 0) :
    thirdFullComplexSixSymbol244 (WithLp.ofLp p) (WithLp.ofLp q) (WithLp.ofLp r)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedRealSolenoidalSchwartz244 δ hδ χ U
          hχsmooth hχcompact hUsmooth j)) p)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedRealSolenoidalSchwartz244 δ hδ χ U
          hχsmooth hχcompact hUsmooth j)) q)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedRealSolenoidalSchwartz244 δ hδ χ U
          hχsmooth hχcompact hUsmooth j)) r) =
    thirdFullComplexSixthPowerFlux244 (WithLp.ofLp p) (WithLp.ofLp q) (WithLp.ofLp r)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedRealSolenoidalSchwartz244 δ hδ χ U
          hχsmooth hχcompact hUsmooth j)) p)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedRealSolenoidalSchwartz244 δ hδ χ U
          hχsmooth hχcompact hUsmooth j)) q)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedRealSolenoidalSchwartz244 δ hδ χ U
          hχsmooth hχcompact hUsmooth j)) r) := by
  exact thirdFullCompactRealSolenoidalSchwartz_physical_six_eq_flux244 χ
    (thirdFullRegularizedTransverseInput244 δ U)
    hχsmooth hχcompact
    (thirdFullRegularizedTransverseInput_contDiff244 δ hδ U hUsmooth)
    p q r hm

end
end PrimeTensor.FirstMonomialTriad

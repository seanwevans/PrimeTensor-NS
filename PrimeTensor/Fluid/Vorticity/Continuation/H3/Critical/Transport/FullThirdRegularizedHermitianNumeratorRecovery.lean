import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdCompactHermitianSupportFlatCutoff
import Mathlib.Tactic

/-!
# Real solenoidal Schwartz recovery from arbitrary compact Hermitian input

The previous smooth physical recovery formula required the *input* Fourier
polarization to be pointwise transverse. That is too restrictive to apply
compact-Hermitian density before the Leray operator: the Leray image is only
known to be an L² class and need not be smooth at frequency zero.

This module instead applies the globally smooth, positive-denominator
transverse numerator directly to a smooth compact Hermitian input `U`.
The Hermitianized numerator is twice its single-sided value. The factor
`1/(2*(|ξ|²+δ))` in the construction cancels this doubling, giving exactly

   (|ξ|² U(ξ) - ξ(ξ·U(ξ))) / (|ξ|²+δ)

at every frequency, including zero. No solenoidality of U is assumed.
A support-flat even cutoff exists automatically for any compact U, so it
can be removed from this exact Fourier formula. The inverse Fourier field
is REAL and physically divergence-free, because the preexisting Schwartz
construction proves those properties for every smooth input.

This establishes the smooth numerator side of the remaining finite-index
Leray-symbol bridge. It does not *identify* the finite-index weighted L²
Leray image with this numerator or claim unconditional full H³ density yet.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators ENNReal ContDiff SchwartzMap FourierTransform ComplexConjugate

noncomputable section
set_option maxHeartbeats 1500000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev CPol244 := A3 → ℂ
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeHermitianNumerator244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- An identically zero input polarization has zero transverse numerator. -/
theorem thirdFullComplexTransverseNumerator_zero_input244
    (ξ : Freq244) :
    thirdFullComplexTransverseNumerator244 ξ (0 : CPol244) = 0 := by
  funext j
  simp [thirdFullComplexTransverseNumerator244, mixedDot]

/-- Hermitianization of the regularized polynomial numerator doubles the
single-sided expression. This holds for arbitrary Hermitian input, even
if the input is NOT transverse. No division by |ξ|² occurs. -/
theorem thirdFullRegularizedHermitianProfile_general244
    (δ : ℝ) (_hδ : 0 < δ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (ξ : Freq244) (j : A3) :
    thirdFullCompactHermitianTransverseProfile244 χ
      (thirdFullRegularizedTransverseInput244 δ U) ξ j =
    (2 : ℂ) * (χ ξ : ℂ) *
      (thirdFullRegularizedInverseRadius244 δ ξ : ℂ) *
      thirdFullComplexTransverseNumerator244 ξ (U ξ) j := by
  let W := thirdFullRegularizedTransverseInput244 δ U
  let G := thirdFullComplexCutoffTransverseProfile244 χ W
  have hWHerm : H3ComplexHermitianPolarizationProfile244 W :=
    thirdFullRegularizedTransverseInput_reality244 δ U hUherm
  have hGHerm : H3ComplexHermitianPolarizationProfile244 G :=
    thirdFullComplexCutoffTransverseProfile_reality244 χ W hχeven hWHerm
  have hCoordNeg : (fun k : A3 => -ξ k) = -ξ := by
    funext k
    simp only [Pi.neg_apply]
  have hNeg : G (-ξ) j = star (G ξ j) := by
    simpa only [hCoordNeg] using congrFun (hGHerm ξ) j
  have hAt : G ξ j =
      (χ ξ : ℂ) *
        ((thirdFullRegularizedInverseRadius244 δ ξ : ℂ) *
          thirdFullComplexTransverseNumerator244 ξ (U ξ) j) := by
    change (χ ξ : ℂ) *
      thirdFullComplexTransverseNumerator244 ξ (W ξ) j = _
    rw [thirdFullRegularizedTransverseInput_numerator244 δ U ξ j]
  change G ξ j + star (G (-ξ) j) = _
  rw [hNeg, star_star, hAt]
  ring

/-- The inverse of twice the positive radial denominator has the exact
factor-of-two normalization needed after Hermitian symmetrization. -/
theorem thirdFullRegularizedInverseRadius_twice_eq_inv244
    (δ : ℝ) (hδ : 0 < δ) (ξ : Freq244) :
    2 * thirdFullRegularizedInverseRadius244 δ ξ =
      (thirdTriadAxisDot244 ξ ξ + δ)⁻¹ := by
  have hDen : thirdTriadAxisDot244 ξ ξ + δ ≠ 0 :=
    ne_of_gt (thirdFullRegularizedRadialDen_pos244 δ hδ ξ)
  unfold thirdFullRegularizedInverseRadius244
  field_simp [hDen]
  <;> ring

/-- Smooth Hermitian transverse recovery is the precise normalized Leray
numerator for an arbitrary (not necessarily solenoidal) Hermitian input. -/
theorem thirdFullRegularizedHermitianProfile_fraction244
    (δ : ℝ) (hδ : 0 < δ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (ξ : Freq244) (j : A3) :
    thirdFullCompactHermitianTransverseProfile244 χ
      (thirdFullRegularizedTransverseInput244 δ U) ξ j =
    ((χ ξ : ℂ) *
      (((thirdTriadAxisDot244 ξ ξ + δ)⁻¹ : ℝ) : ℂ)) *
      thirdFullComplexTransverseNumerator244 ξ (U ξ) j := by
  rw [thirdFullRegularizedHermitianProfile_general244
    δ hδ χ U hχeven hUherm ξ j]
  have hInv : (2 : ℂ) *
      (thirdFullRegularizedInverseRadius244 δ ξ : ℂ) =
      (((thirdTriadAxisDot244 ξ ξ + δ)⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast thirdFullRegularizedInverseRadius_twice_eq_inv244 δ hδ ξ
  calc
    (2 : ℂ) * (χ ξ : ℂ) *
        (thirdFullRegularizedInverseRadius244 δ ξ : ℂ) *
        thirdFullComplexTransverseNumerator244 ξ (U ξ) j =
      ((χ ξ : ℂ) *
        ((2 : ℂ) * (thirdFullRegularizedInverseRadius244 δ ξ : ℂ))) *
        thirdFullComplexTransverseNumerator244 ξ (U ξ) j := by ring
    _ = _ := by rw [hInv]

/-- Pointwise Fourier formula for the ACTUAL real physical Schwartz field
built from a Hermitian input. The input itself need not be transverse. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_fourier_general244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (ξ : V3) (j : A3) :
    𝓕 (h3SchwartzComplexify
      (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
        hχsmooth hχcompact hUsmooth j)) ξ =
    ((χ (WithLp.ofLp ξ) : ℂ) *
      (((thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) +
        h3FullThirdRegularizationScale244 n)⁻¹ : ℝ) : ℂ)) *
      thirdFullComplexTransverseNumerator244 (WithLp.ofLp ξ)
        (U (WithLp.ofLp ξ)) j := by
  have hFourier := congrFun
    (thirdFullRegularizedRealSolenoidalSchwartz_fourier244
      (h3FullThirdRegularizationScale244 n)
      (h3FullThirdRegularizationScale_pos244 n)
      χ U hχsmooth hχcompact hUsmooth ξ) j
  change 𝓕 (h3SchwartzComplexify
      (thirdFullRegularizedRealSolenoidalSchwartz244
        (h3FullThirdRegularizationScale244 n)
        (h3FullThirdRegularizationScale_pos244 n)
        χ U hχsmooth hχcompact hUsmooth j)) ξ = _
  rw [hFourier]
  exact thirdFullRegularizedHermitianProfile_fraction244
    (h3FullThirdRegularizationScale244 n)
    (h3FullThirdRegularizationScale_pos244 n)
    χ U hχeven hUherm (WithLp.ofLp ξ) j

/-- A compact input's support-flat cutoff can be removed from its
transverse numerator: if the vector input vanishes, so does the numerator. -/
theorem thirdFullRegularizedHermitianProfile_fraction_no_cutoff244
    (δ : ℝ) (hδ : 0 < δ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hχone : ∀ ξ j, U ξ j ≠ 0 → χ ξ = 1)
    (ξ : Freq244) (j : A3) :
    thirdFullCompactHermitianTransverseProfile244 χ
      (thirdFullRegularizedTransverseInput244 δ U) ξ j =
    (((thirdTriadAxisDot244 ξ ξ + δ)⁻¹ : ℝ) : ℂ) *
      thirdFullComplexTransverseNumerator244 ξ (U ξ) j := by
  rw [thirdFullRegularizedHermitianProfile_fraction244
    δ hδ χ U hχeven hUherm ξ j]
  by_cases hZero : U ξ = 0
  · have hNum : thirdFullComplexTransverseNumerator244 ξ (U ξ) j = 0 := by
      rw [hZero]
      exact congrFun (thirdFullComplexTransverseNumerator_zero_input244 ξ) j
    simp only [hNum, mul_zero]
  · have hSome : ∃ k : A3, U ξ k ≠ 0 := by
      by_contra hNo
      push_neg at hNo
      apply hZero
      funext k
      exact hNo k
    obtain ⟨k, hk⟩ := hSome
    rw [hχone ξ k hk]
    simp

/-- A compact support-flat even window removes itself from the exact Fourier
numerator of the physical real Schwartz field, even without input divergence. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_fourier_no_div244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hχone : ∀ ξ j, U ξ j ≠ 0 → χ ξ = 1)
    (ξ : V3) (j : A3) :
    𝓕 (h3SchwartzComplexify
      (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
        hχsmooth hχcompact hUsmooth j)) ξ =
    (((thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) +
      h3FullThirdRegularizationScale244 n)⁻¹ : ℝ) : ℂ) *
      thirdFullComplexTransverseNumerator244 (WithLp.ofLp ξ)
        (U (WithLp.ofLp ξ)) j := by
  have hFourier := congrFun
    (thirdFullRegularizedRealSolenoidalSchwartz_fourier244
      (h3FullThirdRegularizationScale244 n)
      (h3FullThirdRegularizationScale_pos244 n)
      χ U hχsmooth hχcompact hUsmooth ξ) j
  change 𝓕 (h3SchwartzComplexify
      (thirdFullRegularizedRealSolenoidalSchwartz244
        (h3FullThirdRegularizationScale244 n)
        (h3FullThirdRegularizationScale_pos244 n)
        χ U hχsmooth hχcompact hUsmooth j)) ξ = _
  rw [hFourier]
  exact thirdFullRegularizedHermitianProfile_fraction_no_cutoff244
    (h3FullThirdRegularizationScale244 n)
    (h3FullThirdRegularizationScale_pos244 n)
    χ U hχeven hUherm hχone (WithLp.ofLp ξ) j

/-- NO transverse-input hypothesis: a smooth, compact, Hermitian input
produces an actual REAL, physically divergence-free Schwartz velocity whose
Fourier transform is the regularized Leray numerator, exactly at every ξ.
The cutoff is selected internally by the proven support-flat bump theorem. -/
theorem exists_thirdFullRegularizedPhysicalSchwartz_of_compactHermitian244
    (n : ℕ) (U : Freq244 → CPol244)
    (hUcompact : HasCompactSupport U)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U) :
    ∃ χ : Freq244 → ℝ,
      ∃ (hχsmooth : ContDiff ℝ ∞ χ),
      ∃ (hχcompact : HasCompactSupport χ),
        (∀ (ξ : V3) (j : A3),
          𝓕 (h3SchwartzComplexify
            (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
              hχsmooth hχcompact hUsmooth j)) ξ =
          (((thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) +
            h3FullThirdRegularizationScale244 n)⁻¹ : ℝ) : ℂ) *
            thirdFullComplexTransverseNumerator244 (WithLp.ofLp ξ)
              (U (WithLp.ofLp ξ)) j) ∧
        (∀ x : V3, ∑ j : A3,
          fderiv ℝ (h3SchwartzComplexify
            (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
              hχsmooth hχcompact hUsmooth j))
            x (h3FourierAxisDirection j) = 0) := by
  obtain ⟨χ, hχsmooth, hχcompact, hEven, hFlat⟩ :=
    exists_thirdFullAxisSupportFlatEvenCutoff244 U hUcompact
  refine ⟨χ, hχsmooth, hχcompact, ?_, ?_⟩
  · intro ξ j
    exact thirdFullRegularizedPhysicalSchwartzAt_fourier_no_div244
      n χ U hχsmooth hχcompact hUsmooth hEven hUherm hFlat ξ j
  · exact thirdFullRegularizedPhysicalSchwartzAt_divergence244
      n χ U hχsmooth hχcompact hUsmooth

/-- The precise full H³ spectral-weight multiplier remains on the outside
of the ACTUAL Schwartz Fourier transform. This is the quantity that must be
matched to the finite-index Leray operator in the next theorem. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_weighted_no_div244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hχone : ∀ ξ j, U ξ j ≠ 0 → χ ξ = 1)
    (ξ : V3) (j : A3) :
    (h3SobolevFrequencyWeight ξ : ℂ) *
      𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
          hχsmooth hχcompact hUsmooth j)) ξ =
    (((thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) +
      h3FullThirdRegularizationScale244 n)⁻¹ : ℝ) : ℂ) *
      thirdFullComplexTransverseNumerator244 (WithLp.ofLp ξ)
        (fun k : A3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          U (WithLp.ofLp ξ) k) j := by
  rw [thirdFullRegularizedPhysicalSchwartzAt_fourier_no_div244
    n χ U hχsmooth hχcompact hUsmooth hχeven hUherm hχone ξ j]
  rw [thirdFullComplexTransverseNumerator_const_mul244
    (WithLp.ofLp ξ) (U (WithLp.ofLp ξ))
    (h3SobolevFrequencyWeight ξ : ℂ)]
  ring

end
end PrimeTensor.FirstMonomialTriad

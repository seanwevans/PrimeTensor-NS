import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealInterpolationReflection244
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Exact physical integral of the complete Hermitian-even full-third density

The previous module assembled the actual 3+3+1 and 3+2+2 seven-derivative
real Fourier density, proved it even under reflection, and established
coherent-tube support. This module proves that its integral is EXACTLY the
full static physical H³ third commutator of our real divergence-free Schwartz
velocity. It commutes four gradient integrals and five finite index sums,
retains the physical pairing 2 and interpolation 6, and uses the genuine
Schwartz absolute integrability before applying the real-part integral map.

The integrated sign is NOT determined; evenness alone does not imply it.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap FourierTransform Topology

noncomputable section
set_option maxHeartbeats 1400000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev V3 := H3FourierPoint3
private abbrev PairV244 := V3 × V3

noncomputable local instance axisFintypeFullThirdDensityInt244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Four actual complex Fourier gradient slots at a fixed five-axis label,
including 2 from the physical energy pairing and all seven derivatives. -/
noncomputable def thirdFullAxisRealGradientAxisComplexDensity244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j i k l r : A3) (z : PairV244) : ℂ :=
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  (2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
    (((thirdFullAxisRealGradientSlot244 ρ hρ A B C j r j a b c a b c d z +
       thirdFullAxisRealGradientSlot244 ρ hρ A B C j j r a b c a b d c z) +
       thirdFullAxisRealGradientSlot244 ρ hρ A B C j j r a b c a d c b z) +
       thirdFullAxisRealGradientSlot244 ρ hρ A B C j j r a b c d b c a z)

/-- The four literal gradient Schwartz slots are absolutely integrable. -/
theorem thirdFullAxisRealGradientAxisComplexDensity_integrable244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (j i k l r : A3) :
    Integrable (thirdFullAxisRealGradientAxisComplexDensity244
      ρ hρ A B C j i k l r) (volume.prod volume) := by
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  have h1 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j r j a b c a b c d
  have h2 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j j r a b c a b d c
  have h3 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j j r a b c a d c b
  have h4 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j j r a b c d b c a
  exact (((h1.add h2).add h3).add h4).const_mul _

/-- The Fourier gradient axis block is literally the integral of its four
actual kernels: no altered multiplier and no missing Fourier normalization. -/
theorem thirdFullAxisRealGradientAxisComplexDensity_integral244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (j i k l r : A3) :
    (∫ z : PairV244,
      thirdFullAxisRealGradientAxisComplexDensity244 ρ hρ A B C j i k l r z
      ∂volume.prod volume) =
    thirdGradientSchwartzAxisFourier244
      (fun t => h3SchwartzComplexify
        (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C t))
      j i k l r := by
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  have h1 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j r j a b c a b c d
  have h2 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j j r a b c a b d c
  have h3 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j j r a b c a d c b
  have h4 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j j r a b c d b c a
  -- Keep the four integrands in exactly the same syntactic form as h1--h4.
  -- Broad `unfold`/`dsimp` previously expanded the local directions on
  -- only one side, preventing `integral_add` from matching.
  change
    (∫ z : PairV244,
      (2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
        (((thirdFullAxisRealGradientSlot244 ρ hρ A B C
              j r j a b c a b c d z +
            thirdFullAxisRealGradientSlot244 ρ hρ A B C
              j j r a b c a b d c z) +
            thirdFullAxisRealGradientSlot244 ρ hρ A B C
              j j r a b c a d c b z) +
            thirdFullAxisRealGradientSlot244 ρ hρ A B C
              j j r a b c d b c a z)
      ∂volume.prod volume) =
    (2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
      (((∫ z : PairV244,
           thirdFullAxisRealGradientSlot244 ρ hρ A B C
             j r j a b c a b c d z ∂volume.prod volume) +
         (∫ z : PairV244,
           thirdFullAxisRealGradientSlot244 ρ hρ A B C
             j j r a b c a b d c z ∂volume.prod volume)) +
        (∫ z : PairV244,
           thirdFullAxisRealGradientSlot244 ρ hρ A B C
             j j r a b c a d c b z ∂volume.prod volume) +
        (∫ z : PairV244,
           thirdFullAxisRealGradientSlot244 ρ hρ A B C
             j j r a b c d b c a z ∂volume.prod volume))
  -- `integral_add` is stated for functions added in the Pi additive group.
  -- The integrand above is a lambda with pointwise additions.  Introduce
  -- those functions explicitly and use the integral lemma by `exact`,
  -- rather than asking `rw` to discover a function-level sum under a lambda.
  let F1 : PairV244 → ℂ := thirdFullAxisRealGradientSlot244 ρ hρ A B C
    j r j a b c a b c d
  let F2 : PairV244 → ℂ := thirdFullAxisRealGradientSlot244 ρ hρ A B C
    j j r a b c a b d c
  let F3 : PairV244 → ℂ := thirdFullAxisRealGradientSlot244 ρ hρ A B C
    j j r a b c a d c b
  let F4 : PairV244 → ℂ := thirdFullAxisRealGradientSlot244 ρ hρ A B C
    j j r a b c d b c a
  have hFour :
      (∫ z : PairV244, ((F1 z + F2 z) + F3 z) + F4 z
        ∂volume.prod volume) =
      (((∫ z : PairV244, F1 z ∂volume.prod volume) +
        (∫ z : PairV244, F2 z ∂volume.prod volume)) +
        (∫ z : PairV244, F3 z ∂volume.prod volume)) +
        (∫ z : PairV244, F4 z ∂volume.prod volume) := by
    calc
      _ = (∫ z : PairV244, ((F1 + F2) + F3) z
              ∂volume.prod volume) +
            (∫ z : PairV244, F4 z ∂volume.prod volume) := by
          exact integral_add ((h1.add h2).add h3) h4
      _ = (((∫ z : PairV244, (F1 + F2) z ∂volume.prod volume) +
              (∫ z : PairV244, F3 z ∂volume.prod volume)) +
            (∫ z : PairV244, F4 z ∂volume.prod volume)) := by
          -- `congrArg` uses the exact function-valued integral lemma:
          -- there is no rewrite of an expanded slot lambda to search for.
          exact congrArg
            (fun w : ℂ => w +
              (∫ z : PairV244, F4 z ∂volume.prod volume))
            (integral_add (h1.add h2) h3)
      _ = _ := by
          exact congrArg
            (fun w : ℂ =>
              (w + (∫ z : PairV244, F3 z ∂volume.prod volume)) +
                (∫ z : PairV244, F4 z ∂volume.prod volume))
            (integral_add h1 h2)
  change
    (∫ z : PairV244,
      (2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
        (((F1 z + F2 z) + F3 z) + F4 z)
      ∂volume.prod volume) =
    (2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
      ((((∫ z : PairV244, F1 z ∂volume.prod volume) +
        (∫ z : PairV244, F2 z ∂volume.prod volume)) +
        (∫ z : PairV244, F3 z ∂volume.prod volume)) +
        (∫ z : PairV244, F4 z ∂volume.prod volume))
  rw [integral_const_mul, hFour]

/-- Finite gradient-index sum of the exact complex Fourier densities. -/
noncomputable def thirdFullAxisRealGradientTotalComplexDensity244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) : ℂ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
    thirdFullAxisRealGradientAxisComplexDensity244
      ρ hρ A B C j i k l r z

/-- The complete complex five-index gradient integrand is integrable. -/
theorem thirdFullAxisRealGradientTotalComplexDensity_integrable244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    Integrable (thirdFullAxisRealGradientTotalComplexDensity244 ρ hρ A B C)
      (volume.prod volume) := by
  unfold thirdFullAxisRealGradientTotalComplexDensity244
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro l _
  apply integrable_finsetSum
  intro r _
  exact thirdFullAxisRealGradientAxisComplexDensity_integrable244
    ρ hρ A B C j i k l r

/-- All five finite axis sums commute with the genuine Schwartz frequency
integral, recovering the original full gradient Fourier coefficient. -/
theorem thirdFullAxisRealGradientTotalComplexDensity_integral244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    (∫ z : PairV244,
      thirdFullAxisRealGradientTotalComplexDensity244 ρ hρ A B C z
      ∂volume.prod volume) =
    thirdGradientFourierTotalComplex244
      (fun t => h3SchwartzComplexify
        (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C t)) := by
  have h4 (j i k l : A3) := integrable_finsetSum Finset.univ
    (fun r _ => thirdFullAxisRealGradientAxisComplexDensity_integrable244
      ρ hρ A B C j i k l r)
  have h3 (j i k : A3) := integrable_finsetSum Finset.univ
    (fun l _ => h4 j i k l)
  have h2 (j i : A3) := integrable_finsetSum Finset.univ
    (fun k _ => h3 j i k)
  have h1 (j : A3) := integrable_finsetSum Finset.univ
    (fun i _ => h2 j i)
  unfold thirdFullAxisRealGradientTotalComplexDensity244
    thirdGradientFourierTotalComplex244
  rw [integral_finsetSum Finset.univ (fun j _ => h1 j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun i _ => h2 j i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun k _ => h3 j i k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum Finset.univ (fun l _ => h4 j i k l)]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_finsetSum Finset.univ (fun r _ =>
    thirdFullAxisRealGradientAxisComplexDensity_integrable244
      ρ hρ A B C j i k l r)]
  apply Finset.sum_congr rfl
  intro r _
  exact thirdFullAxisRealGradientAxisComplexDensity_integral244
    ρ hρ A B C j i k l r

/-- The exact entire complex Fourier density, with gradient and
interpolation transport grouped before integration. -/
noncomputable def thirdFullAxisRealThirdComplexDensity244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) : ℂ :=
  thirdFullAxisRealGradientTotalComplexDensity244 ρ hρ A B C z +
    (6 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
      thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z

/-- Integrability of the complete complex Fourier density. -/
theorem thirdFullAxisRealThirdComplexDensity_integrable244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    Integrable (thirdFullAxisRealThirdComplexDensity244 ρ hρ A B C)
      (volume.prod volume) := by
  exact (thirdFullAxisRealGradientTotalComplexDensity_integrable244
    ρ hρ A B C).add
      ((thirdFullAxisRealInterpolationKernel_integrable244
        ρ hρ A B C).const_mul _)

/-- Actual FULL Schwartz physical complex coefficient equals the integral
of the complete pointwise frequency density, without any cutoffs inserted. -/
theorem thirdFullAxisRealThirdComplexDensity_integral244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    (∫ z : PairV244,
      thirdFullAxisRealThirdComplexDensity244 ρ hρ A B C z
      ∂volume.prod volume) =
    fullThirdSchwartzFourierCoefficient244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) := by
  have hG := thirdFullAxisRealGradientTotalComplexDensity_integrable244
    ρ hρ A B C
  have hI := (thirdFullAxisRealInterpolationKernel_integrable244
    ρ hρ A B C).const_mul (6 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7)
  unfold thirdFullAxisRealThirdComplexDensity244
  rw [integral_add hG hI, integral_const_mul,
    thirdFullAxisRealGradientTotalComplexDensity_integral244]
  change _ = thirdGradientFourierTotalComplex244
      (fun t => h3SchwartzComplexify
        (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C t)) +
    6 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      (∫ z : PairV244,
        thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z
        ∂volume.prod volume)
  rfl

/-- The existing real density agrees pointwise with the REAL part of the
complex density, including the factors 2 and 6. -/
theorem thirdFullAxisRealThirdSignedDensity_eq_complex_re244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) :
    thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C z =
      (thirdFullAxisRealThirdComplexDensity244 ρ hρ A B C z).re := by
  have hTwo (w : ℂ) : ((2 : ℂ) * w).re = 2 * w.re := by
    norm_num [Complex.mul_re]
  have hSix (w : ℂ) : ((6 : ℂ) * w).re = 6 * w.re := by
    norm_num [Complex.mul_re]
  have hTwoScale (c w : ℂ) : (((2 : ℂ) * c) * w).re =
      2 * (c * w).re := by
    rw [mul_assoc, hTwo]
  have hSixScale (c w : ℂ) : (((6 : ℂ) * c) * w).re =
      6 * (c * w).re := by
    rw [mul_assoc, hSix]
  have hAxis (j i k l r : A3) :
      thirdFullAxisRealGradientAxisSignedDensity244
        ρ hρ A B C j i k l r z =
      (thirdFullAxisRealGradientAxisComplexDensity244
        ρ hρ A B C j i k l r z).re := by
    unfold thirdFullAxisRealGradientAxisSignedDensity244
      thirdFullAxisRealGradientAxisComplexDensity244
    dsimp only
    rw [hTwoScale]
    simp only [mul_add, Complex.add_re]
  have hSumRe :
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
        thirdFullAxisRealGradientAxisComplexDensity244
          ρ hρ A B C j i k l r z).re =
      ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
        (thirdFullAxisRealGradientAxisComplexDensity244
          ρ hρ A B C j i k l r z).re := by
    change Complex.reCLM
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
        thirdFullAxisRealGradientAxisComplexDensity244
          ρ hρ A B C j i k l r z) = _
    simp only [map_sum, Complex.reCLM_apply]
  change
    (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
      thirdFullAxisRealGradientAxisSignedDensity244
        ρ hρ A B C j i k l r z) +
      6 * (((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z).re) =
    ((∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
      thirdFullAxisRealGradientAxisComplexDensity244
        ρ hρ A B C j i k l r z) +
      (6 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
        thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z).re
  rw [Complex.add_re, hSumRe]
  -- Strip the real scalar six BEFORE expanding complex multiplication.
  rw [hSixScale]
  simp_rw [hAxis]

/-- The real density is absolutely integrable. -/
theorem thirdFullAxisRealThirdSignedDensity_integrable244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    Integrable (thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C)
      (volume.prod volume) := by
  have h := Complex.reCLM.integrable_comp
    (thirdFullAxisRealThirdComplexDensity_integrable244 ρ hρ A B C)
  exact h.congr (Filter.Eventually.of_forall (fun z =>
    (thirdFullAxisRealThirdSignedDensity_eq_complex_re244 ρ hρ A B C z).symm))

/-- The exact REAL physical H³ third-order static commutator of the genuine
real solenoidal Schwartz packet is the global integral of the assembled
reflection-even signed density, not merely an auxiliary Fourier polynomial. -/
theorem thirdFullAxisRealThirdCommutator_eq_signedDensity_integral244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    fullSchwartzThirdCommutator244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
    ∫ z : PairV244,
      thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C z
      ∂volume.prod volume := by
  rw [thirdFullAxisRealSchwartz_commutator_eq_fourier244,
    ← thirdFullAxisRealThirdComplexDensity_integral244]
  have h := Complex.reCLM.integral_comp_comm
    (thirdFullAxisRealThirdComplexDensity_integrable244 ρ hρ A B C)
  calc
    (∫ z : PairV244, thirdFullAxisRealThirdComplexDensity244 ρ hρ A B C z
        ∂volume.prod volume).re =
      ∫ z : PairV244,
        (thirdFullAxisRealThirdComplexDensity244 ρ hρ A B C z).re
        ∂volume.prod volume := by
          simpa only [Complex.reCLM_apply] using h.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      exact (thirdFullAxisRealThirdSignedDensity_eq_complex_re244
        ρ hρ A B C z).symm

/-- The full physical commutator integral is supported in the same coherent
12-center tube, now DIRECTLY as the integral of its actual signed density. -/
theorem thirdFullAxisRealThirdCommutator_eq_signedDensity_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (A B C : Freq244) :
    fullSchwartzThirdCommutator244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
    ∫ z : PairV244,
      (thirdFullAxisRealHilbertCoherentTube244 δ).indicator
        (thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C) z
      ∂volume.prod volume := by
  rw [thirdFullAxisRealThirdCommutator_eq_signedDensity_integral244]
  apply integral_congr_ae
  filter_upwards with z
  classical
  change thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C z =
    if z ∈ thirdFullAxisRealHilbertCoherentTube244 δ then
      thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C z else 0
  split_ifs with hz
  · rfl
  · exact thirdFullAxisRealThirdSignedDensity_zero_off_tube244
      ρ hρ hSmall δ hρδ A B C z hz

/-- For each positive 12-center tube radius a single narrow packet width
localizes the EXACT physical signed-density integral for EVERY polarization. -/
theorem thirdFullAxisRealThirdCommutator_exists_signedDensity_tube244
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ) ∧
      ∀ A B C : Freq244,
        fullSchwartzThirdCommutator244
          (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
        ∫ z : PairV244,
          (thirdFullAxisRealHilbertCoherentTube244 δ).indicator
            (thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C) z
          ∂volume.prod volume := by
  let σ := lowNormalSixCenterSeparationRadius (1 : ℝ)
  have hσ : 0 < σ :=
    lowNormalSixCenterSeparationRadius_pos (1 : ℝ) (by norm_num)
  let ρ := min δ σ / 2
  have hρ : 0 < ρ := half_pos (lt_min hδ hσ)
  have hSmall : ρ ≤ σ := by
    dsimp [ρ]
    linarith [min_le_right δ σ]
  have hρδ : ρ ≤ δ := by
    dsimp [ρ]
    linarith [min_le_left δ σ]
  refine ⟨ρ, hρ, hSmall, ?_⟩
  intro A B C
  exact thirdFullAxisRealThirdCommutator_eq_signedDensity_tube244
    ρ hρ hSmall δ hρδ A B C

end
end PrimeTensor.FirstMonomialTriad

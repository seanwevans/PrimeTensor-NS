import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRegularizedPhysicalWeightedFourierBridge
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic

/-!
# Support-flat Hermitian frequency cutoffs on the actual depth-three axis carrier

The physical Schwartz / weighted-H³ Fourier bridge constructed in the previous
module requires an even, smooth, compact-frequency scalar cutoff which equals
one on the support of a given smooth transverse Hermitian vector profile.
That cutoff is not an additional hypothesis: compact support is bounded in the
finite-dimensional real axis carrier, and a ContDiffBump centered at zero with
large enough inner radius equals one throughout the support.

We prove the cutoff selection for ANY compactly supported complex vector
profile, with no smoothness, solenoidality, or Hermitian assumptions. The
radial bump is even by the actual Mathlib `ContDiffBump.neg` identity, so it
does not disturb Fourier reality. The final theorem eliminates ALL cutoff
hypotheses from the earlier moving physical Schwartz assembly.

The substantive remaining gap is the construction of genuinely smooth compact
pointwise transverse Fourier representatives for a general real solenoidal
weighted H³ spectral datum. This file does not assume that a measurable Leray
projection is smooth at zero and does not assert that missing density result.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology Set PrimeTensor.Bridge.Euclidean
open scoped ENNReal BigOperators ContDiff SchwartzMap FourierTransform

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev CPol244 := A3 → ℂ
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeSupportFlat244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Smooth even bump with inner radius `R` and outer radius `2R` on the
original finite-axis real Fourier carrier (not a surrogate `Fin 3` space). -/
noncomputable def thirdFullAxisSupportFlatBump244
    (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : Freq244) where
  rIn := R
  rOut := 2 * R
  rIn_pos := hR
  rIn_lt_rOut := by nlinarith

@[simp] theorem thirdFullAxisSupportFlatBump_rIn244
    (R : ℝ) (hR : 0 < R) :
    (thirdFullAxisSupportFlatBump244 R hR).rIn = R := rfl

@[simp] theorem thirdFullAxisSupportFlatBump_rOut244
    (R : ℝ) (hR : 0 < R) :
    (thirdFullAxisSupportFlatBump244 R hR).rOut = 2 * R := rfl

/-- Evenness is an exact pointwise statement, including frequency zero. -/
theorem thirdFullAxisSupportFlatBump_even244
    (R : ℝ) (hR : 0 < R) (ξ : Freq244) :
    thirdFullAxisSupportFlatBump244 R hR (fun j => -ξ j) =
      thirdFullAxisSupportFlatBump244 R hR ξ := by
  have hNeg : (fun j : A3 => -ξ j) = -ξ := by
    funext j
    simp only [Pi.neg_apply]
  rw [hNeg]
  exact (thirdFullAxisSupportFlatBump244 R hR).neg ξ

/-- A support-flat cutoff is nonnegative at every frequency. -/
theorem thirdFullAxisSupportFlatBump_nonneg244
    (R : ℝ) (hR : 0 < R) (ξ : Freq244) :
    0 ≤ thirdFullAxisSupportFlatBump244 R hR ξ :=
  (thirdFullAxisSupportFlatBump244 R hR).nonneg

/-- A support-flat cutoff is bounded by one everywhere. -/
theorem thirdFullAxisSupportFlatBump_le_one244
    (R : ℝ) (hR : 0 < R) (ξ : Freq244) :
    thirdFullAxisSupportFlatBump244 R hR ξ ≤ 1 :=
  (thirdFullAxisSupportFlatBump244 R hR).le_one

/-- The axis cutoff is smooth of every order. -/
theorem thirdFullAxisSupportFlatBump_contDiff244
    (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (thirdFullAxisSupportFlatBump244 R hR : Freq244 → ℝ) := by
  simpa using
    ((thirdFullAxisSupportFlatBump244 R hR).contDiff (n := (⊤ : ℕ∞)))

/-- Its support is compact, with no restriction on the multiplied field. -/
theorem thirdFullAxisSupportFlatBump_hasCompactSupport244
    (R : ℝ) (hR : 0 < R) :
    HasCompactSupport
      (thirdFullAxisSupportFlatBump244 R hR : Freq244 → ℝ) :=
  (thirdFullAxisSupportFlatBump244 R hR).hasCompactSupport

/-- The cutoff is identically one on the entire closed inner ball. -/
theorem thirdFullAxisSupportFlatBump_eq_one244
    (R : ℝ) (hR : 0 < R) (ξ : Freq244)
    (hξ : ‖ξ‖ ≤ R) :
    thirdFullAxisSupportFlatBump244 R hR ξ = 1 := by
  apply (thirdFullAxisSupportFlatBump244 R hR).one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right,
    thirdFullAxisSupportFlatBump_rIn244] using hξ

/-- Unconditional support-flat, even, smooth compact cutoff selection for
ANY compactly supported complex depth-three vector Fourier profile.

This is the exact missing cutoff witness required by the real solenoidal
Schwartz / weighted-H³ bridge. The last property is componentwise because
the physical construction is indexed by the intrinsic depth-three axis. -/
theorem exists_thirdFullAxisSupportFlatEvenCutoff244
    (U : Freq244 → CPol244)
    (hU : HasCompactSupport U) :
    ∃ χ : Freq244 → ℝ,
      ContDiff ℝ ∞ χ ∧
      HasCompactSupport χ ∧
      (∀ ξ : Freq244, χ (fun j => -ξ j) = χ ξ) ∧
      (∀ (ξ : Freq244) (j : A3), U ξ j ≠ 0 → χ ξ = 1) := by
  obtain ⟨R, hBall⟩ :=
    (hU.isCompact.isBounded).subset_closedBall (0 : Freq244)
  let ρ : ℝ := max R 1
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (le_max_right R 1)
  refine ⟨thirdFullAxisSupportFlatBump244 ρ hρ,
    thirdFullAxisSupportFlatBump_contDiff244 ρ hρ,
    thirdFullAxisSupportFlatBump_hasCompactSupport244 ρ hρ,
    thirdFullAxisSupportFlatBump_even244 ρ hρ, ?_⟩
  intro ξ j hj
  have hUne : U ξ ≠ 0 := by
    intro hZero
    apply hj
    simp only [hZero, Pi.zero_apply]
  have hMem : ξ ∈ tsupport U :=
    subset_tsupport U hUne
  have hBound : ‖ξ‖ ≤ R := by
    have hIn := hBall hMem
    simpa only [Metric.mem_closedBall, dist_zero_right] using hIn
  exact thirdFullAxisSupportFlatBump_eq_one244 ρ hρ ξ
    (le_trans hBound (le_max_left R 1))

/-- Every compact smooth Hermitian transverse profile has an ACTUAL real
solenoidal Schwartz reconstruction at every regularization scale, with no
cutoff argument left to supply. Its Fourier transform equals the regularized
input pointwise and its physical divergence is identically zero. -/
theorem exists_thirdFullRealSchwartzRecovery_of_compactProfile244
    (n : ℕ) (U : Freq244 → CPol244)
    (hUcompact : HasCompactSupport U)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hUdiv : ∀ ξ, mixedDot ξ (U ξ) = 0) :
    ∃ χ : Freq244 → ℝ,
      ∃ (hχsmooth : ContDiff ℝ ∞ χ),
      ∃ (hχcompact : HasCompactSupport χ),
        (∀ (ξ : V3) (j : A3),
          𝓕 (h3SchwartzComplexify
            (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
              hχsmooth hχcompact hUsmooth j)) ξ =
            (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) *
              U (WithLp.ofLp ξ) j) ∧
        (∀ x : V3, ∑ j : A3,
          fderiv ℝ (h3SchwartzComplexify
            (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
              hχsmooth hχcompact hUsmooth j))
            x (h3FourierAxisDirection j) = 0) := by
  obtain ⟨χ, hχsmooth, hχcompact, hEven, hFlat⟩ :=
    exists_thirdFullAxisSupportFlatEvenCutoff244 U hUcompact
  refine ⟨χ, hχsmooth, hχcompact, ?_, ?_⟩
  · intro ξ j
    exact thirdFullRegularizedPhysicalSchwartzAt_fourier_no_cutoff244
      n χ U hχsmooth hχcompact hUsmooth hEven hUherm hUdiv
      hFlat ξ j
  · exact thirdFullRegularizedPhysicalSchwartzAt_divergence244
      n χ U hχsmooth hχcompact hUsmooth

/-- Apply the support-flat cutoff selection *to the entire moving physical
Schwartz sequence*. There are now NO externally supplied cutoff functions,
cutoff-smoothness assumptions, cutoff-evenness assumptions or cutoff-flatness
assumptions in this theorem.

The remaining source hypotheses are precisely (a) a moving weighted-H³
approximation, and (b) smooth, compactly supported, pointwise Hermitian and
transverse Fourier representatives of those moving spectral states. -/
theorem exists_thirdFullPhysicalSchwartzMovingCompletion_of_compactProfiles244
    (target : H3SpectralVelocityState)
    (F : ℕ → H3SpectralVelocityState)
    (hFconverges : Tendsto F atTop (𝓝 target))
    (U : ℕ → Freq244 → CPol244)
    (hUcompact : ∀ n, HasCompactSupport (U n))
    (hUsmooth : ∀ n, ContDiff ℝ ∞ (U n))
    (hUherm : ∀ n, H3ComplexHermitianPolarizationProfile244 (U n))
    (hUdiv : ∀ n ξ, mixedDot ξ (U n ξ) = 0)
    (hFweighted : ∀ n i,
      (F n i : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          U n (WithLp.ofLp ξ) (h3AxisOfFin3 i))) :
    ∃ χ : ℕ → Freq244 → ℝ,
      ∃ (hχsmooth : ∀ n, ContDiff ℝ ∞ (χ n)),
      ∃ (hχcompact : ∀ n, HasCompactSupport (χ n)),
      (∀ n ξ, χ n (fun j => -ξ j) = χ n ξ) ∧
      (∀ n ξ j, U n ξ j ≠ 0 → χ n ξ = 1) ∧
      Tendsto (fun n => h3FullThirdRadialRecoveryVelocity244 n (F n))
        atTop (𝓝 target) ∧
      (∀ (n : ℕ) (i : Fin 3),
        (h3FullThirdRadialRecoveryVelocity244 n (F n) i : V3 → ℂ) =ᵐ[volume]
          (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
            𝓕 (h3SchwartzComplexify
              (thirdFullRegularizedPhysicalSchwartzAt244 n (χ n) (U n)
                (hχsmooth n) (hχcompact n) (hUsmooth n)
                (h3AxisOfFin3 i))) ξ)) ∧
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (thirdFullRegularizedPhysicalSchwartzAt244 n (χ n) (U n)
            (hχsmooth n) (hχcompact n) (hUsmooth n) j))
          x (h3FourierAxisDirection j) = 0) ∧
      Tendsto (fun n => h3SpectralVelocityDecodeRealL2
        (h3FullThirdRadialRecoveryVelocity244 n (F n)))
        atTop (𝓝 (h3SpectralVelocityDecodeRealL2 target)) ∧
      CauchySeq (fun n => h3FullThirdRadialRecoveryVelocity244 n (F n)) := by
  classical
  have hCutoff (n : ℕ) :
      ∃ χ : Freq244 → ℝ,
        ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ ξ : Freq244, χ (fun j => -ξ j) = χ ξ) ∧
        (∀ ξ j, U n ξ j ≠ 0 → χ ξ = 1) :=
    exists_thirdFullAxisSupportFlatEvenCutoff244 (U n) (hUcompact n)
  choose χ hχsmooth hχcompact hχeven hχone using hCutoff
  have hCompletion :=
    thirdFullRegularizedPhysicalSchwartzAt_moving_weighted_completion244
      target F hFconverges χ U hχsmooth hχcompact hUsmooth
      hχeven hUherm hUdiv hχone hFweighted
  exact ⟨χ, hχsmooth, hχcompact, hχeven, hχone, hCompletion⟩

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadIntegralBound

/-!
# Automatic weighted moment finiteness for Schwartz triad amplitudes

Coordinate Schwartz decay supplies all polynomial L1 and squared L2
moments of the Euclidean Fourier amplitude. This discharges the analytic
hypotheses of the integral bound without asserting control by H3 alone.
-/

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap

noncomputable section

noncomputable local instance axisFintypeH3TriadSchwartzMoments (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

/-- The vector amplitude squared is the sum of coordinate Fourier norms squared. -/
theorem h3TriadSpectralAmplitude_sq (u : A3 → SchwartzMap V3 ℂ) (p : V3) :
    h3TriadSpectralAmplitude u p ^ 2 = ∑ j, ‖(𝓕 (u j)) p‖ ^ 2 := by
  simp [h3TriadSpectralAmplitude, h3TriadPolarizationNorm,
    PiLp.norm_sq_eq_of_L2, h3SchwartzTriadPolarization]

theorem h3TriadSpectralAmplitude_eq_sqrt (u : A3 → SchwartzMap V3 ℂ) (p : V3) :
    h3TriadSpectralAmplitude u p = Real.sqrt (∑ j, ‖(𝓕 (u j)) p‖ ^ 2) := by
  simp [h3TriadSpectralAmplitude, h3TriadPolarizationNorm,
    PiLp.norm_eq_of_L2, h3SchwartzTriadPolarization]

theorem h3TriadSpectralAmplitude_continuous (u : A3 → SchwartzMap V3 ℂ) :
    Continuous (h3TriadSpectralAmplitude u) := by
  have heq : h3TriadSpectralAmplitude u =
      fun p => Real.sqrt (∑ j, ‖(𝓕 (u j)) p‖ ^ 2) := by
    funext p
    exact h3TriadSpectralAmplitude_eq_sqrt u p
  rw [heq]
  exact (continuous_finset_sum Finset.univ
    (fun j _ => ((𝓕 (u j)).continuous.norm.pow 2))).sqrt

/-- The l1 coordinate sum is an integrable majorant for the Euclidean amplitude. -/
theorem h3TriadSpectralAmplitude_le_sum (u : A3 → SchwartzMap V3 ℂ) (p : V3) :
    h3TriadSpectralAmplitude u p ≤ ∑ j, ‖(𝓕 (u j)) p‖ := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun j : A3 => ‖(𝓕 (u j)) p‖)
    (fun j _ => norm_nonneg _)
  rw [← h3TriadSpectralAmplitude_sq u p] at hs
  have hn := h3TriadSpectralAmplitude_nonneg u p
  have ht : 0 ≤ ∑ j, ‖(𝓕 (u j)) p‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  nlinarith

/-- Every polynomial L1 moment of the Fourier vector amplitude is finite. -/
theorem h3TriadSpectralAmplitude_integrable_pow_mul
    (u : A3 → SchwartzMap V3 ℂ) (n : ℕ) :
    Integrable (fun p => ‖p‖ ^ n * h3TriadSpectralAmplitude u p) := by
  have hi : Integrable (fun p : V3 => ∑ j, ‖p‖ ^ n * ‖(𝓕 (u j)) p‖) :=
    integrable_finsetSum Finset.univ
      (fun j _ => (𝓕 (u j)).integrable_pow_mul volume n)
  apply hi.mono'
    (((continuous_norm.pow n).mul (h3TriadSpectralAmplitude_continuous u)).aestronglyMeasurable)
  filter_upwards with p
  change ‖‖p‖ ^ n * h3TriadSpectralAmplitude u p‖ ≤
    ∑ j, ‖p‖ ^ n * ‖(𝓕 (u j)) p‖
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (h3TriadSpectralAmplitude_nonneg u p)), ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (h3TriadSpectralAmplitude_le_sum u p)
    (pow_nonneg (norm_nonneg _) _)

/-- Every polynomial moment of the amplitude squared is finite. Products of
coordinate Schwartz maps provide the integrable squared-norm terms. -/
theorem h3TriadSpectralAmplitude_integrable_pow_mul_sq
    (u : A3 → SchwartzMap V3 ℂ) (n : ℕ) :
    Integrable (fun p => ‖p‖ ^ n * h3TriadSpectralAmplitude u p ^ 2) := by
  have hj : ∀ j : A3, Integrable (fun p : V3 => ‖p‖ ^ n * ‖(𝓕 (u j)) p‖ ^ 2) := by
    intro j
    let G := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 (u j)) (𝓕 (u j))
    have hi := G.integrable_pow_mul volume n
    change Integrable (fun p : V3 => ‖p‖ ^ n * ‖(𝓕 (u j)) p * (𝓕 (u j)) p‖) at hi
    simpa only [norm_mul, pow_two] using hi
  have hi : Integrable (fun p : V3 => ∑ j, ‖p‖ ^ n * ‖(𝓕 (u j)) p‖ ^ 2) :=
    integrable_finsetSum Finset.univ (fun j _ => hj j)
  apply hi.congr
  filter_upwards with p
  rw [← Finset.mul_sum, h3TriadSpectralAmplitude_sq]

/-- The precise second-order L2 hypothesis used by the shell integral estimate. -/
theorem h3TriadSpectralAmplitude_secondOrder_square_integrable
    (u : A3 → SchwartzMap V3 ℂ) :
    Integrable (fun p => (‖p‖ ^ 2 * h3TriadSpectralAmplitude u p) ^ 2) := by
  apply (h3TriadSpectralAmplitude_integrable_pow_mul_sq u 4).congr
  filter_upwards with p
  ring

/-- The shell integral estimate now needs only Schwartz data and incompressibility;
weighted moment finiteness is derived internally. -/
theorem h3SchwartzTriadShellKernel_integral_norm_le_of_schwartz
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    ‖∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume‖ ≤
      2 * (∫ p, (‖p‖ ^ 2 * h3TriadSpectralAmplitude u p) ^ 2) *
        ∫ q, ‖q‖ ^ 3 * h3TriadSpectralAmplitude u q :=
  h3SchwartzTriadShellKernel_integral_norm_le u hDiv
    (h3TriadSpectralAmplitude_secondOrder_square_integrable u)
    (h3TriadSpectralAmplitude_integrable_pow_mul u 3)

end
end PrimeTensor.Bridge.Euclidean

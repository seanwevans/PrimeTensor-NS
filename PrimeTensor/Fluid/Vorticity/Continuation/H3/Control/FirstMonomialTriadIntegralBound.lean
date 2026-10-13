import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPolarizationBound
import Mathlib.MeasureTheory.Group.Prod

/-!
# An L2-L2-L1 estimate for the first-monomial shell integral

The change (p,r) -> (p,-(p+r)) preserves product volume. An elementary
square inequality separates the three factors. Weighted moment finiteness
is explicit in the Schwartz specialization below.
-/

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped BigOperators

noncomputable section

noncomputable local instance axisFintypeH3TriadIntegralBound (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

private def h3TriadMiddleEquiv : V3 × V3 ≃ᵐ V3 × V3 where
  toFun z := (z.1, -(z.1 + z.2))
  invFun z := (z.1, -(z.1 + z.2))
  left_inv z := by
    apply Prod.ext
    · rfl
    · change -(z.1 + -(z.1 + z.2)) = z.2
      abel
  right_inv z := by
    apply Prod.ext
    · rfl
    · change -(z.1 + -(z.1 + z.2)) = z.2
      abel
  measurable_toFun := by
    change Measurable (fun z : V3 × V3 => (z.1, -(z.1 + z.2)))
    exact measurable_fst.prodMk ((measurable_fst.add measurable_snd).neg)
  measurable_invFun := by
    change Measurable (fun z : V3 × V3 => (z.1, -(z.1 + z.2)))
    exact measurable_fst.prodMk ((measurable_fst.add measurable_snd).neg)

private theorem h3TriadMiddleEquiv_preserving :
    MeasurePreserving h3TriadMiddleEquiv (volume.prod volume) (volume.prod volume) := by
  exact ((MeasurePreserving.id (volume : Measure V3)).prod
    (Measure.measurePreserving_neg (volume : Measure V3))).comp
      (measurePreserving_prod_add (volume : Measure V3) (volume : Measure V3))

/-- A separated product remains integrable after introducing the middle frequency. -/
theorem h3Triad_square_middle_integrable (F H : V3 → ℝ)
    (hF : Integrable (fun p => F p ^ 2)) (hH : Integrable H) :
    Integrable (fun z : V3 × V3 => F z.1 ^ 2 * H (-(z.1 + z.2)))
      (volume.prod volume) := by
  have hi := hF.mul_prod hH
  exact (h3TriadMiddleEquiv_preserving.integrable_comp hi.aestronglyMeasurable).mpr hi

/-- The separated majorant has an exact product integral. -/
theorem h3Triad_square_middle_integral (F H : V3 → ℝ) :
    (∫ z : V3 × V3, F z.1 ^ 2 * H (-(z.1 + z.2)) ∂volume.prod volume) =
      (∫ p, F p ^ 2) * ∫ q, H q := by
  calc
    _ = ∫ z : V3 × V3, F z.1 ^ 2 * H z.2 ∂volume.prod volume :=
      h3TriadMiddleEquiv_preserving.integral_comp
        h3TriadMiddleEquiv.measurableEmbedding (fun z => F z.1 ^ 2 * H z.2)
    _ = _ := integral_prod_mul (μ := (volume : Measure V3))
      (ν := (volume : Measure V3)) (fun p : V3 => F p ^ 2) H

/-- Elementary Young/Cauchy estimate on the momentum plane. The factor two
matches the shell bound; no Fourier normalization constants are included. -/
theorem h3Triad_integral_norm_le_L2_L1
    (K : V3 × V3 → ℂ) (F H : V3 → ℝ)
    (hK : Integrable K (volume.prod volume))
    (hF : Integrable (fun p => F p ^ 2)) (hH : Integrable H)
    (hHnonneg : ∀ q, 0 ≤ H q)
    (hBound : ∀ z, ‖K z‖ ≤ 2 * F z.1 * F z.2 * H (-(z.1 + z.2))) :
    ‖∫ z, K z ∂volume.prod volume‖ ≤
      2 * (∫ p, F p ^ 2) * ∫ q, H q := by
  have hi := h3Triad_square_middle_integrable F H hF hH
  have hj : Integrable (fun z : V3 × V3 => F z.2 ^ 2 * H (-(z.1 + z.2)))
      (volume.prod volume) := by
    have hs := hi.swap
    change Integrable (fun z : V3 × V3 => F z.2 ^ 2 * H (-(z.2 + z.1)))
      (volume.prod volume) at hs
    simpa only [add_comm] using hs
  have hswap :
      (∫ z : V3 × V3, F z.2 ^ 2 * H (-(z.1 + z.2)) ∂volume.prod volume) =
      ∫ z : V3 × V3, F z.1 ^ 2 * H (-(z.1 + z.2)) ∂volume.prod volume := by
    have hs := integral_prod_swap (μ := (volume : Measure V3))
      (ν := (volume : Measure V3))
      (fun z : V3 × V3 => F z.1 ^ 2 * H (-(z.1 + z.2)))
    change (∫ z : V3 × V3, F z.2 ^ 2 * H (-(z.2 + z.1)) ∂volume.prod volume) =
      (∫ z : V3 × V3, F z.1 ^ 2 * H (-(z.1 + z.2)) ∂volume.prod volume) at hs
    simpa only [add_comm] using hs
  calc
    _ ≤ ∫ z, ‖K z‖ ∂volume.prod volume := norm_integral_le_integral_norm K
    _ ≤ ∫ z : V3 × V3,
        F z.1 ^ 2 * H (-(z.1 + z.2)) + F z.2 ^ 2 * H (-(z.1 + z.2))
          ∂volume.prod volume := by
      apply integral_mono hK.norm (hi.add hj)
      intro z
      change ‖K z‖ ≤ F z.1 ^ 2 * H (-(z.1 + z.2)) +
        F z.2 ^ 2 * H (-(z.1 + z.2))
      apply (hBound z).trans
      have hs : 2 * F z.1 * F z.2 ≤ F z.1 ^ 2 + F z.2 ^ 2 := by
        nlinarith [sq_nonneg (F z.1 - F z.2)]
      simpa only [add_mul] using mul_le_mul_of_nonneg_right hs (hHnonneg _)
    _ = (∫ z : V3 × V3, F z.1 ^ 2 * H (-(z.1 + z.2)) ∂volume.prod volume) +
        ∫ z : V3 × V3, F z.2 ^ 2 * H (-(z.1 + z.2)) ∂volume.prod volume :=
      integral_add hi hj
    _ = _ := by rw [hswap, h3Triad_square_middle_integral]; ring

/-- The minimum outer radius pays for the sum of the two outer radii. -/
theorem h3Triad_min_mul_add_le (P R : ℝ) (hP : 0 ≤ P) (hR : 0 ≤ R) :
    min P R * (P + R) ≤ 2 * P * R := by
  rcases le_total P R with h | h
  · rw [min_eq_left h]
    nlinarith [mul_le_mul_of_nonneg_left h hP]
  · rw [min_eq_right h]
    nlinarith [mul_le_mul_of_nonneg_left h hR]

/-- Radial Fourier amplitude in Euclidean complex l2. -/
def h3TriadSpectralAmplitude (u : A3 → SchwartzMap V3 ℂ) (p : V3) : ℝ :=
  h3TriadPolarizationNorm (h3SchwartzTriadPolarization u (WithLp.ofLp p))

theorem h3TriadSpectralAmplitude_nonneg (u : A3 → SchwartzMap V3 ℂ) (p : V3) :
    0 ≤ h3TriadSpectralAmplitude u p := h3TriadPolarizationNorm_nonneg _

/-- Pointwise separation into two second-order factors and one third-order factor. -/
theorem h3SchwartzTriadShellKernel_norm_le_separated
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    ‖h3SchwartzTriadShellKernel u z‖ ≤
      2 * (‖z.1‖ ^ 2 * h3TriadSpectralAmplitude u z.1) *
        (‖z.2‖ ^ 2 * h3TriadSpectralAmplitude u z.2) *
        (‖-(z.1 + z.2)‖ ^ 3 * h3TriadSpectralAmplitude u (-(z.1 + z.2))) := by
  have hm := h3Triad_min_mul_add_le ‖z.1‖ ‖z.2‖ (norm_nonneg _) (norm_nonneg _)
  have ha := h3TriadSpectralAmplitude_nonneg u z.1
  have hb := h3TriadSpectralAmplitude_nonneg u (-(z.1 + z.2))
  have hc := h3TriadSpectralAmplitude_nonneg u z.2
  calc
    _ ≤ (‖z.1‖ * ‖z.2‖ * min ‖z.1‖ ‖z.2‖ * (‖z.1‖ + ‖z.2‖) *
        ‖-(z.1 + z.2)‖ ^ 3) * h3TriadSpectralAmplitude u z.1 *
        h3TriadSpectralAmplitude u (-(z.1 + z.2)) * h3TriadSpectralAmplitude u z.2 :=
      h3SchwartzTriadShellKernel_norm_le_polarization u z (hDiv _)
    _ = (min ‖z.1‖ ‖z.2‖ * (‖z.1‖ + ‖z.2‖)) *
        (‖z.1‖ * ‖z.2‖ * ‖-(z.1 + z.2)‖ ^ 3 * h3TriadSpectralAmplitude u z.1 *
          h3TriadSpectralAmplitude u (-(z.1 + z.2)) * h3TriadSpectralAmplitude u z.2) := by ring
    _ ≤ (2 * ‖z.1‖ * ‖z.2‖) *
        (‖z.1‖ * ‖z.2‖ * ‖-(z.1 + z.2)‖ ^ 3 * h3TriadSpectralAmplitude u z.1 *
          h3TriadSpectralAmplitude u (-(z.1 + z.2)) * h3TriadSpectralAmplitude u z.2) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = _ := by ring

/-- Integrated shell estimate with the weighted moment hypotheses explicit.
The second-order L2 moment and third-order Fourier L1 moment are distinct. -/
theorem h3SchwartzTriadShellKernel_integral_norm_le
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0)
    (hL2 : Integrable (fun p => (‖p‖ ^ 2 * h3TriadSpectralAmplitude u p) ^ 2))
    (hL1 : Integrable (fun q => ‖q‖ ^ 3 * h3TriadSpectralAmplitude u q)) :
    ‖∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume‖ ≤
      2 * (∫ p, (‖p‖ ^ 2 * h3TriadSpectralAmplitude u p) ^ 2) *
        ∫ q, ‖q‖ ^ 3 * h3TriadSpectralAmplitude u q := by
  apply h3Triad_integral_norm_le_L2_L1 _ _ _
    (h3SchwartzTriadShellKernel_integrable u hDiv) hL2 hL1
  · intro q
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (h3TriadSpectralAmplitude_nonneg u q)
  · intro z
    exact h3SchwartzTriadShellKernel_norm_le_separated u z hDiv

end
end PrimeTensor.Bridge.Euclidean

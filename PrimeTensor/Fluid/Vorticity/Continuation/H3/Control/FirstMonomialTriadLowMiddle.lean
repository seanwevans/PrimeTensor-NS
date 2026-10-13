import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadSchwartzMoments

/-!
# A quantitative gain for low-middle-frequency triads

On ||q|| <= eps min(||p||,||r||), q=-(p+r), the shell integral is bounded
by 2 eps^2 times the third-order Fourier energy and first-order Fourier
L1 moment. The complementary frequency region is not estimated here.
-/

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped BigOperators

noncomputable section

noncomputable local instance axisFintypeH3TriadLowMiddle (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

def h3TriadLowMiddleSet (ε : ℝ) : Set (V3 × V3) :=
  {z | ‖-(z.1 + z.2)‖ ≤ ε * min ‖z.1‖ ‖z.2‖}

theorem h3TriadLowMiddleSet_measurable (ε : ℝ) : MeasurableSet (h3TriadLowMiddleSet ε) := by
  have hleft : Continuous (fun z : V3 × V3 => ‖-(z.1 + z.2)‖) :=
    (continuous_fst.add continuous_snd).neg.norm
  have hright : Continuous (fun z : V3 × V3 => ε * min ‖z.1‖ ‖z.2‖) :=
    continuous_const.mul (continuous_fst.norm.min continuous_snd.norm)
  exact (isClosed_le hleft hright).measurableSet

/-- The small-middle restriction contributes two additional powers of eps. -/
theorem h3Triad_lowMiddle_weight_le (P R Q ε : ℝ)
    (hP : 0 ≤ P) (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hε : 0 ≤ ε)
    (hLow : Q ≤ ε * min P R) :
    P ^ 2 * R ^ 2 * Q ^ 3 ≤ ε ^ 2 * P ^ 3 * R ^ 3 * Q := by
  have hp : Q ≤ ε * P := hLow.trans (mul_le_mul_of_nonneg_left (min_le_left P R) hε)
  have hr : Q ≤ ε * R := hLow.trans (mul_le_mul_of_nonneg_left (min_le_right P R) hε)
  have hsq : Q ^ 2 ≤ ε ^ 2 * P * R := by
    have h := mul_le_mul hp hr hQ (mul_nonneg hε hP)
    nlinarith
  calc
    _ = Q ^ 2 * (P ^ 2 * R ^ 2 * Q) := by ring
    _ ≤ (ε ^ 2 * P * R) * (P ^ 2 * R ^ 2 * Q) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = _ := by ring

/-- Restrict the existing shell kernel without changing its sign or phase. -/
def h3SchwartzTriadLowMiddleKernel (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ) : V3 × V3 → ℂ :=
  (h3TriadLowMiddleSet ε).indicator (h3SchwartzTriadShellKernel u)

theorem h3SchwartzTriadLowMiddleKernel_integrable
    (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    Integrable (h3SchwartzTriadLowMiddleKernel u ε) (volume.prod volume) :=
  (h3SchwartzTriadShellKernel_integrable u hDiv).indicator (h3TriadLowMiddleSet_measurable ε)

/-- A pointwise separated bound for the restricted kernel, suitable for the
proved L2-L2-L1 integral inequality. -/
theorem h3SchwartzTriadLowMiddleKernel_norm_le
    (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0)
    (z : V3 × V3) :
    ‖h3SchwartzTriadLowMiddleKernel u ε z‖ ≤
      2 * (‖z.1‖ ^ 3 * h3TriadSpectralAmplitude u z.1) *
        (‖z.2‖ ^ 3 * h3TriadSpectralAmplitude u z.2) *
        (ε ^ 2 * (‖-(z.1 + z.2)‖ * h3TriadSpectralAmplitude u (-(z.1 + z.2)))) := by
  classical
  have ha := h3TriadSpectralAmplitude_nonneg u z.1
  have hb := h3TriadSpectralAmplitude_nonneg u (-(z.1 + z.2))
  have hc := h3TriadSpectralAmplitude_nonneg u z.2
  by_cases hz : z ∈ h3TriadLowMiddleSet ε
  · rw [h3SchwartzTriadLowMiddleKernel, Set.indicator_of_mem hz]
    have hw := h3Triad_lowMiddle_weight_le ‖z.1‖ ‖z.2‖ ‖-(z.1 + z.2)‖ ε
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hε hz
    calc
      _ ≤ 2 * (‖z.1‖ ^ 2 * h3TriadSpectralAmplitude u z.1) *
          (‖z.2‖ ^ 2 * h3TriadSpectralAmplitude u z.2) *
          (‖-(z.1 + z.2)‖ ^ 3 * h3TriadSpectralAmplitude u (-(z.1 + z.2))) :=
        h3SchwartzTriadShellKernel_norm_le_separated u z hDiv
      _ = 2 * ((‖z.1‖ ^ 2 * ‖z.2‖ ^ 2 * ‖-(z.1 + z.2)‖ ^ 3) *
          (h3TriadSpectralAmplitude u z.1 * h3TriadSpectralAmplitude u z.2 *
            h3TriadSpectralAmplitude u (-(z.1 + z.2)))) := by ring
      _ ≤ 2 * ((ε ^ 2 * ‖z.1‖ ^ 3 * ‖z.2‖ ^ 3 * ‖-(z.1 + z.2)‖) *
          (h3TriadSpectralAmplitude u z.1 * h3TriadSpectralAmplitude u z.2 *
            h3TriadSpectralAmplitude u (-(z.1 + z.2)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hw (mul_nonneg (mul_nonneg ha hc) hb)) (by norm_num)
      _ = _ := by ring
  · rw [h3SchwartzTriadLowMiddleKernel, Set.indicator_of_notMem hz, norm_zero]
    positivity

/-- The low-middle shell integral gains eps squared and involves only the
first-order Fourier L1 moment, with moment finiteness derived from Schwartz data. -/
theorem h3SchwartzTriadLowMiddleKernel_integral_norm_le
    (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    ‖∫ z, h3SchwartzTriadLowMiddleKernel u ε z ∂volume.prod volume‖ ≤
      2 * ε ^ 2 * (∫ p, (‖p‖ ^ 3 * h3TriadSpectralAmplitude u p) ^ 2) *
        ∫ q, ‖q‖ * h3TriadSpectralAmplitude u q := by
  have hF : Integrable (fun p => (‖p‖ ^ 3 * h3TriadSpectralAmplitude u p) ^ 2) := by
    apply (h3TriadSpectralAmplitude_integrable_pow_mul_sq u 6).congr
    filter_upwards with p
    ring
  have hH : Integrable (fun q => ‖q‖ * h3TriadSpectralAmplitude u q) := by
    simpa only [pow_one] using h3TriadSpectralAmplitude_integrable_pow_mul u 1
  have h := h3Triad_integral_norm_le_L2_L1
    (h3SchwartzTriadLowMiddleKernel u ε)
    (fun p => ‖p‖ ^ 3 * h3TriadSpectralAmplitude u p)
    (fun q => ε ^ 2 * (‖q‖ * h3TriadSpectralAmplitude u q))
    (h3SchwartzTriadLowMiddleKernel_integrable u ε hDiv) hF (hH.const_mul (ε ^ 2))
    (fun q => mul_nonneg (sq_nonneg ε)
      (mul_nonneg (norm_nonneg q) (h3TriadSpectralAmplitude_nonneg u q)))
    (h3SchwartzTriadLowMiddleKernel_norm_le u ε hε hDiv)
  calc
    _ ≤ 2 * (∫ p, (‖p‖ ^ 3 * h3TriadSpectralAmplitude u p) ^ 2) *
        ∫ q, ε ^ 2 * (‖q‖ * h3TriadSpectralAmplitude u q) := h
    _ = _ := by rw [integral_const_mul]; ring

end
end PrimeTensor.Bridge.Euclidean

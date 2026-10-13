import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowMiddle

/-!
# A linear separation gain for a small outer frequency

When ||p|| <= eps ||r||, the shell integral is controlled by 2 eps E3 M1.
A measure-preserving cyclic change of triad variables places the low outer
frequency in the L1 factor. Swapping p and r gives the other outer region.
-/

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped BigOperators

noncomputable section

noncomputable local instance axisFintypeH3TriadLowOuter (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

private def h3TriadOuterEquiv : V3 × V3 ≃ᵐ V3 × V3 :=
  h3TriadMiddleEquiv.trans (MeasurableEquiv.prodComm : V3 × V3 ≃ᵐ V3 × V3)

private theorem h3TriadOuterEquiv_preserving :
    MeasurePreserving h3TriadOuterEquiv (volume.prod volume) (volume.prod volume) :=
  (Measure.measurePreserving_swap (μ := (volume : Measure V3))
    (ν := (volume : Measure V3))).comp h3TriadMiddleEquiv_preserving

/-- The L1 factor can be assigned to the first outer frequency by a cyclic
change of triad variables. -/
theorem h3Triad_integral_norm_le_outer_L1
    (K : V3 × V3 → ℂ) (F H : V3 → ℝ)
    (hK : Integrable K (volume.prod volume))
    (hF : Integrable (fun p => F p ^ 2)) (hH : Integrable H)
    (hHnonneg : ∀ p, 0 ≤ H p)
    (hBound : ∀ z, ‖K z‖ ≤ 2 * F z.2 * F (-(z.1 + z.2)) * H z.1) :
    ‖∫ z, K z ∂volume.prod volume‖ ≤
      2 * (∫ p, F p ^ 2) * ∫ q, H q := by
  have hi : Integrable (K ∘ h3TriadOuterEquiv) (volume.prod volume) :=
    (h3TriadOuterEquiv_preserving.integrable_comp hK.aestronglyMeasurable).mpr hK
  have hb : ∀ z : V3 × V3, ‖(K ∘ h3TriadOuterEquiv) z‖ ≤
      2 * F z.1 * F (z.2) * H (-(z.1 + z.2)) := by
    intro z
    have h := hBound (h3TriadOuterEquiv z)
    change ‖K (-(z.1 + z.2), z.1)‖ ≤
      2 * F z.1 * F (-(-(z.1 + z.2) + z.1)) * H (-(z.1 + z.2)) at h
    have hq : -(-(z.1 + z.2) + z.1) = z.2 := by abel
    rw [hq] at h
    exact h
  have h := h3Triad_integral_norm_le_L2_L1 (K ∘ h3TriadOuterEquiv) F H hi hF hH hHnonneg hb
  have heq : (∫ z, (K ∘ h3TriadOuterEquiv) z ∂volume.prod volume) =
      ∫ z, K z ∂volume.prod volume :=
    h3TriadOuterEquiv_preserving.integral_comp h3TriadOuterEquiv.measurableEmbedding K
  rw [heq] at h
  exact h

def h3TriadLowLeftSet (ε : ℝ) : Set (V3 × V3) := {z | ‖z.1‖ ≤ ε * ‖z.2‖}

theorem h3TriadLowLeftSet_measurable (ε : ℝ) : MeasurableSet (h3TriadLowLeftSet ε) := by
  have hl : Continuous (fun z : V3 × V3 => ‖z.1‖) := continuous_fst.norm
  have hr : Continuous (fun z : V3 × V3 => ε * ‖z.2‖) := continuous_const.mul continuous_snd.norm
  exact (isClosed_le hl hr).measurableSet

def h3SchwartzTriadLowLeftKernel (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ) : V3 × V3 → ℂ :=
  (h3TriadLowLeftSet ε).indicator (h3SchwartzTriadShellKernel u)

theorem h3SchwartzTriadLowLeftKernel_integrable
    (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    Integrable (h3SchwartzTriadLowLeftKernel u ε) (volume.prod volume) :=
  (h3SchwartzTriadShellKernel_integrable u hDiv).indicator (h3TriadLowLeftSet_measurable ε)

/-- The low outer radius contributes one power of the separation ratio. -/
theorem h3SchwartzTriadLowLeftKernel_norm_le
    (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0)
    (z : V3 × V3) :
    ‖h3SchwartzTriadLowLeftKernel u ε z‖ ≤
      2 * (‖z.2‖ ^ 3 * h3TriadSpectralAmplitude u z.2) *
        (‖-(z.1 + z.2)‖ ^ 3 * h3TriadSpectralAmplitude u (-(z.1 + z.2))) *
        (ε * (‖z.1‖ * h3TriadSpectralAmplitude u z.1)) := by
  classical
  have ha := h3TriadSpectralAmplitude_nonneg u z.1
  have hb := h3TriadSpectralAmplitude_nonneg u (-(z.1 + z.2))
  have hc := h3TriadSpectralAmplitude_nonneg u z.2
  by_cases hz : z ∈ h3TriadLowLeftSet ε
  · rw [h3SchwartzTriadLowLeftKernel, Set.indicator_of_mem hz]
    have hp : ‖z.1‖ ≤ ε * ‖z.2‖ := hz
    have hw : ‖z.1‖ ^ 2 * ‖z.2‖ ^ 2 * ‖-(z.1 + z.2)‖ ^ 3 ≤
        ε * ‖z.1‖ * ‖z.2‖ ^ 3 * ‖-(z.1 + z.2)‖ ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hp
        (show 0 ≤ ‖z.1‖ * ‖z.2‖ ^ 2 * ‖-(z.1 + z.2)‖ ^ 3 by positivity)
      nlinarith
    calc
      _ ≤ 2 * (‖z.1‖ ^ 2 * h3TriadSpectralAmplitude u z.1) *
          (‖z.2‖ ^ 2 * h3TriadSpectralAmplitude u z.2) *
          (‖-(z.1 + z.2)‖ ^ 3 * h3TriadSpectralAmplitude u (-(z.1 + z.2))) :=
        h3SchwartzTriadShellKernel_norm_le_separated u z hDiv
      _ = 2 * ((‖z.1‖ ^ 2 * ‖z.2‖ ^ 2 * ‖-(z.1 + z.2)‖ ^ 3) *
          (h3TriadSpectralAmplitude u z.1 * h3TriadSpectralAmplitude u z.2 *
            h3TriadSpectralAmplitude u (-(z.1 + z.2)))) := by ring
      _ ≤ 2 * ((ε * ‖z.1‖ * ‖z.2‖ ^ 3 * ‖-(z.1 + z.2)‖ ^ 3) *
          (h3TriadSpectralAmplitude u z.1 * h3TriadSpectralAmplitude u z.2 *
            h3TriadSpectralAmplitude u (-(z.1 + z.2)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hw (mul_nonneg (mul_nonneg ha hc) hb)) (by norm_num)
      _ = _ := by ring
  · rw [h3SchwartzTriadLowLeftKernel, Set.indicator_of_notMem hz, norm_zero]
    positivity

/-- The low-left shell contribution has the linear separation gain 2 eps E3 M1. -/
theorem h3SchwartzTriadLowLeftKernel_integral_norm_le
    (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    ‖∫ z, h3SchwartzTriadLowLeftKernel u ε z ∂volume.prod volume‖ ≤
      2 * ε * (∫ p, (‖p‖ ^ 3 * h3TriadSpectralAmplitude u p) ^ 2) *
        ∫ q, ‖q‖ * h3TriadSpectralAmplitude u q := by
  have hF : Integrable (fun p => (‖p‖ ^ 3 * h3TriadSpectralAmplitude u p) ^ 2) := by
    apply (h3TriadSpectralAmplitude_integrable_pow_mul_sq u 6).congr
    filter_upwards with p
    ring
  have hH : Integrable (fun q => ‖q‖ * h3TriadSpectralAmplitude u q) := by
    simpa only [pow_one] using h3TriadSpectralAmplitude_integrable_pow_mul u 1
  have h := h3Triad_integral_norm_le_outer_L1
    (h3SchwartzTriadLowLeftKernel u ε)
    (fun p => ‖p‖ ^ 3 * h3TriadSpectralAmplitude u p)
    (fun q => ε * (‖q‖ * h3TriadSpectralAmplitude u q))
    (h3SchwartzTriadLowLeftKernel_integrable u ε hDiv) hF (hH.const_mul ε)
    (fun q => mul_nonneg hε (mul_nonneg (norm_nonneg q) (h3TriadSpectralAmplitude_nonneg u q)))
    (h3SchwartzTriadLowLeftKernel_norm_le u ε hε hDiv)
  calc
    _ ≤ 2 * (∫ p, (‖p‖ ^ 3 * h3TriadSpectralAmplitude u p) ^ 2) *
        ∫ q, ε * (‖q‖ * h3TriadSpectralAmplitude u q) := h
    _ = _ := by rw [integral_const_mul]; ring

/-- The paired shell kernel is invariant under exchanging the outer frequencies. -/
theorem h3SchwartzTriadShellKernel_swap
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0)
    (z : V3 × V3) : h3SchwartzTriadShellKernel u z.swap = h3SchwartzTriadShellKernel u z := by
  rw [← h3SchwartzTriadKernel_add_swap u hDiv z.swap,
    ← h3SchwartzTriadKernel_add_swap u hDiv z]
  simp only [Prod.swap_swap, add_comm]

/-- Restriction to a small right outer frequency. -/
def h3SchwartzTriadLowRightKernel (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ) (z : V3 × V3) : ℂ :=
  if ‖z.2‖ ≤ ε * ‖z.1‖ then h3SchwartzTriadShellKernel u z else 0

theorem h3SchwartzTriadLowRightKernel_eq_swap
    (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0)
    (z : V3 × V3) :
    h3SchwartzTriadLowRightKernel u ε z = h3SchwartzTriadLowLeftKernel u ε z.swap := by
  classical
  simp [h3SchwartzTriadLowRightKernel, h3SchwartzTriadLowLeftKernel,
    h3TriadLowLeftSet, Set.indicator, h3SchwartzTriadShellKernel_swap u hDiv]

theorem h3SchwartzTriadLowRightKernel_integral_norm_le
    (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    ‖∫ z, h3SchwartzTriadLowRightKernel u ε z ∂volume.prod volume‖ ≤
      2 * ε * (∫ p, (‖p‖ ^ 3 * h3TriadSpectralAmplitude u p) ^ 2) *
        ∫ q, ‖q‖ * h3TriadSpectralAmplitude u q := by
  have heq : h3SchwartzTriadLowRightKernel u ε =
      fun z => h3SchwartzTriadLowLeftKernel u ε z.swap :=
    funext (h3SchwartzTriadLowRightKernel_eq_swap u ε hDiv)
  rw [heq, integral_prod_swap]
  exact h3SchwartzTriadLowLeftKernel_integral_norm_le u ε hε hDiv

end
end PrimeTensor.Bridge.Euclidean

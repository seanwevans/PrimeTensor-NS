import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadShellBound

/-!
# Euclidean polarization bounds for the first-monomial shell kernel

The bilinear complex contraction obeys Cauchy-Schwarz despite having no
conjugation. Incompressibility gives the smaller of the two outer radii in
the mixed contraction. Together these complete the pointwise symbol bound.
-/

namespace PrimeTensor.Bridge.Euclidean

open scoped BigOperators

noncomputable section

noncomputable local instance axisFintypeH3TriadPolarizationBound (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

/-- Euclidean complex l2 norm, not the sup norm on coordinate functions. -/
def h3TriadPolarizationNorm (b : A3 → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 b : EuclideanSpace ℂ A3)‖

theorem h3TriadPolarizationNorm_nonneg (b : A3 → ℂ) :
    0 ≤ h3TriadPolarizationNorm b := norm_nonneg _

private theorem h3Triad_norm_magnitudes (b : A3 → ℂ) :
    ‖(WithLp.toLp 2 (fun i => ‖b i‖) : V3)‖ = h3TriadPolarizationNorm b := by
  simp [h3TriadPolarizationNorm, PiLp.norm_eq_of_L2]

/-- Taking absolute values coordinatewise reduces the bilinear complex
contraction to real Euclidean Cauchy-Schwarz. -/
theorem h3Triad_amplitudeDot_norm_le (a c : A3 → ℂ) :
    ‖FirstMonomialTriad.amplitudeDot a c‖ ≤
      h3TriadPolarizationNorm a * h3TriadPolarizationNorm c := by
  calc
    _ ≤ ∑ i, ‖a i * c i‖ := norm_sum_le _ _
    _ = inner ℝ (WithLp.toLp 2 (fun i => ‖a i‖) : V3)
        (WithLp.toLp 2 (fun i => ‖c i‖) : V3) := by
      simp [PiLp.inner_apply, mul_comm]
    _ ≤ ‖(WithLp.toLp 2 (fun i => ‖a i‖) : V3)‖ *
        ‖(WithLp.toLp 2 (fun i => ‖c i‖) : V3)‖ := real_inner_le_norm _ _
    _ = _ := by rw [h3Triad_norm_magnitudes, h3Triad_norm_magnitudes]

/-- A real frequency embedded in the complex Euclidean carrier preserves norm. -/
theorem h3TriadPolarizationNorm_ofReal (p : V3) :
    h3TriadPolarizationNorm (fun i => (p i : ℂ)) = ‖p‖ := by
  simp [h3TriadPolarizationNorm, PiLp.norm_eq_of_L2, Complex.norm_real]

theorem h3Triad_mixedDot_norm_le (p : V3) (b : A3 → ℂ) :
    ‖FirstMonomialTriad.mixedDot (WithLp.ofLp p) b‖ ≤
      ‖p‖ * h3TriadPolarizationNorm b := by
  simpa only [FirstMonomialTriad.amplitudeDot, FirstMonomialTriad.mixedDot,
    h3TriadPolarizationNorm_ofReal] using
    h3Triad_amplitudeDot_norm_le (fun i => (p i : ℂ)) b

/-- Momentum and incompressibility identify the outer contractions up to sign. -/
theorem h3Triad_mixedDot_eq_neg (p r : V3) (b : A3 → ℂ)
    (hDiv : FirstMonomialTriad.mixedDot (WithLp.ofLp (-(p + r))) b = 0) :
    FirstMonomialTriad.mixedDot (WithLp.ofLp p) b =
      -FirstMonomialTriad.mixedDot (WithLp.ofLp r) b := by
  have hm : FirstMonomialTriad.mixedDot (WithLp.ofLp p) b +
      FirstMonomialTriad.mixedDot (WithLp.ofLp (-(p + r))) b +
      FirstMonomialTriad.mixedDot (WithLp.ofLp r) b = 0 := by
    unfold FirstMonomialTriad.mixedDot
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    change (p i : ℂ) * b i + ((-(p i + r i) : ℝ) : ℂ) * b i +
      (r i : ℂ) * b i = 0
    push_cast
    ring
  rw [hDiv, add_zero] at hm
  exact eq_neg_of_add_eq_zero_left hm

/-- The smaller outer radius controls the mixed contraction. -/
theorem h3Triad_mixedDot_norm_le_min (p r : V3) (b : A3 → ℂ)
    (hDiv : FirstMonomialTriad.mixedDot (WithLp.ofLp (-(p + r))) b = 0) :
    ‖FirstMonomialTriad.mixedDot (WithLp.ofLp p) b‖ ≤
      min ‖p‖ ‖r‖ * h3TriadPolarizationNorm b := by
  have hp := h3Triad_mixedDot_norm_le p b
  have hr : ‖FirstMonomialTriad.mixedDot (WithLp.ofLp p) b‖ ≤
      ‖r‖ * h3TriadPolarizationNorm b := by
    rw [h3Triad_mixedDot_eq_neg p r b hDiv, norm_neg]
    exact h3Triad_mixedDot_norm_le r b
  rcases le_total ‖p‖ ‖r‖ with h | h
  · rw [min_eq_left h]
    exact hp
  · rw [min_eq_right h]
    exact hr

/-- The complete pointwise bound for the actual Schwartz shell kernel.
The three polarization norms correspond to p, q=-(p+r), and r. -/
theorem h3SchwartzTriadShellKernel_norm_le_polarization
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3)
    (hDiv : FirstMonomialTriad.mixedDot (WithLp.ofLp (-(z.1 + z.2)))
      (h3SchwartzTriadPolarization u (WithLp.ofLp (-(z.1 + z.2)))) = 0) :
    ‖h3SchwartzTriadShellKernel u z‖ ≤
      (‖z.1‖ * ‖z.2‖ * min ‖z.1‖ ‖z.2‖ * (‖z.1‖ + ‖z.2‖) *
        ‖-(z.1 + z.2)‖ ^ 3) *
      h3TriadPolarizationNorm (h3SchwartzTriadPolarization u (WithLp.ofLp z.1)) *
      h3TriadPolarizationNorm (h3SchwartzTriadPolarization u (WithLp.ofLp (-(z.1 + z.2)))) *
      h3TriadPolarizationNorm (h3SchwartzTriadPolarization u (WithLp.ofLp z.2)) := by
  let A := h3SchwartzTriadPolarization u (WithLp.ofLp z.1)
  let B := h3SchwartzTriadPolarization u (WithLp.ofLp (-(z.1 + z.2)))
  let C := h3SchwartzTriadPolarization u (WithLp.ofLp z.2)
  have hB := h3Triad_mixedDot_norm_le_min z.1 z.2 B hDiv
  have hAC := h3Triad_amplitudeDot_norm_le A C
  have hBn := h3TriadPolarizationNorm_nonneg B
  calc
    _ ≤ ‖z.1‖ * ‖z.2‖ * ‖FirstMonomialTriad.mixedDot (WithLp.ofLp z.1) B‖ *
        ‖-(z.1 + z.2)‖ ^ 3 * (‖z.1‖ + ‖z.2‖) *
        ‖FirstMonomialTriad.amplitudeDot A C‖ := h3SchwartzTriadShellKernel_norm_le u z
    _ ≤ ‖z.1‖ * ‖z.2‖ * (min ‖z.1‖ ‖z.2‖ * h3TriadPolarizationNorm B) *
        ‖-(z.1 + z.2)‖ ^ 3 * (‖z.1‖ + ‖z.2‖) *
        (h3TriadPolarizationNorm A * h3TriadPolarizationNorm C) := by
      gcongr
    _ = _ := by dsimp [A, B, C]; ring

end
end PrimeTensor.Bridge.Euclidean

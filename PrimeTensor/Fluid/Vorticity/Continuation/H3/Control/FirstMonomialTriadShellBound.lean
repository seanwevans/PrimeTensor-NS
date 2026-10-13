import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPhysicalShell

/-!
# The small-middle-frequency factor in the first-monomial shell kernel

The shell difference is bounded before discarding its geometry. Polarization
contractions remain explicit; this is a pointwise estimate, not an integrated
Sobolev estimate or a continuation theorem.
-/

namespace PrimeTensor.Bridge.Euclidean

open scoped BigOperators

noncomputable section

noncomputable local instance axisFintypeH3TriadShellBound (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

/-- Momentum converts the difference of squared outer radii into a middle
frequency factor. This statement works in any real inner product space. -/
theorem h3Triad_shell_gap_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p r : E) :
    |‖r‖ ^ 2 - ‖p‖ ^ 2| ≤ (‖p‖ + ‖r‖) * ‖-(p + r)‖ := by
  have hgap : ‖r‖ ^ 2 - ‖p‖ ^ 2 = inner ℝ (p - r) (-(p + r)) := by
    simp only [inner_neg_right, inner_sub_left, inner_add_right,
      real_inner_self_eq_norm_sq]
    rw [real_inner_comm r p]
    ring
  rw [hgap]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_sub_le p r) (norm_nonneg _))

/-- On outer frequencies at most N and middle frequency at most L, the
shell gap is at most 2NL. No division or nonzero-frequency assumption. -/
theorem h3Triad_shell_gap_bound_on_scales
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p r : E) {N L : ℝ} (hp : ‖p‖ ≤ N) (hr : ‖r‖ ≤ N)
    (hq : ‖-(p + r)‖ ≤ L) :
    |‖r‖ ^ 2 - ‖p‖ ^ 2| ≤ 2 * N * L := by
  have hN : 0 ≤ N := (norm_nonneg p).trans hp
  calc
    _ ≤ (‖p‖ + ‖r‖) * ‖-(p + r)‖ := h3Triad_shell_gap_bound p r
    _ ≤ (N + N) * L := mul_le_mul (add_le_add hp hr) hq
      (norm_nonneg _) (add_nonneg hN hN)
    _ = _ := by ring

/-- The algebraic dot product agrees with the Euclidean inner product. -/
theorem h3Triad_dot_eq_inner (p r : V3) :
    FirstMonomialTriad.dot (WithLp.ofLp p) (WithLp.ofLp r) = inner ℝ p r := by
  simp only [FirstMonomialTriad.dot, PiLp.inner_apply, Real.inner_apply]

/-- The shell coefficient has three middle-frequency powers after using
momentum. The mixed polarization contraction is deliberately retained. -/
theorem h3Triad_complexShellCoefficient_norm_le (p r : V3) (b : A3 → ℂ) :
    ‖FirstMonomialTriad.complexShellCoefficient
      (WithLp.ofLp p) (WithLp.ofLp (-(p + r))) (WithLp.ofLp r) b‖ ≤
      ‖p‖ * ‖r‖ * ‖FirstMonomialTriad.mixedDot (WithLp.ofLp p) b‖ *
        ‖-(p + r)‖ ^ 3 * (‖p‖ + ‖r‖) := by
  simp only [FirstMonomialTriad.complexShellCoefficient, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, h3Triad_dot_eq_inner,
    real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖-(p + r)‖)]
  calc
    _ ≤ (‖p‖ * ‖r‖) * ‖FirstMonomialTriad.mixedDot (WithLp.ofLp p) b‖ *
        ‖-(p + r)‖ ^ 2 * ((‖p‖ + ‖r‖) * ‖-(p + r)‖) := by
      gcongr
      · exact abs_real_inner_le_norm p r
      · exact h3Triad_shell_gap_bound p r
    _ = _ := by ring

/-- The bound applies to the same shell kernel used in the physical identity.
No divergence assumption is needed to bound the shell expression itself;
divergence is needed when identifying it with the physical aggregate. -/
theorem h3SchwartzTriadShellKernel_norm_le
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) :
    ‖h3SchwartzTriadShellKernel u z‖ ≤
      ‖z.1‖ * ‖z.2‖ *
        ‖FirstMonomialTriad.mixedDot (WithLp.ofLp z.1)
          (h3SchwartzTriadPolarization u (WithLp.ofLp (-(z.1 + z.2))))‖ *
        ‖-(z.1 + z.2)‖ ^ 3 * (‖z.1‖ + ‖z.2‖) *
        ‖FirstMonomialTriad.amplitudeDot
          (h3SchwartzTriadPolarization u (WithLp.ofLp z.1))
          (h3SchwartzTriadPolarization u (WithLp.ofLp z.2))‖ := by
  have hq : FirstMonomialTriad.middleFrequency (WithLp.ofLp z.1) (WithLp.ofLp z.2) =
      WithLp.ofLp (-(z.1 + z.2)) := by
    ext i
    rfl
  unfold h3SchwartzTriadShellKernel FirstMonomialTriad.shellKernel
  rw [hq, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (h3Triad_complexShellCoefficient_norm_le z.1 z.2 _) (norm_nonneg _)

end
end PrimeTensor.Bridge.Euclidean

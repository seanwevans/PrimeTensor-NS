import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowNormal

/-!
# Sharpness audit for the low-frequency normal contribution

An explicit incompressible family has a purely imaginary complete coefficient
of size t²(1+2t)² while its quadratic-separation energy weight is O(t³).
Thus no uniform constant supplies the quadratic bound from incompressibility
and frequency separation alone. This is a pointwise symbol audit, not a
Schwartz-field or Navier-Stokes counterexample.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

def lowNormalAuditP : Fin 3 → ℝ := ![1, 0, 0]
def lowNormalAuditQ (t : ℝ) : Fin 3 → ℝ := ![t, t, 0]
def lowNormalAuditR (t : ℝ) : Fin 3 → ℝ := ![-1-t, -t, 0]
def lowNormalAuditA : Fin 3 → ℂ := ![0, 1, 0]
def lowNormalAuditB : Fin 3 → ℂ := ![0, 0, 1]
def lowNormalAuditC : Fin 3 → ℂ := ![0, 0, Complex.I]

theorem lowNormalAudit_momentum (t : ℝ) :
    ∀ i, lowNormalAuditP i + lowNormalAuditQ t i + lowNormalAuditR t i = 0 := by
  intro i
  fin_cases i <;> simp [lowNormalAuditP, lowNormalAuditQ, lowNormalAuditR] <;> ring

theorem lowNormalAudit_incompressible (t : ℝ) :
    mixedDot lowNormalAuditP lowNormalAuditA = 0 ∧
      mixedDot (lowNormalAuditQ t) lowNormalAuditB = 0 ∧
      mixedDot (lowNormalAuditR t) lowNormalAuditC = 0 := by
  norm_num [mixedDot, lowNormalAuditP, lowNormalAuditQ, lowNormalAuditR,
    lowNormalAuditA, lowNormalAuditB, lowNormalAuditC, Fin.sum_univ_succ]

theorem lowNormalAudit_squared_radii (t : ℝ) :
    dot lowNormalAuditP lowNormalAuditP = 1 ∧
      dot (lowNormalAuditQ t) (lowNormalAuditQ t) = 2*t^2 ∧
      dot (lowNormalAuditR t) (lowNormalAuditR t) = 1+2*t+2*t^2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [dot, lowNormalAuditP, lowNormalAuditQ, lowNormalAuditR,
      Fin.sum_univ_succ] <;> ring

theorem lowNormalAudit_amplitude_norms :
    polarizationNorm lowNormalAuditA = 1 ∧ polarizationNorm lowNormalAuditB = 1 ∧
      polarizationNorm lowNormalAuditC = 1 := by
  norm_num [polarizationNorm, PiLp.norm_eq_of_L2, lowNormalAuditA,
    lowNormalAuditB, lowNormalAuditC, Fin.sum_univ_succ]

set_option maxHeartbeats 800000 in
/-- The complete six-order coefficient retains a quadratic low-frequency term. -/
theorem lowNormalAudit_sixOrder (t : ℝ) :
    sixOrderTriadCoefficient lowNormalAuditP (lowNormalAuditQ t) (lowNormalAuditR t)
      lowNormalAuditA lowNormalAuditB lowNormalAuditC =
      -((t^2 * (1+2*t)^2 : ℝ) : ℂ) * Complex.I := by
  norm_num [sixOrderTriadCoefficient, orderedTriadCoefficient, complexCoefficient,
    dot, mixedDot, amplitudeDot, lowNormalAuditP, lowNormalAuditQ, lowNormalAuditR,
    lowNormalAuditA, lowNormalAuditB, lowNormalAuditC, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 800000 in
/-- The opposite-frequency partner with conjugated amplitudes has the same
coefficient: A and B are real, while conjugation negates the purely imaginary C. -/
theorem lowNormalAudit_reflected_sixOrder (t : ℝ) :
    sixOrderTriadCoefficient (fun i => -lowNormalAuditP i)
      (fun i => -lowNormalAuditQ t i) (fun i => -lowNormalAuditR t i)
      lowNormalAuditA lowNormalAuditB (fun i => -lowNormalAuditC i) =
      -((t^2 * (1+2*t)^2 : ℝ) : ℂ) * Complex.I := by
  norm_num [sixOrderTriadCoefficient, orderedTriadCoefficient, complexCoefficient,
    dot, mixedDot, amplitudeDot, lowNormalAuditP, lowNormalAuditQ, lowNormalAuditR,
    lowNormalAuditA, lowNormalAuditB, lowNormalAuditC, Fin.sum_univ_succ]
  ring

theorem lowNormalAudit_coefficient_norm (t : ℝ) :
    ‖sixOrderTriadCoefficient lowNormalAuditP (lowNormalAuditQ t) (lowNormalAuditR t)
      lowNormalAuditA lowNormalAuditB lowNormalAuditC‖ = t^2 * (1+2*t)^2 := by
  have hnonneg : (0 : ℝ) ≤ t^2 * (1+2*t)^2 :=
    mul_nonneg (sq_nonneg t) (sq_nonneg (1+2*t))
  have hreal : ‖((t^2 * (1+2*t)^2 : ℝ) : ℂ)‖ = t^2 * (1+2*t)^2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (abs_of_nonneg hnonneg)
  rw [lowNormalAudit_sixOrder, norm_mul, norm_neg, hreal, Complex.norm_I, mul_one]

theorem lowNormalAudit_norm_lower (t : ℝ) (ht : 0 ≤ t) :
    t^2 ≤ ‖sixOrderTriadCoefficient lowNormalAuditP (lowNormalAuditQ t) (lowNormalAuditR t)
      lowNormalAuditA lowNormalAuditB lowNormalAuditC‖ := by
  rw [lowNormalAudit_coefficient_norm]
  have h : (1 : ℝ) ≤ (1+2*t)^2 := by nlinarith [sq_nonneg t]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (sq_nonneg t)

/-- The low mode has full normal amplitude, so the additional geometric
smallness condition from the previous patch is absent. -/
theorem lowNormalAudit_normal_amplitudes :
    mixedDot (![0, 0, 1] : Fin 3 → ℝ) lowNormalAuditA = 0 ∧
      mixedDot (![0, 0, 1] : Fin 3 → ℝ) lowNormalAuditB = 1 ∧
      mixedDot (![0, 0, 1] : Fin 3 → ℝ) lowNormalAuditC = Complex.I := by
  norm_num [mixedDot, lowNormalAuditA, lowNormalAuditB, lowNormalAuditC, Fin.sum_univ_succ]

/-- Uniform elementary radius bounds on the family. -/
theorem lowNormalAudit_radius_bounds (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    frequencyNorm lowNormalAuditP = 1 ∧ frequencyNorm (lowNormalAuditQ t) ≤ 2*t ∧
      1 ≤ frequencyNorm (lowNormalAuditR t) ∧ frequencyNorm (lowNormalAuditR t) ≤ 3 := by
  obtain ⟨hp, hq, hr⟩ := lowNormalAudit_squared_radii t
  rw [dot_self_eq_frequencyNorm_sq] at hp hq hr
  have hp0 : 0 ≤ frequencyNorm lowNormalAuditP := norm_nonneg _
  have hq0 : 0 ≤ frequencyNorm (lowNormalAuditQ t) := norm_nonneg _
  have hr0 : 0 ≤ frequencyNorm (lowNormalAuditR t) := norm_nonneg _
  have ht2 : t^2 ≤ 1 := by
    calc
      t^2 ≤ (1 : ℝ)^2 := by gcongr
      _ = 1 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg t]

theorem lowNormalAudit_low_middle (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    frequencyNorm (lowNormalAuditQ t) ≤
      (2*t) * min (frequencyNorm lowNormalAuditP) (frequencyNorm (lowNormalAuditR t)) := by
  obtain ⟨hp, hq, hr, _⟩ := lowNormalAudit_radius_bounds t ht ht1
  rw [hp, min_eq_left hr, mul_one]
  exact hq

/-- The proposed quadratic-separation weight, with epsilon=2t. -/
def lowNormalAuditQuadraticWeight (t : ℝ) : ℝ :=
  (2*t)^2 * frequencyNorm lowNormalAuditP^3 * frequencyNorm (lowNormalAuditR t)^3 *
    frequencyNorm (lowNormalAuditQ t) * polarizationNorm lowNormalAuditA *
    polarizationNorm lowNormalAuditB * polarizationNorm lowNormalAuditC

theorem lowNormalAudit_quadratic_weight_upper (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    lowNormalAuditQuadraticWeight t ≤ 216*t^3 := by
  obtain ⟨hp, hq, _, hr⟩ := lowNormalAudit_radius_bounds t ht ht1
  obtain ⟨ha, hb, hc⟩ := lowNormalAudit_amplitude_norms
  have hq0 : 0 ≤ frequencyNorm (lowNormalAuditQ t) := norm_nonneg _
  have hr0 : 0 ≤ frequencyNorm (lowNormalAuditR t) := norm_nonneg _
  unfold lowNormalAuditQuadraticWeight
  rw [hp, ha, hb, hc]
  calc
    _ ≤ (2*t)^2 * (1 : ℝ)^3 * 3^3 * (2*t) * 1 * 1 * 1 := by gcongr
    _ = _ := by ring

/-- No constant can give the quadratic-separation estimate on this
incompressible low-frequency family without an additional hypothesis. -/
theorem lowNormalAudit_no_uniform_quadratic_bound (K : ℝ) (hK : 0 ≤ K) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      frequencyNorm (lowNormalAuditQ t) ≤
        (2*t) * min (frequencyNorm lowNormalAuditP) (frequencyNorm (lowNormalAuditR t)) ∧
      K * lowNormalAuditQuadraticWeight t <
        ‖sixOrderTriadCoefficient lowNormalAuditP (lowNormalAuditQ t) (lowNormalAuditR t)
          lowNormalAuditA lowNormalAuditB lowNormalAuditC‖ := by
  let t : ℝ := (432*(K+1))⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  have hden : (432 : ℝ)*(K+1) ≠ 0 := by positivity
  have heq : (432*(K+1))*t = 1 := mul_inv_cancel₀ hden
  have hKt : 0 ≤ K*t := mul_nonneg hK ht.le
  have ht1 : t ≤ 1 := by nlinarith [heq]
  have hsmall : K*(216*t) < 1 := by nlinarith [heq]
  refine ⟨t, ht, ht1, lowNormalAudit_low_middle t ht.le ht1, ?_⟩
  calc
    K * lowNormalAuditQuadraticWeight t ≤ K*(216*t^3) :=
      mul_le_mul_of_nonneg_left (lowNormalAudit_quadratic_weight_upper t ht.le ht1) hK
    _ = (K*(216*t))*t^2 := by ring
    _ < t^2 := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hsmall (show 0 < t^2 by positivity)
    _ ≤ _ := lowNormalAudit_norm_lower t ht.le

end
end PrimeTensor.FirstMonomialTriad

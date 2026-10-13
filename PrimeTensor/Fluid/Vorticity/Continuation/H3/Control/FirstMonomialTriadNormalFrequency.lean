import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadNormalBound

/-!
# Frequency separation with tangential and normal amplitudes retained

Momentum gives the smaller outer radius in the tangential contraction and
one middle-frequency power in the shell gap. The resulting radial weight
multiplies one tangential and two normal amplitudes. A low-middle-frequency
channel gains two powers of the separation parameter without discarding
its normal factors.
-/

namespace PrimeTensor.FirstMonomialTriad

open scoped BigOperators

noncomputable section
variable {ι : Type*} [Fintype ι]

private theorem dot_eq_real_inner (p r : ι → ℝ) :
    dot p r = inner ℝ (WithLp.toLp 2 p : EuclideanSpace ℝ ι) (WithLp.toLp 2 r) := by
  simp only [dot, PiLp.inner_apply, Real.inner_apply]

theorem dot_self_eq_frequencyNorm_sq (p : ι → ℝ) :
    dot p p = frequencyNorm p^2 := by
  change dot p p = ‖(WithLp.toLp 2 p : EuclideanSpace ℝ ι)‖^2
  rw [dot_eq_real_inner, real_inner_self_eq_norm_sq]

theorem mixedDot_outer_eq_neg (p q r : ι → ℝ) (b : ι → ℂ)
    (hm : ∀ i, p i + q i + r i = 0) (hb : mixedDot q b = 0) :
    mixedDot p b = -mixedDot r b := by
  have h : mixedDot p b + mixedDot q b + mixedDot r b = 0 := by
    unfold mixedDot
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    calc
      (p i : ℂ) * b i + (q i : ℂ) * b i + (r i : ℂ) * b i =
          ((p i + q i + r i : ℝ) : ℂ) * b i := by push_cast; ring
      _ = 0 := by rw [hm i]; simp
  rw [hb, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Incompressibility bounds the tangential contraction by the smaller
outer radius, without dividing by a frequency. -/
theorem mixedDot_norm_le_min_tangential (p q r n : ι → ℝ) (b : ι → ℂ)
    (hm : ∀ i, p i + q i + r i = 0) (hb : mixedDot q b = 0)
    (hpn : dot p n = 0) (hrn : dot r n = 0) :
    ‖mixedDot p b‖ ≤ min (frequencyNorm p) (frequencyNorm r) *
      polarizationNorm (tangentialPolarization n b) := by
  have hp := mixedDot_norm_le_tangential p n b hpn
  have hr : ‖mixedDot p b‖ ≤ frequencyNorm r *
      polarizationNorm (tangentialPolarization n b) := by
    rw [mixedDot_outer_eq_neg p q r b hm hb, norm_neg]
    exact mixedDot_norm_le_tangential r n b hrn
  rcases le_total (frequencyNorm p) (frequencyNorm r) with h | h
  · rw [min_eq_left h]; exact hp
  · rw [min_eq_right h]; exact hr

theorem shell_gap_le_frequencyNorm (p q r : ι → ℝ)
    (hm : ∀ i, p i + q i + r i = 0) :
    |dot r r - dot p p| ≤ (frequencyNorm p + frequencyNorm r) * frequencyNorm q := by
  have hq : (WithLp.toLp 2 q : EuclideanSpace ℝ ι) =
      -(WithLp.toLp 2 p + WithLp.toLp 2 r) := by
    ext i
    change q i = -(p i + r i)
    have h := hm i
    linarith
  have h := PrimeTensor.Bridge.Euclidean.h3Triad_shell_gap_bound
    (WithLp.toLp 2 p : EuclideanSpace ℝ ι) (WithLp.toLp 2 r)
  rw [← hq] at h
  rw [dot_self_eq_frequencyNorm_sq, dot_self_eq_frequencyNorm_sq]
  exact h

/-- Radial shell weight retaining the smaller outer radius. -/
def separatedNormalShellWeight (p q r : ι → ℝ) : ℝ :=
  frequencyNorm p * frequencyNorm r * min (frequencyNorm p) (frequencyNorm r) *
    (frequencyNorm p + frequencyNorm r) * frequencyNorm q^3

theorem complexShellCoefficient_norm_le_separated_tangential
    (p q r n : ι → ℝ) (b : ι → ℂ)
    (hm : ∀ i, p i + q i + r i = 0) (hb : mixedDot q b = 0)
    (hpn : dot p n = 0) (hrn : dot r n = 0) :
    ‖complexShellCoefficient p q r b‖ ≤
      separatedNormalShellWeight p q r * polarizationNorm (tangentialPolarization n b) := by
  have hmix := mixedDot_norm_le_min_tangential p q r n b hm hb hpn hrn
  have hgap := shell_gap_le_frequencyNorm p q r hm
  have hdot : |dot p r| ≤ frequencyNorm p * frequencyNorm r := by
    rw [dot_eq_real_inner]
    exact abs_real_inner_le_norm _ _
  have hqq : |dot q q| = frequencyNorm q^2 := by
    rw [dot_self_eq_frequencyNorm_sq, abs_of_nonneg (sq_nonneg _)]
  have hp0 : 0 ≤ frequencyNorm p := norm_nonneg _
  have hr0 : 0 ≤ frequencyNorm r := norm_nonneg _
  have hq0 : 0 ≤ frequencyNorm q := norm_nonneg _
  have ht0 : 0 ≤ polarizationNorm (tangentialPolarization n b) := norm_nonneg _
  calc
    _ = |dot p r| * ‖mixedDot p b‖ * frequencyNorm q^2 * |dot r r - dot p p| := by
      simp only [complexShellCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs, hqq]
    _ ≤ (frequencyNorm p * frequencyNorm r) *
        (min (frequencyNorm p) (frequencyNorm r) * polarizationNorm (tangentialPolarization n b)) *
        frequencyNorm q^2 * ((frequencyNorm p + frequencyNorm r) * frequencyNorm q) := by
      gcongr
    _ = _ := by unfold separatedNormalShellWeight; ring

/-- A complete three-channel geometric envelope with frequency separation. -/
def separatedNormalGeometryMajorant (n p q r : ι → ℝ) (a b c : ι → ℂ) : ℝ :=
  separatedNormalShellWeight p q r * polarizationNorm (tangentialPolarization n b) *
    (‖mixedDot n a‖ * ‖mixedDot n c‖) +
  separatedNormalShellWeight p r q * polarizationNorm (tangentialPolarization n c) *
    (‖mixedDot n a‖ * ‖mixedDot n b‖) +
  separatedNormalShellWeight q p r * polarizationNorm (tangentialPolarization n a) *
    (‖mixedDot n b‖ * ‖mixedDot n c‖)

theorem normalShellSum_norm_le_separated_geometry
    (n p q r : ι → ℝ) (a b c : ι → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (ha : mixedDot p a = 0) (hb : mixedDot q b = 0) (hc : mixedDot r c = 0)
    (hpn : dot p n = 0) (hqn : dot q n = 0) (hrn : dot r n = 0) :
    ‖normalShellSum p q r a b c (mixedDot n a) (mixedDot n b) (mixedDot n c)‖ ≤
      separatedNormalGeometryMajorant n p q r a b c := by
  have hm' : ∀ i, p i + r i + q i = 0 := by intro i; have h := hm i; linarith
  have hm'' : ∀ i, q i + p i + r i = 0 := by intro i; have h := hm i; linarith
  have h1 := complexShellCoefficient_norm_le_separated_tangential p q r n b hm hb hpn hrn
  have h2 := complexShellCoefficient_norm_le_separated_tangential p r q n c hm' hc hpn hqn
  have h3 := complexShellCoefficient_norm_le_separated_tangential q p r n a hm'' ha hqn hrn
  unfold normalShellSum separatedNormalGeometryMajorant
  calc
    _ ≤ ‖complexShellCoefficient p q r b * (mixedDot n a * mixedDot n c)‖ +
        ‖complexShellCoefficient p r q c * (mixedDot n a * mixedDot n b)‖ +
        ‖complexShellCoefficient q p r a * (mixedDot n b * mixedDot n c)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by simp only [norm_mul]; gcongr

/-- The low-middle gain applies to its own shell channel while preserving
both normal-amplitude factors in applications. -/
theorem separatedNormalShellWeight_le_low_middle (p q r : ι → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hLow : frequencyNorm q ≤ ε * min (frequencyNorm p) (frequencyNorm r)) :
    separatedNormalShellWeight p q r ≤
      2 * ε^2 * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q := by
  have hp : 0 ≤ frequencyNorm p := norm_nonneg _
  have hq : 0 ≤ frequencyNorm q := norm_nonneg _
  have hr : 0 ≤ frequencyNorm r := norm_nonneg _
  have hmin : min (frequencyNorm p) (frequencyNorm r) *
      (frequencyNorm p + frequencyNorm r) ≤ 2 * frequencyNorm p * frequencyNorm r := by
    rcases le_total (frequencyNorm p) (frequencyNorm r) with h | h
    · rw [min_eq_left h]
      have hh := mul_le_mul_of_nonneg_left h hp
      nlinarith
    · rw [min_eq_right h]
      have hh := mul_le_mul_of_nonneg_left h hr
      nlinarith
  have hw := PrimeTensor.Bridge.Euclidean.h3Triad_lowMiddle_weight_le
    (frequencyNorm p) (frequencyNorm r) (frequencyNorm q) ε hp hr hq hε hLow
  calc
    separatedNormalShellWeight p q r =
      (frequencyNorm p * frequencyNorm r * frequencyNorm q^3) *
        (min (frequencyNorm p) (frequencyNorm r) * (frequencyNorm p + frequencyNorm r)) := by
      unfold separatedNormalShellWeight; ring
    _ ≤ (frequencyNorm p * frequencyNorm r * frequencyNorm q^3) *
        (2 * frequencyNorm p * frequencyNorm r) := by gcongr
    _ = 2 * (frequencyNorm p^2 * frequencyNorm r^2 * frequencyNorm q^3) := by ring
    _ ≤ 2 * (ε^2 * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q) := by gcongr
    _ = _ := by ring

/-- A low-middle shell channel retains its two normal-amplitude factors
while gaining the square of the frequency-separation parameter. -/
theorem normalShellChannel_norm_le_low_middle
    (n p q r : ι → ℝ) (a b c : ι → ℂ) (ε : ℝ)
    (hm : ∀ i, p i + q i + r i = 0) (hb : mixedDot q b = 0)
    (hpn : dot p n = 0) (hrn : dot r n = 0)
    (hε : 0 ≤ ε) (hLow : frequencyNorm q ≤ ε * min (frequencyNorm p) (frequencyNorm r)) :
    ‖complexShellCoefficient p q r b * (mixedDot n a * mixedDot n c)‖ ≤
      (2 * ε^2 * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q) *
        polarizationNorm (tangentialPolarization n b) * (‖mixedDot n a‖ * ‖mixedDot n c‖) := by
  have hs := complexShellCoefficient_norm_le_separated_tangential p q r n b hm hb hpn hrn
  have hw := separatedNormalShellWeight_le_low_middle p q r ε hε hLow
  have ht : 0 ≤ polarizationNorm (tangentialPolarization n b) := norm_nonneg _
  calc
    _ = ‖complexShellCoefficient p q r b‖ * (‖mixedDot n a‖ * ‖mixedDot n c‖) := by
      simp only [norm_mul]
    _ ≤ (separatedNormalShellWeight p q r * polarizationNorm (tangentialPolarization n b)) *
        (‖mixedDot n a‖ * ‖mixedDot n c‖) := by gcongr
    _ ≤ _ := by gcongr

/-- Every incompressible momentum triad has the combined radial and
polarization-geometric bound, including zero frequencies. -/
theorem exists_unit_normal_separated_geometry_bound
    (p q r : Fin 3 → ℝ) (a b c : Fin 3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (ha : mixedDot p a = 0) (hb : mixedDot q b = 0) (hc : mixedDot r c = 0) :
    ∃ n : Fin 3 → ℝ, dot n n = 1 ∧ dot n p = 0 ∧ dot n q = 0 ∧ dot n r = 0 ∧
      ‖sixOrderTriadCoefficient p q r a b c‖ ≤
        separatedNormalGeometryMajorant n p q r a b c := by
  obtain ⟨n, hn, hnp, hnq, hnr, h⟩ :=
    exists_unit_normal_shell_decomposition p q r a b c hm ha hb hc
  refine ⟨n, hn, hnp, hnq, hnr, ?_⟩
  rw [h]
  exact normalShellSum_norm_le_separated_geometry n p q r a b c hm ha hb hc
    (by rwa [dot_comm]) (by rwa [dot_comm]) (by rwa [dot_comm])

end
end PrimeTensor.FirstMonomialTriad

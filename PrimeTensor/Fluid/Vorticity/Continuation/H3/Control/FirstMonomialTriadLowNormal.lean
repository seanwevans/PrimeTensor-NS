import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadNormalFrequency

/-!
# One low frequency across all three normal-shell channels

If q is low relative to both outer frequencies, its middle-frequency channel
has quadratic separation gain. The other two channels have linear gain and
both contain the normal amplitude of b, the polarization at q. This exposes
a sufficient geometric condition for quadratic gain of the complete symbol.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section
variable {ι : Type*} [Fintype ι]

theorem separatedNormalShellWeight_le_product (p q r : ι → ℝ) :
    separatedNormalShellWeight p q r ≤
      2 * frequencyNorm p^2 * frequencyNorm r^2 * frequencyNorm q^3 := by
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
  calc
    separatedNormalShellWeight p q r =
      (frequencyNorm p * frequencyNorm r * frequencyNorm q^3) *
        (min (frequencyNorm p) (frequencyNorm r) * (frequencyNorm p + frequencyNorm r)) := by
      unfold separatedNormalShellWeight; ring
    _ ≤ (frequencyNorm p * frequencyNorm r * frequencyNorm q^3) *
        (2 * frequencyNorm p * frequencyNorm r) := by gcongr
    _ = _ := by ring

theorem separatedNormalShellWeight_outer_swap (p q r : ι → ℝ) :
    separatedNormalShellWeight p q r = separatedNormalShellWeight r q p := by
  unfold separatedNormalShellWeight
  rw [min_comm (frequencyNorm r) (frequencyNorm p)]
  ring

/-- Linear separation gain when the right outer frequency is low. -/
theorem separatedNormalShellWeight_le_low_right (p q r : ι → ℝ) (ε : ℝ)
    (hLow : frequencyNorm r ≤ ε * frequencyNorm p) :
    separatedNormalShellWeight p q r ≤
      2 * ε * frequencyNorm p^3 * frequencyNorm q^3 * frequencyNorm r := by
  have hp : 0 ≤ frequencyNorm p := norm_nonneg _
  have hq : 0 ≤ frequencyNorm q := norm_nonneg _
  have hr : 0 ≤ frequencyNorm r := norm_nonneg _
  calc
    _ ≤ 2 * frequencyNorm p^2 * frequencyNorm r^2 * frequencyNorm q^3 :=
      separatedNormalShellWeight_le_product p q r
    _ = (2 * frequencyNorm p^2 * frequencyNorm r * frequencyNorm q^3) * frequencyNorm r := by ring
    _ ≤ (2 * frequencyNorm p^2 * frequencyNorm r * frequencyNorm q^3) *
        (ε * frequencyNorm p) := mul_le_mul_of_nonneg_left hLow (by positivity)
    _ = _ := by ring

/-- Common-frequency envelope. The linear part is proportional to the
normal amplitude of the low-frequency polarization b. -/
def lowMiddleNormalMajorant (n p q r : ι → ℝ) (a b c : ι → ℂ) (ε : ℝ) : ℝ :=
  (2 * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q) *
    (ε^2 * polarizationNorm (tangentialPolarization n b) * ‖mixedDot n a‖ * ‖mixedDot n c‖ +
      ε * ‖mixedDot n b‖ *
        (polarizationNorm (tangentialPolarization n c) * ‖mixedDot n a‖ +
          polarizationNorm (tangentialPolarization n a) * ‖mixedDot n c‖))

theorem separatedNormalGeometryMajorant_le_low_middle
    (n p q r : ι → ℝ) (a b c : ι → ℂ) (ε : ℝ)
    (hε : 0 ≤ ε) (hLow : frequencyNorm q ≤ ε * min (frequencyNorm p) (frequencyNorm r)) :
    separatedNormalGeometryMajorant n p q r a b c ≤ lowMiddleNormalMajorant n p q r a b c ε := by
  have hqp : frequencyNorm q ≤ ε * frequencyNorm p :=
    hLow.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hε)
  have hqr : frequencyNorm q ≤ ε * frequencyNorm r :=
    hLow.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hε)
  have h1 := separatedNormalShellWeight_le_low_middle p q r ε hε hLow
  have h2 := separatedNormalShellWeight_le_low_right p r q ε hqp
  have h3 : separatedNormalShellWeight q p r ≤
      2 * ε * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q := by
    rw [separatedNormalShellWeight_outer_swap q p r]
    calc
      _ ≤ 2 * ε * frequencyNorm r^3 * frequencyNorm p^3 * frequencyNorm q :=
        separatedNormalShellWeight_le_low_right r p q ε hqr
      _ = _ := by ring
  have hta : 0 ≤ polarizationNorm (tangentialPolarization n a) := norm_nonneg _
  have htb : 0 ≤ polarizationNorm (tangentialPolarization n b) := norm_nonneg _
  have htc : 0 ≤ polarizationNorm (tangentialPolarization n c) := norm_nonneg _
  calc
    separatedNormalGeometryMajorant n p q r a b c ≤
      (2 * ε^2 * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q) *
        polarizationNorm (tangentialPolarization n b) * (‖mixedDot n a‖ * ‖mixedDot n c‖) +
      (2 * ε * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q) *
        polarizationNorm (tangentialPolarization n c) * (‖mixedDot n a‖ * ‖mixedDot n b‖) +
      (2 * ε * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q) *
        polarizationNorm (tangentialPolarization n a) * (‖mixedDot n b‖ * ‖mixedDot n c‖) := by
      unfold separatedNormalGeometryMajorant
      gcongr
    _ = _ := by unfold lowMiddleNormalMajorant; ring

/-- A planar low-frequency amplitude removes both linear-gain channels. -/
theorem lowMiddleNormalMajorant_of_low_planar
    (n p q r : ι → ℝ) (a b c : ι → ℂ) (ε : ℝ) (hb : mixedDot n b = 0) :
    lowMiddleNormalMajorant n p q r a b c ε =
      (2 * ε^2 * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q) *
        polarizationNorm (tangentialPolarization n b) * (‖mixedDot n a‖ * ‖mixedDot n c‖) := by
  simp only [lowMiddleNormalMajorant, hb, norm_zero, mul_zero, zero_mul, add_zero]
  ring

theorem normalAmplitude_norm_le (n : ι → ℝ) (a : ι → ℂ) (hn : dot n n = 1) :
    ‖mixedDot n a‖ ≤ polarizationNorm a := by
  have h := polarizationNorm_tangential_sq n a hn
  have ha : 0 ≤ polarizationNorm a := norm_nonneg _
  nlinarith [norm_nonneg (mixedDot n a),
    sq_nonneg (polarizationNorm (tangentialPolarization n a))]

/-- Only the low-frequency normal amplitude needs an extra epsilon factor
to give quadratic separation gain for the whole three-channel envelope. -/
theorem lowMiddleNormalMajorant_le_quadratic_of_low_normal_small
    (n p q r : ι → ℝ) (a b c : ι → ℂ) (ε : ℝ)
    (hn : dot n n = 1) (hε : 0 ≤ ε)
    (hb : ‖mixedDot n b‖ ≤ ε * polarizationNorm b) :
    lowMiddleNormalMajorant n p q r a b c ε ≤
      6 * ε^2 * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q *
        polarizationNorm a * polarizationNorm b * polarizationNorm c := by
  have hta := polarizationNorm_tangential_le n a hn
  have htb := polarizationNorm_tangential_le n b hn
  have htc := polarizationNorm_tangential_le n c hn
  have hna := normalAmplitude_norm_le n a hn
  have hnc := normalAmplitude_norm_le n c hn
  have hA : 0 ≤ polarizationNorm a := norm_nonneg _
  have hB : 0 ≤ polarizationNorm b := norm_nonneg _
  have hC : 0 ≤ polarizationNorm c := norm_nonneg _
  have htA : 0 ≤ polarizationNorm (tangentialPolarization n a) := norm_nonneg _
  have htB : 0 ≤ polarizationNorm (tangentialPolarization n b) := norm_nonneg _
  have htC : 0 ≤ polarizationNorm (tangentialPolarization n c) := norm_nonneg _
  have hW : 0 ≤ 2 * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q := by
    unfold frequencyNorm; positivity
  calc
    lowMiddleNormalMajorant n p q r a b c ε ≤
      (2 * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q) *
        (ε^2 * polarizationNorm b * polarizationNorm a * polarizationNorm c +
          ε * (ε * polarizationNorm b) *
            (polarizationNorm c * polarizationNorm a + polarizationNorm a * polarizationNorm c)) := by
      unfold lowMiddleNormalMajorant
      gcongr
    _ = _ := by ring

/-- All three channels are controlled on the same low-q region. The final
implication records the additional geometric condition needed for a quadratic
bound on the full coefficient, rather than just its low-middle channel. -/
theorem exists_unit_normal_low_middle_bound
    (p q r : Fin 3 → ℝ) (a b c : Fin 3 → ℂ) (ε : ℝ)
    (hm : ∀ i, p i + q i + r i = 0)
    (ha : mixedDot p a = 0) (hb : mixedDot q b = 0) (hc : mixedDot r c = 0)
    (hε : 0 ≤ ε) (hLow : frequencyNorm q ≤ ε * min (frequencyNorm p) (frequencyNorm r)) :
    ∃ n : Fin 3 → ℝ, dot n n = 1 ∧ dot n p = 0 ∧ dot n q = 0 ∧ dot n r = 0 ∧
      ‖sixOrderTriadCoefficient p q r a b c‖ ≤ lowMiddleNormalMajorant n p q r a b c ε ∧
      (‖mixedDot n b‖ ≤ ε * polarizationNorm b →
        ‖sixOrderTriadCoefficient p q r a b c‖ ≤
          6 * ε^2 * frequencyNorm p^3 * frequencyNorm r^3 * frequencyNorm q *
            polarizationNorm a * polarizationNorm b * polarizationNorm c) := by
  obtain ⟨n, hn, hnp, hnq, hnr, h⟩ :=
    exists_unit_normal_separated_geometry_bound p q r a b c hm ha hb hc
  have hlow := h.trans (separatedNormalGeometryMajorant_le_low_middle n p q r a b c ε hε hLow)
  refine ⟨n, hn, hnp, hnq, hnr, hlow, ?_⟩
  intro hbn
  exact hlow.trans (lowMiddleNormalMajorant_le_quadratic_of_low_normal_small n p q r a b c ε hn hε hbn)

end
end PrimeTensor.FirstMonomialTriad

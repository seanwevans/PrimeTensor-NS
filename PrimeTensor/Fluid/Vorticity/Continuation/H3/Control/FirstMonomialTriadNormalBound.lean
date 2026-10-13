import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadNormalShell

/-!
# Tangential-normal geometry in a quantitative triad bound

Orthogonal projection splits the squared complex Euclidean amplitude into
its tangential energy and squared normal amplitude. The shell contraction
sees only the tangential part. The complete triad bound therefore retains
one tangential amplitude and two normal amplitudes in every channel.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Complex Euclidean amplitude norm. -/
def polarizationNorm (a : ι → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 a : EuclideanSpace ℂ ι)‖

/-- Real Euclidean frequency norm. -/
def frequencyNorm (p : ι → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 p : EuclideanSpace ℝ ι)‖

/-- Subtract the complex amplitude along a real unit normal. -/
def tangentialPolarization (n : ι → ℝ) (a : ι → ℂ) : ι → ℂ :=
  WithLp.ofLp ((WithLp.toLp 2 a : EuclideanSpace ℂ ι) -
    mixedDot n a • WithLp.toLp 2 (fun i => (n i : ℂ)))

theorem mixedDot_eq_complex_inner (p : ι → ℝ) (a : ι → ℂ) :
    mixedDot p a = inner ℂ
      (WithLp.toLp 2 (fun i => (p i : ℂ)) : EuclideanSpace ℂ ι)
      (WithLp.toLp 2 a) := by
  simp [mixedDot, PiLp.inner_apply, mul_comm]

private theorem complex_inner_real_vectors (p n : ι → ℝ) :
    inner ℂ (WithLp.toLp 2 (fun i => (p i : ℂ)) : EuclideanSpace ℂ ι)
      (WithLp.toLp 2 (fun i => (n i : ℂ))) = (dot p n : ℂ) := by
  rw [← mixedDot_eq_complex_inner]
  simp [mixedDot, dot]

theorem mixedDot_tangentialPolarization (p n : ι → ℝ) (a : ι → ℂ) :
    mixedDot p (tangentialPolarization n a) =
      mixedDot p a - mixedDot n a * (dot p n : ℂ) := by
  rw [mixedDot_eq_complex_inner]
  change inner ℂ (WithLp.toLp 2 (fun i => (p i : ℂ)) : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 a - mixedDot n a • WithLp.toLp 2 (fun i => (n i : ℂ))) = _
  rw [inner_sub_right, inner_smul_right, complex_inner_real_vectors,
    ← mixedDot_eq_complex_inner]

/-- Exact Pythagorean identity for complex polarizations and a real unit normal. -/
theorem polarizationNorm_tangential_sq (n : ι → ℝ) (a : ι → ℂ)
    (hn : dot n n = 1) :
    polarizationNorm (tangentialPolarization n a)^2 + ‖mixedDot n a‖^2 =
      polarizationNorm a^2 := by
  let N : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => (n i : ℂ))
  let A : EuclideanSpace ℂ ι := WithLp.toLp 2 a
  let T : EuclideanSpace ℂ ι := A - mixedDot n a • N
  have hNN : inner ℂ N N = 1 := by
    change inner ℂ (WithLp.toLp 2 (fun i => (n i : ℂ)) : EuclideanSpace ℂ ι)
      (WithLp.toLp 2 (fun i => (n i : ℂ))) = 1
    rw [complex_inner_real_vectors, hn]
    norm_num
  have hN : ‖N‖ = 1 := by
    have hs : ‖N‖^2 = 1 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), hNN]
      rfl
    nlinarith [norm_nonneg N]
  have hNT : inner ℂ N T = 0 := by
    change inner ℂ (WithLp.toLp 2 (fun i => (n i : ℂ)) : EuclideanSpace ℂ ι)
      (WithLp.toLp 2 (tangentialPolarization n a)) = 0
    rw [← mixedDot_eq_complex_inner, mixedDot_tangentialPolarization, hn]
    simp
  have horth : inner ℂ (mixedDot n a • N) T = 0 := by
    rw [inner_smul_left, hNT, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (mixedDot n a • N) T horth
  have hsum : mixedDot n a • N + T = A := by dsimp [T]; abel
  rw [hsum, norm_smul, hN, mul_one] at h
  change polarizationNorm a * polarizationNorm a =
    ‖mixedDot n a‖ * ‖mixedDot n a‖ +
      polarizationNorm (tangentialPolarization n a) *
        polarizationNorm (tangentialPolarization n a) at h
  nlinarith

/-- Removing the normal component cannot increase Euclidean amplitude. -/
theorem polarizationNorm_tangential_le (n : ι → ℝ) (a : ι → ℂ)
    (hn : dot n n = 1) :
    polarizationNorm (tangentialPolarization n a) ≤ polarizationNorm a := by
  have h := polarizationNorm_tangential_sq n a hn
  have ha : 0 ≤ polarizationNorm a := norm_nonneg _
  have ht : 0 ≤ polarizationNorm (tangentialPolarization n a) := norm_nonneg _
  nlinarith [sq_nonneg ‖mixedDot n a‖]

theorem mixedDot_norm_le_euclidean (p : ι → ℝ) (a : ι → ℂ) :
    ‖mixedDot p a‖ ≤ frequencyNorm p * polarizationNorm a := by
  rw [mixedDot_eq_complex_inner]
  have h := norm_inner_le_norm (𝕜 := ℂ)
    (WithLp.toLp 2 (fun i => (p i : ℂ)) : EuclideanSpace ℂ ι) (WithLp.toLp 2 a)
  have hp : ‖(WithLp.toLp 2 (fun i => (p i : ℂ)) : EuclideanSpace ℂ ι)‖ =
      frequencyNorm p := by
    simp [frequencyNorm, PiLp.norm_eq_of_L2, Complex.norm_real]
  simpa only [hp, polarizationNorm] using h

/-- A planar frequency sees only the tangential amplitude. -/
theorem mixedDot_norm_le_tangential (p n : ι → ℝ) (a : ι → ℂ)
    (hpn : dot p n = 0) :
    ‖mixedDot p a‖ ≤ frequencyNorm p * polarizationNorm (tangentialPolarization n a) := by
  have h := mixedDot_norm_le_euclidean p (tangentialPolarization n a)
  simpa only [mixedDot_tangentialPolarization, hpn, Complex.ofReal_zero,
    mul_zero, sub_zero] using h

/-- Exact scalar shell weight after bounding only the mixed contraction. -/
def normalShellWeight (p q r : ι → ℝ) : ℝ :=
  |dot p r| * frequencyNorm p * |dot q q| * |dot r r - dot p p|

theorem complexShellCoefficient_norm_le_tangential (p q r n : ι → ℝ)
    (b : ι → ℂ) (hpn : dot p n = 0) :
    ‖complexShellCoefficient p q r b‖ ≤
      normalShellWeight p q r * polarizationNorm (tangentialPolarization n b) := by
  have h := mixedDot_norm_le_tangential p n b hpn
  calc
    _ = |dot p r| * ‖mixedDot p b‖ * |dot q q| * |dot r r - dot p p| := by
      simp only [complexShellCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |dot p r| * (frequencyNorm p * polarizationNorm (tangentialPolarization n b)) *
        |dot q q| * |dot r r - dot p p| := by gcongr
    _ = _ := by unfold normalShellWeight; ring

/-- The three channels retain one tangential and two normal amplitudes each. -/
def normalGeometryMajorant (n p q r : ι → ℝ) (a b c : ι → ℂ) : ℝ :=
  normalShellWeight p q r * polarizationNorm (tangentialPolarization n b) *
    (‖mixedDot n a‖ * ‖mixedDot n c‖) +
  normalShellWeight p r q * polarizationNorm (tangentialPolarization n c) *
    (‖mixedDot n a‖ * ‖mixedDot n b‖) +
  normalShellWeight q p r * polarizationNorm (tangentialPolarization n a) *
    (‖mixedDot n b‖ * ‖mixedDot n c‖)

theorem normalShellSum_norm_le_geometry (n p q r : ι → ℝ) (a b c : ι → ℂ)
    (hpn : dot p n = 0) (hqn : dot q n = 0) :
    ‖normalShellSum p q r a b c (mixedDot n a) (mixedDot n b) (mixedDot n c)‖ ≤
      normalGeometryMajorant n p q r a b c := by
  have h1 := complexShellCoefficient_norm_le_tangential p q r n b hpn
  have h2 := complexShellCoefficient_norm_le_tangential p r q n c hpn
  have h3 := complexShellCoefficient_norm_le_tangential q p r n a hqn
  unfold normalShellSum normalGeometryMajorant
  calc
    _ ≤ ‖complexShellCoefficient p q r b * (mixedDot n a * mixedDot n c)‖ +
        ‖complexShellCoefficient p r q c * (mixedDot n a * mixedDot n b)‖ +
        ‖complexShellCoefficient q p r a * (mixedDot n b * mixedDot n c)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by simp only [norm_mul]; gcongr

/-- Nearly planar amplitudes give a quadratic normal-fraction gain. The
smallness assumptions are explicit and are not inferred from incompressibility. -/
theorem normalGeometryMajorant_le_of_normal_small
    (n p q r : ι → ℝ) (a b c : ι → ℂ) (ε : ℝ)
    (hn : dot n n = 1) (hε : 0 ≤ ε)
    (ha : ‖mixedDot n a‖ ≤ ε * polarizationNorm a)
    (hb : ‖mixedDot n b‖ ≤ ε * polarizationNorm b)
    (hc : ‖mixedDot n c‖ ≤ ε * polarizationNorm c) :
    normalGeometryMajorant n p q r a b c ≤
      ε^2 * (normalShellWeight p q r + normalShellWeight p r q + normalShellWeight q p r) *
        polarizationNorm a * polarizationNorm b * polarizationNorm c := by
  have hta := polarizationNorm_tangential_le n a hn
  have htb := polarizationNorm_tangential_le n b hn
  have htc := polarizationNorm_tangential_le n c hn
  have hwa : 0 ≤ normalShellWeight p q r := by
    unfold normalShellWeight frequencyNorm; positivity
  have hwb : 0 ≤ normalShellWeight p r q := by
    unfold normalShellWeight frequencyNorm; positivity
  have hwc : 0 ≤ normalShellWeight q p r := by
    unfold normalShellWeight frequencyNorm; positivity
  have hna : 0 ≤ polarizationNorm a := norm_nonneg _
  have hnb : 0 ≤ polarizationNorm b := norm_nonneg _
  have hnc : 0 ≤ polarizationNorm c := norm_nonneg _
  have hnta : 0 ≤ polarizationNorm (tangentialPolarization n a) := norm_nonneg _
  have hntb : 0 ≤ polarizationNorm (tangentialPolarization n b) := norm_nonneg _
  have hntc : 0 ≤ polarizationNorm (tangentialPolarization n c) := norm_nonneg _
  calc
    normalGeometryMajorant n p q r a b c ≤
      normalShellWeight p q r * polarizationNorm b *
          ((ε * polarizationNorm a) * (ε * polarizationNorm c)) +
      normalShellWeight p r q * polarizationNorm c *
          ((ε * polarizationNorm a) * (ε * polarizationNorm b)) +
      normalShellWeight q p r * polarizationNorm a *
          ((ε * polarizationNorm b) * (ε * polarizationNorm c)) := by
      unfold normalGeometryMajorant
      gcongr
    _ = _ := by ring

/-- Every incompressible momentum triad admits the quantitative intrinsic
normal/tangential bound, including degenerate frequencies. -/
theorem exists_unit_normal_geometry_bound (p q r : Fin 3 → ℝ) (a b c : Fin 3 → ℂ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (ha : mixedDot p a = 0) (hb : mixedDot q b = 0) (hc : mixedDot r c = 0) :
    ∃ n : Fin 3 → ℝ, dot n n = 1 ∧ dot n p = 0 ∧ dot n q = 0 ∧ dot n r = 0 ∧
      ‖sixOrderTriadCoefficient p q r a b c‖ ≤ normalGeometryMajorant n p q r a b c := by
  obtain ⟨n, hn, hnp, hnq, hnr, h⟩ :=
    exists_unit_normal_shell_decomposition p q r a b c hMomentum ha hb hc
  refine ⟨n, hn, hnp, hnq, hnr, ?_⟩
  rw [h]
  exact normalShellSum_norm_le_geometry n p q r a b c
    (by rwa [dot_comm]) (by rwa [dot_comm])

end
end PrimeTensor.FirstMonomialTriad

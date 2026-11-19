import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3ConstructedSolenoidalLocalExistence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic

/-!
# Hermitian Fourier reflection: real-data geometry and Galerkin limit closure

The integer-frequency reality constraint is u(-n)=conj(u(n)) componentwise.
This module defines the actual complex-conjugation involution on the
Euclidean Fourier three-vector, establishes its real-linearity, isometry and
continuity, and proves parity of the genuine Z3 spectral degree, Wiener weight,
and the canonical Galerkin cubes. The Hermitian average of an arbitrary
Fourier field is Hermitian, with an explicit pointwise norm estimate.

For a symmetric finite cutoff the honest zero-extension of a Hermitian
finite state is Hermitian at EVERY lattice mode, including absent modes.
Finally, uniform-mode convergence of Hermitian finite Fourier fields
propagates Hermitian symmetry to the infinite limit without an infinite-time
ODE differentiability assumption.

The *remaining* nonlinear theorem is conjugate-reflection equivariance of
the output Leray projector and the complete ordered quadratic field. Only
once that and finite-ODE uniqueness are supplied does this imply that the
constructed solenoidal Fourier flow is real-valued. No global-regularity or
physical R3 continuation assertion is made here.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev HrIndex244 := thirdFullThreeBandZ3Index244
private abbrev HrBand244 := EuclideanSpace ℂ (Fin 3)

/-- Componentwise complex conjugation of a genuine complex Fourier velocity.
The scalar map is Mathlib's real-linear isometry, not a missing
`Complex.conj` namespace constant. -/
def thirdFullThreeBandZ3BandConj244 (v : HrBand244) : HrBand244 :=
  WithLp.toLp 2 (fun j : Fin 3 => Complex.conjLIE (v j))

@[simp] theorem thirdFullThreeBand_z3BandConj_apply244
    (v : HrBand244) (j : Fin 3) :
    thirdFullThreeBandZ3BandConj244 v j = Complex.conjLIE (v j) := rfl

/-- The real structure is involutive, with no imaginary-phase choices. -/
theorem thirdFullThreeBand_z3BandConj_involutive244 (v : HrBand244) :
    thirdFullThreeBandZ3BandConj244 (thirdFullThreeBandZ3BandConj244 v) = v := by
  ext j
  simp [thirdFullThreeBand_z3BandConj_apply244]

/-- Conjugation commutes with addition of complex Fourier velocity vectors. -/
theorem thirdFullThreeBand_z3BandConj_add244 (v w : HrBand244) :
    thirdFullThreeBandZ3BandConj244 (v + w) =
      thirdFullThreeBandZ3BandConj244 v + thirdFullThreeBandZ3BandConj244 w := by
  ext j
  simp [thirdFullThreeBand_z3BandConj_apply244]

/-- Conjugation is linear over REAL time-dependent multipliers. -/
theorem thirdFullThreeBand_z3BandConj_realSmul244
    (r : ℝ) (v : HrBand244) :
    thirdFullThreeBandZ3BandConj244 (r • v) =
      r • thirdFullThreeBandZ3BandConj244 v := by
  ext j
  simp [thirdFullThreeBand_z3BandConj_apply244]

@[simp] theorem thirdFullThreeBand_z3BandConj_zero244 :
    thirdFullThreeBandZ3BandConj244 (0 : HrBand244) = 0 := by
  ext j
  simp [thirdFullThreeBand_z3BandConj_apply244]

/-- The Fourier reality involution is an isometry in the ACTUAL Euclidean norm. -/
theorem thirdFullThreeBand_z3BandConj_norm244 (v : HrBand244) :
    ‖thirdFullThreeBandZ3BandConj244 v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [thirdFullThreeBand_z3BandConj_apply244,
    Complex.conjLIE_apply, Complex.norm_conj]

/-- Continuity of the Fourier conjugation, used in the actual limit argument. -/
theorem thirdFullThreeBand_z3BandConj_continuous244 :
    Continuous (thirdFullThreeBandZ3BandConj244 : HrBand244 → HrBand244) := by
  have hComponent (j : Fin 3) :
      Continuous (fun v : HrBand244 => Complex.conjLIE (v j)) :=
    Complex.conjLIE.continuous.comp
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j)
  have hPi : Continuous (fun v : HrBand244 =>
      fun j : Fin 3 => Complex.conjLIE (v j)) :=
    continuous_pi hComponent
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp hPi

/-- Exact reflection of integer-frequency embedding into complex Euclidean space. -/
theorem thirdFullThreeBand_z3ComplexFrequency_neg244 (n : HrIndex244) :
    thirdFullThreeBandZ3ComplexFrequency244 (-n) =
      -thirdFullThreeBandZ3ComplexFrequency244 n := by
  ext j
  simp [thirdFullThreeBandZ3ComplexFrequency244]

/-- The physical Laplacian Fourier multiplier is even under n -> -n. -/
theorem thirdFullThreeBand_z3ComplexFrequency_norm_neg244 (n : HrIndex244) :
    ‖thirdFullThreeBandZ3ComplexFrequency244 (-n)‖ =
      ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ := by
  rw [thirdFullThreeBand_z3ComplexFrequency_neg244, norm_neg]

/-- The genuine lattice l1 degree is reflection invariant. -/
theorem thirdFullThreeBand_z3Degree_neg244 (n : HrIndex244) :
    thirdFullThreeBandZ3Degree244 (-n) = thirdFullThreeBandZ3Degree244 n := by
  simp [thirdFullThreeBandZ3Degree244]

/-- Hence EVERY analytic Wiener weight is reflection invariant. -/
theorem thirdFullThreeBand_z3Weight_neg244 (r : ℝ) (n : HrIndex244) :
    thirdFullThreeBandZ3Weight244 r (-n) =
      thirdFullThreeBandZ3Weight244 r n := by
  simp [thirdFullThreeBandZ3Weight244, thirdFullThreeBand_z3Degree_neg244]

/-- The precise Fourier reality condition for a velocity snapshot. -/
def thirdFullThreeBandZ3FourierHermitian244
    (u : HrIndex244 → HrBand244) : Prop :=
  ∀ n, u (-n) = thirdFullThreeBandZ3BandConj244 (u n)

/-- Hermitian reflection is itself an involution on whole Fourier fields. -/
def thirdFullThreeBandZ3HermitianReflect244
    (u : HrIndex244 → HrBand244) (n : HrIndex244) : HrBand244 :=
  thirdFullThreeBandZ3BandConj244 (u (-n))

theorem thirdFullThreeBand_z3HermitianReflect_involutive244
    (u : HrIndex244 → HrBand244) :
    thirdFullThreeBandZ3HermitianReflect244
        (thirdFullThreeBandZ3HermitianReflect244 u) = u := by
  funext n
  simp only [thirdFullThreeBandZ3HermitianReflect244, neg_neg,
    thirdFullThreeBand_z3BandConj_involutive244]

/-- Canonical Hermitian average of an arbitrary complex Fourier field. -/
def thirdFullThreeBandZ3HermitianAverage244
    (u : HrIndex244 → HrBand244) (n : HrIndex244) : HrBand244 :=
  (1 / 2 : ℝ) • (u n + thirdFullThreeBandZ3HermitianReflect244 u n)

/-- The Hermitian average satisfies the reality identity EXACTLY. -/
theorem thirdFullThreeBand_z3HermitianAverage_reality244
    (u : HrIndex244 → HrBand244) :
    thirdFullThreeBandZ3FourierHermitian244
      (thirdFullThreeBandZ3HermitianAverage244 u) := by
  intro n
  change (1 / 2 : ℝ) •
      (u (-n) + thirdFullThreeBandZ3BandConj244 (u (-(-n)))) =
    thirdFullThreeBandZ3BandConj244
      ((1 / 2 : ℝ) •
        (u n + thirdFullThreeBandZ3BandConj244 (u (-n))))
  simp only [neg_neg, thirdFullThreeBand_z3BandConj_realSmul244,
    thirdFullThreeBand_z3BandConj_add244,
    thirdFullThreeBand_z3BandConj_involutive244]
  rw [add_comm]

/-- Quantitative pointwise cost of enforcing real Fourier symmetry:
no frequency factor or derivative loss is introduced by conjugation. -/
theorem thirdFullThreeBand_z3HermitianAverage_norm244
    (u : HrIndex244 → HrBand244) (n : HrIndex244) :
    ‖thirdFullThreeBandZ3HermitianAverage244 u n‖ ≤
      (‖u n‖ + ‖u (-n)‖) / 2 := by
  change ‖(1 / 2 : ℝ) • (u n +
      thirdFullThreeBandZ3BandConj244 (u (-n)))‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) * ‖u n + thirdFullThreeBandZ3BandConj244 (u (-n))‖ ≤
      (1 / 2 : ℝ) * (‖u n‖ + ‖thirdFullThreeBandZ3BandConj244 (u (-n))‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (‖u n‖ + ‖u (-n)‖) / 2 := by
      rw [thirdFullThreeBand_z3BandConj_norm244]
      ring

/-- The standard finite integer Fourier cubes are genuinely symmetric. -/
theorem thirdFullThreeBand_z3FixedCoreCube_neg244
    (N : ℕ) (n : HrIndex244)
    (hn : n ∈ thirdFullThreeBandZ3GalerkinFixedCoreCube244 N) :
    -n ∈ thirdFullThreeBandZ3GalerkinFixedCoreCube244 N := by
  classical
  unfold thirdFullThreeBandZ3GalerkinFixedCoreCube244 at hn ⊢
  rw [Fintype.mem_piFinset] at hn ⊢
  intro j
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp (hn j)
  apply Finset.mem_Icc.mpr
  constructor
  · simpa using (neg_le_neg hu)
  · simpa using (neg_le_neg hl)

/-- The zero-extension of a Hermitian finite state on a symmetric support
is Hermitian at ALL frequencies, not just the retained ones. -/
theorem thirdFullThreeBand_z3FiniteExtend_Hermitian244
    (s : Finset HrIndex244)
    (hs : ∀ n : HrIndex244, n ∈ s → -n ∈ s)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hx : ∀ n (hn : n ∈ s),
      x ⟨-n, hs n hn⟩ = thirdFullThreeBandZ3BandConj244 (x ⟨n, hn⟩)) :
    thirdFullThreeBandZ3FourierHermitian244
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) := by
  intro n
  by_cases hn : n ∈ s
  · rw [thirdFullThreeBand_z3GalerkinFiniteExtend_on244 s x (-n) (hs n hn),
      thirdFullThreeBand_z3GalerkinFiniteExtend_on244 s x n hn]
    exact hx n hn
  · have hneg : -n ∉ s := by
      intro hneg
      have hnn : -(-n) ∈ s := hs (-n) hneg
      exact hn (by simpa using hnn)
    rw [thirdFullThreeBand_z3GalerkinFiniteExtend_off244 s x n hn,
      thirdFullThreeBand_z3GalerkinFiniteExtend_off244 s x (-n) hneg,
      thirdFullThreeBand_z3BandConj_zero244]

/-- Restricting one Hermitian infinite initial field to a symmetric finite
Galerkin support produces EXACTLY Hermitian retained coordinates. -/
theorem thirdFullThreeBand_z3Hermitian_initialRestriction244
    (s : Finset HrIndex244)
    (hs : ∀ n : HrIndex244, n ∈ s → -n ∈ s)
    (u0 : HrIndex244 → HrBand244)
    (hu0 : thirdFullThreeBandZ3FourierHermitian244 u0)
    (n : HrIndex244) (hn : n ∈ s) :
    (fun j : {m : HrIndex244 // m ∈ s} => u0 j.1) ⟨-n, hs n hn⟩ =
      thirdFullThreeBandZ3BandConj244
        ((fun j : {m : HrIndex244 // m ∈ s} => u0 j.1) ⟨n, hn⟩) := by
  exact hu0 n

/-- Hermitian Fourier symmetry survives uniform-in-time mode convergence;
no infinite-dimensional ODE derivative is required. The approximating
fields may be the actual zero-extended Galerkin trajectories. -/
theorem thirdFullThreeBand_z3Hermitian_uniformLimit244
    (a b : ℝ)
    (u : ℕ → ℝ → HrIndex244 → HrBand244)
    (g : ℝ → HrIndex244 → HrBand244)
    (hFinite : ∀ k, ∀ t ∈ Icc a b,
      thirdFullThreeBandZ3FourierHermitian244 (u k t))
    (hUniform : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc a b,
        dist (u k t n) (g t n) < epsilon) :
    ∀ t ∈ Icc a b, thirdFullThreeBandZ3FourierHermitian244 (g t) := by
  intro t ht n
  have hMode (j : HrIndex244) :
      Tendsto (fun k : ℕ => u k t j) atTop (nhds (g t j)) := by
    apply Metric.tendsto_atTop.mpr
    intro epsilon hEpsilon
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hUniform j epsilon hEpsilon)
    exact ⟨K, fun k hk => hK k hk t ht⟩
  have hMirror : (fun k : ℕ => u k t (-n)) =
      (fun k : ℕ => thirdFullThreeBandZ3BandConj244 (u k t n)) := by
    funext k
    exact hFinite k t ht n
  have hTarget : Tendsto
      (fun k : ℕ => thirdFullThreeBandZ3BandConj244 (u k t n))
      atTop (nhds (g t (-n))) := by
    rw [← hMirror]
    exact hMode (-n)
  have hConj : Tendsto
      (fun k : ℕ => thirdFullThreeBandZ3BandConj244 (u k t n))
      atTop (nhds (thirdFullThreeBandZ3BandConj244 (g t n))) :=
    ((thirdFullThreeBand_z3BandConj_continuous244).tendsto (g t n)).comp (hMode n)
  exact tendsto_nhds_unique hTarget hConj

/-- Apply Hermitian closedness to an actual family of finite Galerkin
states; finite symmetry is stated on retained coordinates and transferred
to the zero-extension without assuming the infinite constraint. -/
theorem thirdFullThreeBand_z3GalerkinHermitian_uniformLimit244
    (a b : ℝ)
    (s : ℕ → Finset HrIndex244)
    (hs : ∀ k (n : HrIndex244), n ∈ s k → -n ∈ s k)
    (gamma : (k : ℕ) → ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 (s k))
    (g : ℝ → HrIndex244 → HrBand244)
    (hFinite : ∀ k, ∀ t ∈ Icc a b, ∀ n (hn : n ∈ s k),
      gamma k t ⟨-n, hs k n hn⟩ =
        thirdFullThreeBandZ3BandConj244 (gamma k t ⟨n, hn⟩))
    (hUniform : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc a b,
        dist (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (gamma k t) n)
          (g t n) < epsilon) :
    ∀ t ∈ Icc a b, thirdFullThreeBandZ3FourierHermitian244 (g t) := by
  apply thirdFullThreeBand_z3Hermitian_uniformLimit244 a b
    (fun k t n => thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (gamma k t) n)
    g
  · intro k t ht
    exact thirdFullThreeBand_z3FiniteExtend_Hermitian244 (s k)
      (hs k) (gamma k t) (hFinite k t ht)
  · exact hUniform

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinArzelaDiagonal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
# Actual Galerkin Fourier diagonal converges in the lower-radius Wiener Cauchy metric

The proved Arzelà--Ascoli/Tychonoff theorem gives one subsequence converging
uniformly in time at every Fourier frequency. The previous fixed-core inequality
then upgrades convergence of the finitely many modes inside a fixed cube to
UNIFORM-IN-TIME Cauchy convergence in W_log(3/2), across unrelated cutoffs.

The analytic reserve log(9/5)-log(3/2) yields the exact geometric tail
200*(5/6)^N. We choose the Fourier core BEFORE choosing the Cauchy time index;
thus neither cutoff cardinality nor a mode-dependent time threshold survives.

The final theorem constructs the Galerkin trajectories and the common subsequence
from arbitrary cutoff-indexed initial states obeying a strict W_log(2)<100 bound.
It proves the strong Wiener Cauchy property, not yet the existence of a limit in
the infinite weighted sequence space or passage of the nonlinear Leray equation.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

private abbrev WcIndex244 := thirdFullThreeBandZ3Index244
private abbrev WcBand244 := EuclideanSpace ℂ (Fin 3)
private abbrev WcTime244 (a : ℝ) :=
  Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)
private abbrev WcCurve244 (a : ℝ) :=
  BoundedContinuousFunction (WcTime244 a) WcBand244

/-- Uniform convergence in time at each Fourier mode yields a SINGLE Cauchy
index for the entire fixed finite cube. All low Fourier weights are paid
by one finite positive sum; no uniformity over infinitely many modes is
assumed. -/
theorem thirdFullThreeBand_z3Galerkin_uniformFixedCoreCauchy244
    (a : ℝ)
    (f : ℕ → WcTime244 a → WcIndex244 → WcBand244)
    (g : WcIndex244 → WcTime244 a → WcBand244)
    (hUniform : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k in atTop, ∀ t : WcTime244 a,
        dist (f k t n) (g n t) < epsilon)
    (N : ℕ) (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : WcTime244 a,
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
        (thirdFullThreeBandZ3GalerkinFixedCoreCube244 N)
        (fun n => f k t n - f l t n) ≤ epsilon := by
  classical
  let q := thirdFullThreeBandZ3GalerkinFixedCoreCube244 N
  let E : ℝ := ∑ n ∈ q, thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n
  have hE : 0 ≤ E := by
    dsimp only [E]
    apply Finset.sum_nonneg
    intro n hn
    exact (thirdFullThreeBand_z3Weight_pos244 _ n).le
  let delta : ℝ := epsilon / (2 * (E + 1))
  have hDen : 0 < 2 * (E + 1) := by positivity
  have hDelta : 0 < delta := div_pos hEpsilon hDen
  have hSmall : (2 * delta) * E ≤ epsilon := by
    have hExact : delta * (2 * (E + 1)) = epsilon := by
      dsimp only [delta]
      field_simp [ne_of_gt hDen]
    nlinarith
  have hAll : ∀ᶠ k in atTop, ∀ n ∈ q, ∀ t : WcTime244 a,
      dist (f k t n) (g n t) < delta := by
    apply (Finset.eventually_all q).2
    intro n hn
    exact hUniform n delta hDelta
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨K, ?_⟩
  intro k hk l hl t
  change (∑ n ∈ q,
    thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n *
      ‖f k t n - f l t n‖) ≤ epsilon
  calc
    _ ≤ ∑ n ∈ q,
        thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n *
          (2 * delta) := by
          apply Finset.sum_le_sum
          intro n hn
          have hLeft := hK k hk n hn t
          have hRight := hK l hl n hn t
          have hDist : ‖f k t n - f l t n‖ ≤ 2 * delta := by
            calc
              _ = dist (f k t n) (f l t n) := (dist_eq_norm _ _).symm
              _ ≤ dist (f k t n) (g n t) + dist (g n t) (f l t n) :=
                dist_triangle _ _ _
              _ ≤ 2 * delta := by
                rw [dist_comm (g n t) (f l t n)]
                linarith
          exact mul_le_mul_of_nonneg_left hDist
            (thirdFullThreeBand_z3Weight_pos244 _ n).le
    _ = (2 * delta) * E := by
      dsimp only [E]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ epsilon := hSmall

/-- The exact 9/5 -> 3/2 spectral tail is a geometric 5/6 power.
Thus its cutoff-independent 200-factor tends to zero. -/
theorem thirdFullThreeBand_z3Galerkin_WienerDifferenceTail_tendsto_zero244 :
    Tendsto (fun N : ℕ =>
      Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) *
        (N : ℝ)) * 200) atTop (nhds (0 : ℝ)) := by
  have hBase :
      Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ))) =
      (5 / 6 : ℝ) := by
    rw [neg_sub, Real.exp_sub,
      Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 9 / 5)]
    norm_num
  have hExp (N : ℕ) :
      Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) *
        (N : ℝ)) = (5 / 6 : ℝ) ^ N := by
    calc
      _ = Real.exp ((N : ℝ) *
          (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)))) := by ring
      _ = (Real.exp (-(Real.log (9 / 5 : ℝ) -
          Real.log (3 / 2 : ℝ)))) ^ N := by rw [Real.exp_nat_mul]
      _ = (5 / 6 : ℝ) ^ N := by rw [hBase]
  have hPower : Tendsto (fun N : ℕ => (5 / 6 : ℝ) ^ N)
      atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hMul : Tendsto (fun N : ℕ => (5 / 6 : ℝ) ^ N * 200)
      atTop (nhds (0 : ℝ)) := by
    simpa only [zero_mul] using hPower.mul_const (200 : ℝ)
  have hEq :
      (fun N : ℕ => Real.exp
        (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) *
          (N : ℝ)) * 200) =
      (fun N : ℕ => (5 / 6 : ℝ) ^ N * 200) := by
    funext N
    rw [hExp N]
  rw [hEq]
  exact hMul

/-- For every positive tolerance the 200*(5/6)^N high-frequency cost
is strictly smaller than that tolerance at some explicit finite cube. -/
theorem thirdFullThreeBand_z3Galerkin_WienerDifferenceTail_small244
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ,
      Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) *
        (N : ℝ)) * 200 < epsilon := by
  have hEventually : ∀ᶠ N : ℕ in atTop,
      Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) *
        (N : ℝ)) * 200 < epsilon :=
    thirdFullThreeBand_z3Galerkin_WienerDifferenceTail_tendsto_zero244.eventually
      (Iio_mem_nhds hEpsilon)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEventually
  exact ⟨N, hN N le_rfl⟩

/-- The full, cutoff-independent strong Wiener Cauchy upgrade: the SAME
subsequence is Cauchy in W_log(3/2), UNIFORMLY for all times in the
closed common interval. The difference uses the union of two unrelated
finite supports and zero-extended genuine Galerkin coefficients. -/
theorem thirdFullThreeBand_z3Galerkin_uniformTime_strongWienerCauchy244
    (a : ℝ) (s : ℕ → Finset WcIndex244)
    (gamma : (k : ℕ) → ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 (s k))
    (hHigh : ∀ k, ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (9 / 5 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (gamma k t)) ≤ 100)
    (g : WcIndex244 → WcCurve244 a) (φ : ℕ → ℕ)
    (hUniform : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k in atTop, ∀ t : WcTime244 a,
        dist (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
          (gamma (φ k) t) n) (g n t) < epsilon) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : WcTime244 a,
        thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
          (s (φ k) ∪ s (φ l))
          (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
              (gamma (φ k) t) n -
            thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ l))
              (gamma (φ l) t) n) < epsilon := by
  classical
  intro epsilon hEpsilon
  obtain ⟨N, hTail⟩ :=
    thirdFullThreeBand_z3Galerkin_WienerDifferenceTail_small244
      (epsilon / 2) (by linarith)
  let f : ℕ → WcTime244 a → WcIndex244 → WcBand244 :=
    fun k t n => thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
      (gamma (φ k) t) n
  obtain ⟨K, hCore⟩ := thirdFullThreeBand_z3Galerkin_uniformFixedCoreCauchy244
    a f (fun n t => g n t) (by
      intro n eta hEta
      exact hUniform n eta hEta) N (epsilon / 2) (by linarith)
  refine ⟨K, ?_⟩
  intro k hk l hl t
  have hFixed := hCore k hk l hl t
  have hTwo := thirdFullThreeBand_z3Galerkin_twoCutoff_fixedCore244
    N (s (φ k)) (s (φ l)) (gamma (φ k) t) (gamma (φ l) t)
    (hHigh (φ k) t t.property) (hHigh (φ l) t t.property)
  have hMid := hTwo.trans (add_le_add_left hFixed _)
  have hBound :
      epsilon / 2 + Real.exp
        (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) *
          (N : ℝ)) * 200 < epsilon := by linarith
  exact hMid.trans_lt hBound

/-- ALL finite Galerkin trajectories, one common Fourier diagonal, and the
UNIFORM STRONG Wiener Cauchy estimate are constructed directly from the
strict analytic initial ball. Neither nested cutoffs nor compatibility of
independent initial states is a premise. -/
theorem thirdFullThreeBand_z3Galerkin_exists_constructedStrongWienerCauchy244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : ℕ → Finset WcIndex244)
    (x0 : (k : ℕ) → thirdFullThreeBandZ3GalerkinFiniteState244 (s k))
    (hInitial : ∀ k,
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (2 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x0 k)) < 100) :
    ∃ gamma : (k : ℕ) → ℝ →
        thirdFullThreeBandZ3GalerkinFiniteState244 (s k),
      (∀ k, gamma k a = x0 k ∧
        ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
          HasDerivAt (gamma k)
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu (s k)
              (gamma k t)) t) ∧
      ∃ g : WcIndex244 → WcCurve244 a,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ n, ∀ epsilon : ℝ, 0 < epsilon →
          ∀ᶠ k in atTop, ∀ t : WcTime244 a,
            dist (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
              (gamma (φ k) t) n) (g n t) < epsilon) ∧
        (∀ epsilon : ℝ, 0 < epsilon →
          ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : WcTime244 a,
            thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
              (s (φ k) ∪ s (φ l))
              (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
                  (gamma (φ k) t) n -
                thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ l))
                  (gamma (φ l) t) n) < epsilon) := by
  classical
  have hEx (k : ℕ) :=
    thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244
      mu a hmu hmuMax (s k) (x0 k) (hInitial k)
  let gamma (k : ℕ) := Classical.choose (hEx k)
  have hSpec (k : ℕ) := Classical.choose_spec (hEx k)
  have hLip (k : ℕ) :
      LipschitzOnWith (51000 : NNReal) (gamma k)
        (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)) :=
    (hSpec k).2.2.2.1
  have hHigh (k : ℕ) (t : ℝ)
      (ht : t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)) :
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (9 / 5 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (gamma k t)) ≤ 100 :=
    (hSpec k).2.2.2.2.1 t ht
  obtain ⟨g, φ, hStrict, _hModeConvergence, hUniform⟩ :=
    thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244
      a s gamma hLip hHigh
  have hCauchy := thirdFullThreeBand_z3Galerkin_uniformTime_strongWienerCauchy244
    a s gamma hHigh g φ hUniform
  refine ⟨gamma, ?_, g, φ, hStrict, hUniform, hCauchy⟩
  intro k
  exact ⟨(hSpec k).1, (hSpec k).2.1⟩

end
end PrimeTensor.FirstMonomialTriad

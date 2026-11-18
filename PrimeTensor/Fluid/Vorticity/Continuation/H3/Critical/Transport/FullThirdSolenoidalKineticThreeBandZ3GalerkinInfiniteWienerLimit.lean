import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinStrongWienerCauchy
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
# Genuine infinite Fourier Wiener limit of the constructed finite Galerkin flows

The preceding modules construct a uniform-time Fourier diagonal subsequence
and show that it is Cauchy in W_log(3/2). This module takes the actual
coordinate limit, which consists of bounded continuous time-curves, and
proves that it defines a summable infinite Fourier field. A finite-sum
Fatou argument preserves its W_log(9/5) mass <= 100 at every time.

Uniform coordinate convergence on a fixed finite cube plus the two-radius
analytic tail then yields convergence in the full INFINITE sum of
(3/2)^degree * norm of the Fourier difference, uniformly in time.

No convergence of the differentiated nonlinear Leray convolution or
identification of a Navier--Stokes solution is claimed here.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

private abbrev WiIndex244 := thirdFullThreeBandZ3Index244
private abbrev WiBand244 := EuclideanSpace ℂ (Fin 3)
private abbrev WiTime244 (a : ℝ) :=
  Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)
private abbrev WiCurve244 (a : ℝ) :=
  BoundedContinuousFunction (WiTime244 a) WiBand244

/-- The *infinite*, not cutoff-truncated, weighted Wiener Fourier mass. -/
noncomputable def thirdFullThreeBandZ3InfiniteWienerMass244
    (r : ℝ) (u : WiIndex244 → WiBand244) : ℝ :=
  ∑' n : WiIndex244, thirdFullThreeBandZ3Weight244 r n * ‖u n‖

/-- Zero-extending a finite Galerkin state does not add Wiener mass,
including when the comparison set contains new frequencies. -/
theorem thirdFullThreeBand_z3Galerkin_zeroExtend_arbitraryFiniteMass_le244
    (r : ℝ) (s q : Finset WiIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r q
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) ≤
    thirdFullThreeBandZ3GalerkinWienerMass244 r s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) := by
  classical
  calc
    thirdFullThreeBandZ3GalerkinWienerMass244 r q
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 r (q ∪ s)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) := by
          unfold thirdFullThreeBandZ3GalerkinWienerMass244
          apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          intro n hn hnNot
          exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le
            (norm_nonneg _)
    _ = _ := thirdFullThreeBand_z3GalerkinWiener_zeroExtend_superset244
      r s (q ∪ s) Finset.subset_union_right x

/-- Finite-sum Fatou principle for a family of time curves. A uniform high-radius
bound on EVERY approximating finite Fourier sum passes to EVERY finite
Fourier sum of the coordinatewise uniform-time limit. -/
theorem thirdFullThreeBand_z3Galerkin_uniformCoordinateLimit_finiteHighMass244
    {T : Type*}
    (f : ℕ → T → WiIndex244 → WiBand244)
    (g : WiIndex244 → T → WiBand244)
    (hHigh : ∀ k t (q : Finset WiIndex244),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q (f k t) ≤ 100)
    (hUniform : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k in atTop, ∀ t : T, dist (f k t n) (g n t) < epsilon) :
    ∀ t (q : Finset WiIndex244),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q (fun n => g n t) ≤ 100 := by
  classical
  intro t q
  have hMode (n : WiIndex244) :
      Tendsto (fun k => f k t n) atTop (nhds (g n t)) := by
    apply Metric.tendsto_atTop.mpr
    intro epsilon hEpsilon
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hUniform n epsilon hEpsilon)
    exact ⟨K, fun k hk => hK k hk t⟩
  have hTerm (n : WiIndex244) :
      Tendsto (fun k => thirdFullThreeBandZ3Weight244
        (Real.log (9 / 5 : ℝ)) n * ‖f k t n‖) atTop
      (nhds (thirdFullThreeBandZ3Weight244
        (Real.log (9 / 5 : ℝ)) n * ‖g n t‖)) := by
    have hNorm : Tendsto (fun k => ‖f k t n‖) atTop (nhds ‖g n t‖) :=
      (continuous_norm.tendsto (g n t)).comp (hMode n)
    exact tendsto_const_nhds.mul hNorm
  have hFinite (q : Finset WiIndex244) :
      Tendsto (fun k => ∑ n ∈ q,
        thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n * ‖f k t n‖)
        atTop
      (nhds (∑ n ∈ q,
        thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n * ‖g n t‖)) := by
    induction q using Finset.induction_on with
    | empty => simp
    | @insert n q hn ih =>
      simpa [Finset.sum_insert, hn] using (hTerm n).add ih
  unfold thirdFullThreeBandZ3GalerkinWienerMass244 at *
  exact le_of_tendsto (hFinite q)
    (Filter.Eventually.of_forall fun k => hHigh k t q)

/-- Each time slice of the actual infinite Fourier limit is an element
of the high-radius weighted ell-one class, with bound 100. -/
theorem thirdFullThreeBand_z3Galerkin_limit_highWiener_summable244
    {T : Type*} (g : WiIndex244 → T → WiBand244)
    (hBound : ∀ t (q : Finset WiIndex244),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q (fun n => g n t) ≤ 100) :
    ∀ t, Summable (fun n : WiIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n * ‖g n t‖) ∧
      thirdFullThreeBandZ3InfiniteWienerMass244
        (Real.log (9 / 5 : ℝ)) (fun n => g n t) ≤ 100 := by
  classical
  intro t
  have hNonneg (n : WiIndex244) :
      0 ≤ thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n *
        ‖g n t‖ :=
    mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ n).le (norm_nonneg _)
  have hEvery (q : Finset WiIndex244) :
      (∑ n ∈ q, thirdFullThreeBandZ3Weight244
        (Real.log (9 / 5 : ℝ)) n * ‖g n t‖) ≤ 100 :=
    hBound t q
  exact ⟨summable_of_sum_le hNonneg hEvery,
    Real.tsum_le_of_sum_le hNonneg hEvery⟩

/-- A fixed cube controls every finite partial sum of the *infinite*
low-radius difference, with the same 200*(5/6)^N spectral tail. -/
theorem thirdFullThreeBand_z3Galerkin_finiteToInfinite_fixedCore244
    (N : ℕ) (u v : WiIndex244 → WiBand244)
    (hU : ∀ q : Finset WiIndex244,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q u ≤ 100)
    (hV : ∀ q : Finset WiIndex244,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q v ≤ 100) :
    thirdFullThreeBandZ3InfiniteWienerMass244 (Real.log (3 / 2 : ℝ))
        (fun n => u n - v n) ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
        (thirdFullThreeBandZ3GalerkinFixedCoreCube244 N)
        (fun n => u n - v n) +
      Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) *
        (N : ℝ)) * 200 := by
  classical
  let c : ℝ := thirdFullThreeBandZ3GalerkinWienerMass244
    (Real.log (3 / 2 : ℝ))
    (thirdFullThreeBandZ3GalerkinFixedCoreCube244 N) (fun n => u n - v n) +
    Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) *
      (N : ℝ)) * 200
  have hEvery (q : Finset WiIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
        q (fun n => u n - v n) ≤ c := by
    have hRadius : Real.log (3 / 2 : ℝ) ≤ Real.log (9 / 5 : ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hSplit := thirdFullThreeBand_z3GalerkinWiener_fixedCore_split244
      (Real.log (3 / 2 : ℝ)) (Real.log (9 / 5 : ℝ))
      (N : ℝ) hRadius q u v (hU q) (hV q)
    have hSubset : q.filter (fun n =>
        thirdFullThreeBandZ3Degree244 n < (N : ℝ)) ⊆
        thirdFullThreeBandZ3GalerkinFixedCoreCube244 N := by
      intro n hn
      exact thirdFullThreeBand_z3Galerkin_degree_lt_mem_fixedCube244
        N n (Finset.mem_filter.mp hn).2
    have hCore : thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ))
        (q.filter (fun n => thirdFullThreeBandZ3Degree244 n < (N : ℝ)))
        (fun n => u n - v n) ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
        (thirdFullThreeBandZ3GalerkinFixedCoreCube244 N)
        (fun n => u n - v n) := by
      unfold thirdFullThreeBandZ3GalerkinWienerMass244
      apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
      intro n hn hnNot
      exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ n).le
        (norm_nonneg _)
    exact hSplit.trans (add_le_add_left hCore _)
  have hNonneg (n : WiIndex244) :
      0 ≤ thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n *
        ‖u n - v n‖ :=
    mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ n).le (norm_nonneg _)
  exact Real.tsum_le_of_sum_le hNonneg (by
    intro q
    exact hEvery q)

/-- Strong convergence to the TRUE infinite weighted Fourier series,
uniformly across the entire closed time interval. Finite-sum Fatou
closes the high-radius estimate at the limit, so no prior summability
or infinite-limit hypotheses are required. -/
theorem thirdFullThreeBand_z3Galerkin_uniformTime_infiniteWienerLimit244
    {T : Type*}
    (f : ℕ → T → WiIndex244 → WiBand244)
    (g : WiIndex244 → T → WiBand244)
    (hHigh : ∀ k t (q : Finset WiIndex244),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q (f k t) ≤ 100)
    (hUniform : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k in atTop, ∀ t : T, dist (f k t n) (g n t) < epsilon) :
    (∀ t, Summable (fun n : WiIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n * ‖g n t‖) ∧
      thirdFullThreeBandZ3InfiniteWienerMass244
        (Real.log (9 / 5 : ℝ)) (fun n => g n t) ≤ 100) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k in atTop, ∀ t : T,
        thirdFullThreeBandZ3InfiniteWienerMass244
          (Real.log (3 / 2 : ℝ)) (fun n => f k t n - g n t) < epsilon) := by
  classical
  have hLimit := thirdFullThreeBand_z3Galerkin_uniformCoordinateLimit_finiteHighMass244
    f g hHigh hUniform
  constructor
  · exact thirdFullThreeBand_z3Galerkin_limit_highWiener_summable244 g hLimit
  · intro epsilon hEpsilon
    obtain ⟨N, hTail⟩ :=
      thirdFullThreeBand_z3Galerkin_WienerDifferenceTail_small244
        (epsilon / 2) (by linarith)
    let q := thirdFullThreeBandZ3GalerkinFixedCoreCube244 N
    let E : ℝ := ∑ n ∈ q,
      thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n
    have hE : 0 ≤ E := by
      dsimp only [E]
      apply Finset.sum_nonneg
      intro n hn
      exact (thirdFullThreeBand_z3Weight_pos244 _ n).le
    let delta : ℝ := epsilon / (2 * (E + 1))
    have hDen : 0 < 2 * (E + 1) := by positivity
    have hDelta : 0 < delta := div_pos hEpsilon hDen
    have hSmall : delta * E ≤ epsilon / 2 := by
      have hExact : delta * (2 * (E + 1)) = epsilon := by
        dsimp only [delta]
        field_simp [ne_of_gt hDen]
      nlinarith
    have hAll : ∀ᶠ k in atTop, ∀ n ∈ q, ∀ t : T,
        dist (f k t n) (g n t) < delta := by
      apply (Finset.eventually_all q).2
      intro n hn
      exact hUniform n delta hDelta
    filter_upwards [hAll] with k hk t
    have hCore : thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) q
        (fun n => f k t n - g n t) ≤ epsilon / 2 := by
      unfold thirdFullThreeBandZ3GalerkinWienerMass244
      calc
        (∑ n ∈ q, thirdFullThreeBandZ3Weight244
          (Real.log (3 / 2 : ℝ)) n * ‖f k t n - g n t‖) ≤
        ∑ n ∈ q, thirdFullThreeBandZ3Weight244
          (Real.log (3 / 2 : ℝ)) n * delta := by
            apply Finset.sum_le_sum
            intro n hn
            have hMode := (hk n hn t).le
            have hNorm : ‖f k t n - g n t‖ ≤ delta := by
              simpa only [dist_eq_norm] using hMode
            exact mul_le_mul_of_nonneg_left hNorm
              (thirdFullThreeBand_z3Weight_pos244 _ n).le
        _ = delta * E := by
          dsimp only [E]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ ≤ epsilon / 2 := hSmall
    have hGlobal := thirdFullThreeBand_z3Galerkin_finiteToInfinite_fixedCore244
      N (f k t) (fun n => g n t) (hHigh k t) (hLimit t)
    have hBudget : epsilon / 2 +
        Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) *
          (N : ℝ)) * 200 < epsilon := by linarith
    exact (hGlobal.trans (add_le_add_left hCore _)).trans_lt hBudget

/-- The infinite Fourier limit is now constructed from genuine finite
Galerkin flows and an actual Arzela subsequence, not assumed. Each limit
coefficient is continuous in time and belongs to the uniform high-radius
Wiener ball; the full weighted 3/2 distance converges to zero uniformly
in time. This is NOT YET the infinite Navier--Stokes equation. -/
theorem thirdFullThreeBand_z3Galerkin_exists_actualInfiniteWienerLimit244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : ℕ → Finset WiIndex244)
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
      ∃ g : WiIndex244 → WiCurve244 a,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ t : WiTime244 a,
          Summable (fun n : WiIndex244 =>
            thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n *
              ‖g n t‖) ∧
          thirdFullThreeBandZ3InfiniteWienerMass244
            (Real.log (9 / 5 : ℝ)) (fun n => g n t) ≤ 100) ∧
        (∀ epsilon : ℝ, 0 < epsilon →
          ∀ᶠ k in atTop, ∀ t : WiTime244 a,
            thirdFullThreeBandZ3InfiniteWienerMass244
              (Real.log (3 / 2 : ℝ))
              (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244
                (s (φ k)) (gamma (φ k) t) n - g n t) < epsilon) := by
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
  let f : ℕ → WiTime244 a → WiIndex244 → WiBand244 :=
    fun k t n => thirdFullThreeBandZ3GalerkinFiniteExtend244
      (s (φ k)) (gamma (φ k) t) n
  have hFiniteHigh (k : ℕ) (t : WiTime244 a)
      (q : Finset WiIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q (f k t) ≤ 100 := by
    exact (thirdFullThreeBand_z3Galerkin_zeroExtend_arbitraryFiniteMass_le244
      (Real.log (9 / 5 : ℝ)) (s (φ k)) q (gamma (φ k) t)).trans
      (hHigh (φ k) t t.property)
  obtain ⟨hLimitBound, hStrong⟩ :=
    thirdFullThreeBand_z3Galerkin_uniformTime_infiniteWienerLimit244
      f (fun n t => g n t) hFiniteHigh (by
        intro n epsilon hEpsilon
        exact hUniform n epsilon hEpsilon)
  refine ⟨gamma, ?_, g, φ, hStrict, hLimitBound, ?_⟩
  · intro k
    exact ⟨(hSpec k).1, (hSpec k).2.1⟩
  · intro epsilon hEpsilon
    exact hStrong epsilon hEpsilon

end
end PrimeTensor.FirstMonomialTriad

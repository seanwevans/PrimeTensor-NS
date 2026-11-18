import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinCrossCutoffLeraySource
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
# Completion of the exact finite Leray sources in infinite W_log(5/4)

The complete ordered complex Leray convolution was proved uniformly Cauchy
at every finite collection of output frequencies along the genuine finite
Galerkin trajectories. We now COMPLETE that source in the infinite weighted
Fourier l1 space, rather than merely asserting per-coordinate convergence.

The finite high-radius 100-ball and the 5/4 -> 3/2 derivative reserve give
a 50000 bound for the full quadratic source over ANY finite output set.
Its limit therefore has summable W_log(5/4) mass, at most 50000. The exact
finite-source Cauchy estimate also passes to the whole infinite Fourier sum,
uniformly throughout the common closed time interval.

The source is the actual limit of the exact ordered Leray Galerkin sums. The
identification with an independently defined infinite ordered-pair tsum and
the passage of the time-derivative / retarded integral remain separate.
No claim is made here about Navier--Stokes continuation or global regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

private abbrev IsIndex244 := thirdFullThreeBandZ3Index244
private abbrev IsBand244 := EuclideanSpace ℂ (Fin 3)
private abbrev IsTime244 (a : ℝ) :=
  Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)
private abbrev IsCurve244 (a : ℝ) :=
  BoundedContinuousFunction (IsTime244 a) IsBand244

/-- A uniform finite-output bound on the ACTUAL full Leray quadratic source:
50000 is independent of the retained input and output Fourier sets. -/
theorem thirdFullThreeBand_z3GalerkinQuadratic_allOutputs50000_244
    (s outputs : Finset IsIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hHigh : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (5 / 4 : ℝ)) outputs
      (thirdFullThreeBandZ3GalerkinQuadratic244 s s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x)) ≤ 50000 := by
  classical
  let u := thirdFullThreeBandZ3GalerkinFiniteExtend244 s x
  have hRadiusHigh : Real.log (3 / 2 : ℝ) ≤ Real.log (9 / 5 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hRadiusLow : Real.log (5 / 4 : ℝ) ≤ Real.log (3 / 2 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hMiddle : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s u ≤ 100 :=
    (thirdFullThreeBand_z3WienerMass_radius_mono244 _ _ hRadiusHigh s u).trans hHigh
  have hLow : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (5 / 4 : ℝ)) s u ≤ 100 :=
    (thirdFullThreeBand_z3WienerMass_radius_mono244 _ _ hRadiusLow s u).trans hMiddle
  have hDerivative : thirdFullThreeBandZ3GalerkinWienerDerivative244
      (Real.log (5 / 4 : ℝ)) s u ≤ 500 := by
    have hReserve := thirdFullThreeBand_z3WienerDerivative_reserved244
      (Real.log (5 / 4 : ℝ)) (Real.log (3 / 2 : ℝ)) 5
      (by norm_num) s u (by
        intro n hn
        exact thirdFullThreeBand_z3TwoRadiusDerivativeEnvelope244 n)
    have hCap := mul_le_mul_of_nonneg_left hMiddle (by norm_num : (0 : ℝ) ≤ 5)
    linarith
  have hDerivativeNonneg : 0 ≤ thirdFullThreeBandZ3GalerkinWienerDerivative244
      (Real.log (5 / 4 : ℝ)) s u := by
    unfold thirdFullThreeBandZ3GalerkinWienerDerivative244
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg
      (mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ n).le
        (thirdFullThreeBand_z3Degree_nonneg244 n)) (norm_nonneg _)
  have hSource := thirdFullThreeBand_z3GalerkinAllOutputWienerBound244
    (Real.log (5 / 4 : ℝ)) (Real.log_nonneg (by norm_num))
    outputs s s u u
  calc
    _ ≤ thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (5 / 4 : ℝ)) s u *
          thirdFullThreeBandZ3GalerkinWienerDerivative244 (Real.log (5 / 4 : ℝ)) s u :=
      hSource
    _ ≤ 100 * thirdFullThreeBandZ3GalerkinWienerDerivative244
          (Real.log (5 / 4 : ℝ)) s u :=
      mul_le_mul_of_nonneg_right hLow hDerivativeNonneg
    _ ≤ 100 * 500 := mul_le_mul_of_nonneg_left hDerivative (by norm_num)
    _ = 50000 := by norm_num

/-- If an arbitrary family of Fourier sources is uniformly Cauchy over
ALL finite output sets at once, every individual output coefficient is a
Cauchy sequence. The proof uses the fact that analytic weights are >= 1. -/
theorem thirdFullThreeBand_z3Galerkin_sourceModeCauchy244
    {T : Type*} (f : ℕ → T → IsIndex244 → IsBand244)
    (hCauchy : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : T,
        ∀ q : Finset IsIndex244,
          thirdFullThreeBandZ3GalerkinWienerMass244
            (Real.log (5 / 4 : ℝ)) q (fun n => f k t n - f l t n) < epsilon)
    (t : T) (n : IsIndex244) :
    CauchySeq (fun k => f k t n) := by
  classical
  apply Metric.cauchySeq_iff.mpr
  intro epsilon hEpsilon
  obtain ⟨K, hK⟩ := hCauchy epsilon hEpsilon
  refine ⟨K, ?_⟩
  intro k hk l hl
  have hOne := hK k hk l hl t ({n} : Finset IsIndex244)
  simp only [thirdFullThreeBandZ3GalerkinWienerMass244, Finset.sum_singleton] at hOne
  have hWeight : 1 ≤ thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n :=
    thirdFullThreeBand_z3GalerkinWeight_one_le244
      (Real.log (5 / 4 : ℝ)) (Real.log_nonneg (by norm_num)) n
  have hExtra : 0 ≤
      (thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n - 1) *
        ‖f k t n - f l t n‖ :=
    mul_nonneg (sub_nonneg.mpr hWeight) (norm_nonneg _)
  have hDist : ‖f k t n - f l t n‖ < epsilon := by nlinarith
  simpa only [dist_eq_norm] using hDist

/-- Completeness of the physical complex three-coordinate output space
creates an actual source coefficient at every frequency and every time.
The high-radius finite-output 50000 bound passes to the infinite source,
and full W_log(5/4) convergence holds UNIFORMLY in the time parameter. -/
theorem thirdFullThreeBand_z3Galerkin_uniformSourceCompletion244
    {T : Type*} (f : ℕ → T → IsIndex244 → IsBand244)
    (hCauchy : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : T,
        ∀ q : Finset IsIndex244,
          thirdFullThreeBandZ3GalerkinWienerMass244
            (Real.log (5 / 4 : ℝ)) q (fun n => f k t n - f l t n) < epsilon)
    (hBound : ∀ k t (q : Finset IsIndex244),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (5 / 4 : ℝ)) q (f k t) ≤ 50000) :
    ∃ Q : T → IsIndex244 → IsBand244,
      (∀ t n, Tendsto (fun k => f k t n) atTop (nhds (Q t n))) ∧
      (∀ t,
        Summable (fun n : IsIndex244 =>
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n * ‖Q t n‖) ∧
        thirdFullThreeBandZ3InfiniteWienerMass244 (Real.log (5 / 4 : ℝ))
          (Q t) ≤ 50000) ∧
      (∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ k in atTop, ∀ t : T,
          thirdFullThreeBandZ3InfiniteWienerMass244 (Real.log (5 / 4 : ℝ))
            (fun n => f k t n - Q t n) < epsilon) := by
  classical
  have hExist (t : T) (n : IsIndex244) :
      ∃ v : IsBand244, Tendsto (fun k => f k t n) atTop (nhds v) :=
    cauchySeq_tendsto_of_complete
      (thirdFullThreeBand_z3Galerkin_sourceModeCauchy244 f hCauchy t n)
  let Q (t : T) (n : IsIndex244) : IsBand244 := Classical.choose (hExist t n)
  have hMode (t : T) (n : IsIndex244) :
      Tendsto (fun k => f k t n) atTop (nhds (Q t n)) :=
    Classical.choose_spec (hExist t n)
  have hTerm (k : ℕ) (t : T) (n : IsIndex244) :
      Tendsto (fun l => thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        ‖f k t n - f l t n‖) atTop
        (nhds (thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖f k t n - Q t n‖)) := by
    have hNorm : Tendsto (fun l => ‖f k t n - f l t n‖)
        atTop (nhds ‖f k t n - Q t n‖) :=
      (tendsto_const_nhds.sub (hMode t n)).norm
    exact tendsto_const_nhds.mul hNorm
  have hFiniteDifference (k : ℕ) (t : T) (q : Finset IsIndex244) :
      Tendsto (fun l => ∑ n ∈ q,
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖f k t n - f l t n‖) atTop
        (nhds (∑ n ∈ q,
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
            ‖f k t n - Q t n‖)) := by
    induction q using Finset.induction_on with
    | empty => simp
    | @insert n q hn ih =>
      simpa [Finset.sum_insert, hn] using (hTerm k t n).add ih
  have hTermBound (t : T) (n : IsIndex244) :
      Tendsto (fun k => thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        ‖f k t n‖) atTop
        (nhds (thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖Q t n‖)) :=
    tendsto_const_nhds.mul ((hMode t n).norm)
  have hFiniteBound (t : T) (q : Finset IsIndex244) :
      Tendsto (fun k => ∑ n ∈ q,
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖f k t n‖) atTop
        (nhds (∑ n ∈ q,
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
            ‖Q t n‖)) := by
    induction q using Finset.induction_on with
    | empty => simp
    | @insert n q hn ih =>
      simpa [Finset.sum_insert, hn] using (hTermBound t n).add ih
  have hEveryBound (t : T) (q : Finset IsIndex244) :
      (∑ n ∈ q, thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
        ‖Q t n‖) ≤ 50000 := by
    exact le_of_tendsto (hFiniteBound t q)
      (Filter.Eventually.of_forall fun k => hBound k t q)
  have hLimitMass (t : T) :
      Summable (fun n : IsIndex244 =>
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n * ‖Q t n‖) ∧
      thirdFullThreeBandZ3InfiniteWienerMass244 (Real.log (5 / 4 : ℝ))
        (Q t) ≤ 50000 := by
    have hNonneg (n : IsIndex244) :
        0 ≤ thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖Q t n‖ :=
      mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ n).le (norm_nonneg _)
    exact ⟨summable_of_sum_le hNonneg (hEveryBound t),
      Real.tsum_le_of_sum_le hNonneg (hEveryBound t)⟩
  refine ⟨Q, hMode, hLimitMass, ?_⟩
  intro epsilon hEpsilon
  obtain ⟨K, hK⟩ := hCauchy (epsilon / 2) (by linarith)
  apply Filter.eventually_atTop.mpr
  refine ⟨K, ?_⟩
  intro k hk t
  have hFiniteError (q : Finset IsIndex244) :
      (∑ n ∈ q, thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖f k t n - Q t n‖) ≤ epsilon / 2 := by
    apply le_of_tendsto (hFiniteDifference k t q)
    apply Filter.eventually_atTop.mpr
    refine ⟨K, ?_⟩
    intro l hl
    exact (hK k hk l hl t q).le
  have hError : thirdFullThreeBandZ3InfiniteWienerMass244
      (Real.log (5 / 4 : ℝ)) (fun n => f k t n - Q t n) ≤ epsilon / 2 := by
    apply Real.tsum_le_of_sum_le
      (fun n => mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ n).le
        (norm_nonneg _))
    exact hFiniteError
  exact lt_of_le_of_lt hError (by linarith)

/-- On actual Galerkin ODE paths with the common high Wiener bound, the
exact complete Leray sources converge uniformly in the full infinite
W_log(5/4) norm to a summable 50000-bounded source field. -/
theorem thirdFullThreeBand_z3Galerkin_actualInfiniteSourceLimit244
    (a : ℝ) (s : ℕ → Finset IsIndex244)
    (gamma : (k : ℕ) → ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 (s k))
    (φ : ℕ → ℕ)
    (hHigh : ∀ k, ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (gamma k t)) ≤ 100)
    (hCauchy : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : IsTime244 a,
        thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
          (s (φ k) ∪ s (φ l))
          (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
              (gamma (φ k) t) n -
            thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ l))
              (gamma (φ l) t) n) < epsilon) :
    ∃ Q : IsTime244 a → IsIndex244 → IsBand244,
      (∀ t, Summable (fun n : IsIndex244 =>
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n * ‖Q t n‖) ∧
        thirdFullThreeBandZ3InfiniteWienerMass244 (Real.log (5 / 4 : ℝ))
          (Q t) ≤ 50000) ∧
      (∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ k in atTop, ∀ t : IsTime244 a,
          thirdFullThreeBandZ3InfiniteWienerMass244 (Real.log (5 / 4 : ℝ))
            (fun n => thirdFullThreeBandZ3GalerkinQuadratic244
              (s (φ k)) (s (φ k))
              (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
                (gamma (φ k) t))
              (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
                (gamma (φ k) t)) n - Q t n) < epsilon) := by
  classical
  let f : ℕ → IsTime244 a → IsIndex244 → IsBand244 :=
    fun k t n => thirdFullThreeBandZ3GalerkinQuadratic244
      (s (φ k)) (s (φ k))
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k)) (gamma (φ k) t))
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k)) (gamma (φ k) t)) n
  have hSourceCauchy : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : IsTime244 a,
        ∀ q : Finset IsIndex244,
          thirdFullThreeBandZ3GalerkinWienerMass244
            (Real.log (5 / 4 : ℝ)) q (fun n => f k t n - f l t n) < epsilon := by
    intro epsilon hEpsilon
    obtain ⟨K, hK⟩ := thirdFullThreeBand_z3Galerkin_uniformTime_fullLeraySourceCauchy244
      a s gamma φ hHigh hCauchy epsilon hEpsilon
    refine ⟨K, ?_⟩
    intro k hk l hl t q
    exact hK k hk l hl t q
  have hSourceBound (k : ℕ) (t : IsTime244 a) (q : Finset IsIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (5 / 4 : ℝ)) q (f k t) ≤ 50000 :=
    thirdFullThreeBand_z3GalerkinQuadratic_allOutputs50000_244
      (s (φ k)) q (gamma (φ k) t) (hHigh (φ k) t t.property)
  obtain ⟨Q, _hModes, hBound, hConverges⟩ :=
    thirdFullThreeBand_z3Galerkin_uniformSourceCompletion244
      f hSourceCauchy hSourceBound
  exact ⟨Q, hBound, hConverges⟩

/-- From independent data strictly inside the high analytic ball, build
actual strong finite Galerkin ODEs and one Fourier subsequence whose entire
quadratic Leray sources converge to a complete infinite weighted source.
This is a source LIMIT, not yet an infinite ordered convolution identity
or a time-integrated Navier--Stokes equation. -/
theorem thirdFullThreeBand_z3Galerkin_exists_constructedInfiniteSourceLimit244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : ℕ → Finset IsIndex244)
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
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ Q : IsTime244 a → IsIndex244 → IsBand244,
          (∀ t, Summable (fun n : IsIndex244 =>
            thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n * ‖Q t n‖) ∧
            thirdFullThreeBandZ3InfiniteWienerMass244 (Real.log (5 / 4 : ℝ))
              (Q t) ≤ 50000) ∧
          (∀ epsilon : ℝ, 0 < epsilon →
            ∀ᶠ k in atTop, ∀ t : IsTime244 a,
              thirdFullThreeBandZ3InfiniteWienerMass244 (Real.log (5 / 4 : ℝ))
                (fun n => thirdFullThreeBandZ3GalerkinQuadratic244
                  (s (φ k)) (s (φ k))
                  (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
                    (gamma (φ k) t))
                  (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
                    (gamma (φ k) t)) n - Q t n) < epsilon) := by
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
  obtain ⟨g, φ, hStrict, _hMode, hUniform⟩ :=
    thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244
      a s gamma hLip hHigh
  have hWiener := thirdFullThreeBand_z3Galerkin_uniformTime_strongWienerCauchy244
    a s gamma hHigh g φ hUniform
  obtain ⟨Q, hBound, hSource⟩ :=
    thirdFullThreeBand_z3Galerkin_actualInfiniteSourceLimit244
      a s gamma φ hHigh hWiener
  refine ⟨gamma, ?_, φ, hStrict, Q, hBound, hSource⟩
  intro k
  exact ⟨(hSpec k).1, (hSpec k).2.1⟩

end
end PrimeTensor.FirstMonomialTriad

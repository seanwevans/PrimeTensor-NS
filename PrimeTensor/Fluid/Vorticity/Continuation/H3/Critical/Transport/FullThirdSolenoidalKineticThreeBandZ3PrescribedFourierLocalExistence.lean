import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3InfiniteFourierIntegralEvolution
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinInfiniteWienerLimit
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
# Local Fourier Navier--Stokes existence with prescribed analytic initial data

For an arbitrary exhaustive sequence of finite Z^3 cutoffs, the initial finite
states are the restrictions of ONE specified infinite field u0, not an
unrelated family of initial conditions. The strict W_log(2) initial ball
supplies the finite strong Galerkin ODEs on one common horizon. One genuine
Arzela subsequence yields strong W_log(3/2) convergence; its quadratic sources
are completed and identified with the absolutely convergent infinite ordered
Leray convolution. The already verified finite-to-infinite temporal FTC then
gives the Fourier Navier--Stokes integral equation with initial trace u0.

This is a local periodic Fourier existence result. It does not establish
physical-space R^3 H^3 continuation or global regularity, nor incompressibility
and Hermitian symmetry for an arbitrary input without their own hypotheses.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev PlIndex244 := thirdFullThreeBandZ3Index244
private abbrev PlBand244 := EuclideanSpace ℂ (Fin 3)
private abbrev PlTime244 (a : ℝ) :=
  Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)
private abbrev PlCurve244 (a : ℝ) :=
  BoundedContinuousFunction (PlTime244 a) PlBand244

/-- A strict infinite analytic mass bound transfers to EVERY finite Fourier
projection without any cutoff-counting constant. -/
theorem thirdFullThreeBand_z3PrescribedInitial_finiteProjectionStrict244
    (u0 : PlIndex244 → PlBand244)
    (hSummable : Summable (fun n : PlIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n * ‖u0 n‖))
    (hStrict : thirdFullThreeBandZ3InfiniteWienerMass244
      (Real.log (2 : ℝ)) u0 < 100)
    (s : Finset PlIndex244) :
    thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (2 : ℝ)) s u0 < 100 := by
  classical
  have hNonneg (n : PlIndex244) :
      0 ≤ thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n * ‖u0 n‖ :=
    mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ n).le (norm_nonneg _)
  have hFinite := hSummable.sum_le_tsum s (fun n hn => hNonneg n)
  exact lt_of_le_of_lt hFinite hStrict

/-- Full infinite-Wiener source convergence is not needed to obtain a uniform
coordinate limit once the previously constructed source completion provides
pointwise convergence and a uniform finite-output Cauchy estimate. -/
theorem thirdFullThreeBand_z3UniformSourceCauchy_pointwiseUniform244
    {T : Type*} (f : ℕ → T → PlIndex244 → PlBand244)
    (Q : T → PlIndex244 → PlBand244)
    (hCauchy : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : T,
        ∀ q : Finset PlIndex244,
          thirdFullThreeBandZ3GalerkinWienerMass244
            (Real.log (5 / 4 : ℝ)) q (fun n => f k t n - f l t n) < epsilon)
    (hModes : ∀ t n, Tendsto (fun k => f k t n) atTop (nhds (Q t n))) :
    ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t : T, dist (f k t n) (Q t n) < epsilon := by
  classical
  intro n epsilon hEpsilon
  obtain ⟨K, hK⟩ := hCauchy (epsilon / 2) (by linarith)
  apply Filter.eventually_atTop.mpr
  refine ⟨K, ?_⟩
  intro k hk t
  let w := thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n
  have hWeighted (l : ℕ) (hl : K ≤ l) :
      w * ‖f k t n - f l t n‖ < epsilon / 2 := by
    have h := hK k hk l hl t ({n} : Finset PlIndex244)
    simpa only [thirdFullThreeBandZ3GalerkinWienerMass244,
      Finset.sum_singleton, w] using h
  have hTerm : Tendsto (fun l => w * ‖f k t n - f l t n‖)
      atTop (nhds (w * ‖f k t n - Q t n‖)) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds.sub (hModes t n)).norm)
  have hLimit : w * ‖f k t n - Q t n‖ ≤ epsilon / 2 :=
    le_of_tendsto hTerm (Filter.eventually_atTop.mpr
      ⟨K, fun l hl => (hWeighted l hl).le⟩)
  have hOne : 1 ≤ w :=
    thirdFullThreeBand_z3GalerkinWeight_one_le244
      (Real.log (5 / 4 : ℝ)) (Real.log_nonneg (by norm_num)) n
  have hNorm : ‖f k t n - Q t n‖ ≤ w * ‖f k t n - Q t n‖ := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hOne (norm_nonneg _)
  have hFinal : ‖f k t n - Q t n‖ < epsilon :=
    lt_of_le_of_lt (hNorm.trans hLimit) (by linarith)
  simpa only [dist_eq_norm] using hFinal

/-- Eventual exhaustion is preserved when one common strictly increasing
Arzela subsequence is taken. -/
theorem thirdFullThreeBand_z3GalerkinExhausts_subsequence244
    (s : ℕ → Finset PlIndex244)
    (hExhaust : thirdFullThreeBandZ3GalerkinExhausts244 s)
    (phi : ℕ → ℕ) (hStrict : StrictMono phi) :
    thirdFullThreeBandZ3GalerkinExhausts244 (fun k => s (phi k)) := by
  intro n
  exact hStrict.tendsto_atTop.eventually (hExhaust n)

/-- The canonical integer Fourier cubes form a concrete exhaustive family,
so the local-existence theorem has a nonhypothetical cutoff choice. -/
theorem thirdFullThreeBand_z3GalerkinFixedCubes_exhaust244 :
    thirdFullThreeBandZ3GalerkinExhausts244
      (fun k => thirdFullThreeBandZ3GalerkinFixedCoreCube244 k) := by
  intro n
  obtain ⟨N, hN⟩ := exists_nat_gt (thirdFullThreeBandZ3Degree244 n)
  apply Filter.eventually_atTop.mpr
  refine ⟨N, ?_⟩
  intro k hk
  apply thirdFullThreeBand_z3Galerkin_degree_lt_mem_fixedCube244 k n
  have hkR : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  exact lt_of_lt_of_le hN hkR

set_option maxHeartbeats 1000000

/-- A prescribed high-analytic-radius initial field yields one actual
infinite Fourier Navier--Stokes integral evolution on the Galerkin common
horizon. No initial approximants, convergent subsequence, infinite source,
or infinite ODE are assumed: they are all constructed in the proof.

The result concerns the exact projected complex Fourier equation on the
integer Z^3 lattice. Arbitrary initial Fourier fields are allowed; physical
solenoidality and Hermitian reality require separate invariant-subspace
statements before interpreting the result as a real divergence-free flow. -/
theorem thirdFullThreeBand_z3PrescribedFourier_localExistence244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : ℕ → Finset PlIndex244)
    (hExhaust : thirdFullThreeBandZ3GalerkinExhausts244 s)
    (u0 : PlIndex244 → PlBand244)
    (hSummable : Summable (fun n : PlIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n * ‖u0 n‖))
    (hInitial : thirdFullThreeBandZ3InfiniteWienerMass244
      (Real.log (2 : ℝ)) u0 < 100) :
    ∃ g : ℝ → PlIndex244 → PlBand244,
      (∀ n, ContinuousOn (fun t => g t n)
        (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a))) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        Summable (fun n : PlIndex244 =>
          thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n * ‖g t n‖) ∧
        thirdFullThreeBandZ3InfiniteWienerMass244
          (Real.log (9 / 5 : ℝ)) (g t) ≤ 100) ∧
      (∀ n, g a n = u0 n) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        Summable (fun n : PlIndex244 =>
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
            ‖thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n‖) ∧
        thirdFullThreeBandZ3InfiniteWienerMass244
          (Real.log (5 / 4 : ℝ))
          (thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t)) ≤ 50000) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        ∀ n : PlIndex244,
          g t n - u0 n =
            ∫ r in a..t,
              (-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
                g r n + thirdFullThreeBandZ3InfiniteOrderedLeray244 (g r) n) := by
  classical
  let b : ℝ := thirdFullThreeBandZ3GalerkinCommonHorizon244 a
  have hab : a ≤ b :=
    (thirdFullThreeBand_z3GalerkinCommonHorizon_gt244 a).le
  let z0 : PlTime244 a := ⟨a, ⟨le_rfl, hab⟩⟩
  let x0 (k : ℕ) : thirdFullThreeBandZ3GalerkinFiniteState244 (s k) :=
    fun n => u0 n.1
  have hInitialFinite (k : ℕ) :
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (2 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x0 k)) < 100 := by
    have hProj (n : PlIndex244) (hn : n ∈ s k) :
        thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x0 k) n = u0 n := by
      rw [thirdFullThreeBand_z3GalerkinFiniteExtend_on244 (s k) (x0 k) n hn]
    have hBound := thirdFullThreeBand_z3PrescribedInitial_finiteProjectionStrict244
      u0 hSummable hInitial (s k)
    unfold thirdFullThreeBandZ3GalerkinWienerMass244 at hBound ⊢
    calc
      (∑ n ∈ s k, thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n *
        ‖thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x0 k) n‖) =
        ∑ n ∈ s k, thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n * ‖u0 n‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hProj n hn]
      _ < 100 := hBound
  have hEx (k : ℕ) :=
    thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244
      mu a hmu hmuMax (s k) (x0 k) (hInitialFinite k)
  let gamma (k : ℕ) := Classical.choose (hEx k)
  have hSpec (k : ℕ) := Classical.choose_spec (hEx k)
  have hLip (k : ℕ) :
      LipschitzOnWith (51000 : NNReal) (gamma k) (Icc a b) :=
    (hSpec k).2.2.2.1
  have hHigh (k : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (9 / 5 : ℝ))
        (s k) (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (gamma k t)) ≤ 100 :=
    (hSpec k).2.2.2.2.1 t ht
  have hODE (k : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (gamma k)
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu (s k) (gamma k t)) t :=
    (hSpec k).2.1 t ht
  obtain ⟨gC, phi, hStrict, _hConverges, hUniform⟩ :=
    thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244
      a s gamma hLip hHigh
  have hExhaustPhi :
      thirdFullThreeBandZ3GalerkinExhausts244 (fun k => s (phi k)) :=
    thirdFullThreeBand_z3GalerkinExhausts_subsequence244 s hExhaust phi hStrict
  let gT : PlTime244 a → PlIndex244 → PlBand244 := fun t n => gC n t
  let x : (k : ℕ) → PlTime244 a →
      thirdFullThreeBandZ3GalerkinFiniteState244 (s (phi k)) :=
    fun k t => gamma (phi k) t
  let f : ℕ → PlTime244 a → PlIndex244 → PlBand244 :=
    fun k t n => thirdFullThreeBandZ3GalerkinFiniteExtend244
      (s (phi k)) (x k t) n
  have hFiniteHigh (k : ℕ) (t : PlTime244 a) (q : Finset PlIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q (f k t) ≤ 100 :=
    (thirdFullThreeBand_z3Galerkin_zeroExtend_arbitraryFiniteMass_le244
      (Real.log (9 / 5 : ℝ)) (s (phi k)) q (x k t)).trans
      (hHigh (phi k) t t.property)
  obtain ⟨hLimitHigh, hStrong⟩ :=
    thirdFullThreeBand_z3Galerkin_uniformTime_infiniteWienerLimit244
      f (fun n t => gT t n) hFiniteHigh (by
        intro n epsilon hEpsilon
        exact hUniform n epsilon hEpsilon)
  have hLimitFinite (t : PlTime244 a) (q : Finset PlIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q (gT t) ≤ 100 := by
    have hNonneg (n : PlIndex244) :
        0 ≤ thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n *
          ‖gT t n‖ :=
      mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ n).le (norm_nonneg _)
    calc
      thirdFullThreeBandZ3GalerkinWienerMass244
          (Real.log (9 / 5 : ℝ)) q (gT t) ≤
        thirdFullThreeBandZ3InfiniteWienerMass244
          (Real.log (9 / 5 : ℝ)) (gT t) := by
            exact (hLimitHigh t).1.sum_le_tsum q (fun n hn => hNonneg n)
      _ ≤ 100 := (hLimitHigh t).2
  have hMiddleCauchy :=
    thirdFullThreeBand_z3Galerkin_uniformTime_strongWienerCauchy244
      a s gamma hHigh gC phi hUniform
  have hSourceCauchyRaw :=
    thirdFullThreeBand_z3Galerkin_uniformTime_fullLeraySourceCauchy244
      a s gamma phi hHigh hMiddleCauchy
  let source : ℕ → PlTime244 a → PlIndex244 → PlBand244 :=
    fun k t n => thirdFullThreeBandZ3GalerkinQuadratic244
      (s (phi k)) (s (phi k)) (f k t) (f k t) n
  have hSourceCauchy : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : PlTime244 a,
        ∀ q : Finset PlIndex244,
          thirdFullThreeBandZ3GalerkinWienerMass244
            (Real.log (5 / 4 : ℝ)) q
            (fun n => source k t n - source l t n) < epsilon := by
    intro epsilon hEpsilon
    exact hSourceCauchyRaw epsilon hEpsilon
  have hSourceBound (k : ℕ) (t : PlTime244 a) (q : Finset PlIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (5 / 4 : ℝ)) q (source k t) ≤ 50000 :=
    thirdFullThreeBand_z3GalerkinQuadratic_allOutputs50000_244
      (s (phi k)) q (x k t) (hHigh (phi k) t t.property)
  obtain ⟨Q, hModesQ, hQMass, _hQStrong⟩ :=
    thirdFullThreeBand_z3Galerkin_uniformSourceCompletion244
      source hSourceCauchy hSourceBound
  have hQUniform :=
    thirdFullThreeBand_z3UniformSourceCauchy_pointwiseUniform244
      source Q hSourceCauchy hModesQ
  have hIdent : ∀ t : PlTime244 a, ∀ n : PlIndex244,
      Q t n = thirdFullThreeBandZ3InfiniteOrderedLeray244 (gT t) n :=
    thirdFullThreeBand_z3Galerkin_completedSource_eq_orderedLeray244
      (fun k => s (phi k)) x gT Q hExhaustPhi
      (fun k t => hHigh (phi k) t t.property)
      hLimitFinite hStrong hModesQ
  let g : ℝ → PlIndex244 → PlBand244 :=
    fun t n => if ht : t ∈ Icc a b then gT ⟨t, ht⟩ n else 0
  let QE : ℝ → PlIndex244 → PlBand244 :=
    fun t n => if ht : t ∈ Icc a b then Q ⟨t, ht⟩ n else 0
  have hGOn (t : ℝ) (ht : t ∈ Icc a b) :
      g t = gT (⟨t, ht⟩ : PlTime244 a) := by
    funext n
    dsimp only [g]
    rw [dif_pos ht]
  have hQOn (t : ℝ) (ht : t ∈ Icc a b) :
      QE t = Q (⟨t, ht⟩ : PlTime244 a) := by
    funext n
    dsimp only [QE]
    rw [dif_pos ht]
  have hInitialTrace (n : PlIndex244) : g a n = u0 n := by
    have hExN : ∀ᶠ k : ℕ in atTop, n ∈ s (phi k) := hExhaustPhi n
    have hInitEventually : ∀ᶠ k : ℕ in atTop,
        f k z0 n = u0 n := by
      filter_upwards [hExN] with k hk
      change thirdFullThreeBandZ3GalerkinFiniteExtend244
        (s (phi k)) (gamma (phi k) a) n = u0 n
      have hGamma : gamma (phi k) a = x0 (phi k) :=
        (hSpec (phi k)).1
      calc
        thirdFullThreeBandZ3GalerkinFiniteExtend244
            (s (phi k)) (gamma (phi k) a) n =
          thirdFullThreeBandZ3GalerkinFiniteExtend244
            (s (phi k)) (x0 (phi k)) n :=
              congrArg
                (fun y => thirdFullThreeBandZ3GalerkinFiniteExtend244
                  (s (phi k)) y n) hGamma
        _ = u0 n := by
          rw [thirdFullThreeBand_z3GalerkinFiniteExtend_on244
            (s (phi k)) (x0 (phi k)) n hk]
    have hInitTendsto : Tendsto (fun k => f k z0 n) atTop (nhds (u0 n)) := by
      apply Metric.tendsto_atTop.mpr
      intro epsilon hEpsilon
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hInitEventually
      refine ⟨K, ?_⟩
      intro k hk
      simp [hK k hk, hEpsilon]
    have hLimitTendsto : Tendsto (fun k => f k z0 n)
        atTop (nhds (gT z0 n)) := by
      apply Metric.tendsto_atTop.mpr
      intro epsilon hEpsilon
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
        (hUniform n epsilon hEpsilon)
      exact ⟨K, fun k hk => hK k hk z0⟩
    have hValue : gT z0 n = u0 n :=
      tendsto_nhds_unique hLimitTendsto hInitTendsto
    have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
    rw [hGOn a ha]
    simpa only [z0] using hValue
  have hState : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ (t : ℝ) (ht : t ∈ Icc a b),
        dist (f k ⟨t, ht⟩ n) (g t n) < epsilon := by
    intro n epsilon hEpsilon
    filter_upwards [hUniform n epsilon hEpsilon] with k hk t ht
    rw [hGOn t ht]
    exact hk (⟨t, ht⟩ : PlTime244 a)
  have hSourceMode : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ (t : ℝ) (ht : t ∈ Icc a b),
        dist (source k ⟨t, ht⟩ n) (QE t n) < epsilon := by
    intro n epsilon hEpsilon
    filter_upwards [hQUniform n epsilon hEpsilon] with k hk t ht
    rw [hQOn t ht]
    exact hk (⟨t, ht⟩ : PlTime244 a)
  have hIdentity (t : ℝ) (ht : t ∈ Icc a b) (n : PlIndex244) :
      QE t n = thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n := by
    rw [hQOn t ht, hGOn t ht]
    exact hIdent (⟨t, ht⟩ : PlTime244 a) n
  have hEquation := thirdFullThreeBand_z3Galerkin_orderedLerayIntegralEquation244
    mu a s gamma phi g QE hExhaustPhi hLip hODE
    (by
      intro n epsilon hEpsilon
      filter_upwards [hState n epsilon hEpsilon] with k hk t ht
      simpa [f, x] using hk t ht)
    (by
      intro n epsilon hEpsilon
      filter_upwards [hSourceMode n epsilon hEpsilon] with k hk t ht
      simpa [source, f, x] using hk t ht)
    hIdentity
  refine ⟨g, ?_, ?_, hInitialTrace, ?_, ?_⟩
  · intro n
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hEq : (fun t : PlTime244 a => g (t : ℝ) n) =
        (fun t => gC n t) := by
      funext t
      have ht : (t : ℝ) ∈ Icc a b := t.property
      rw [hGOn t ht]
    change Continuous (fun t : PlTime244 a => g (t : ℝ) n)
    rw [hEq]
    exact (gC n).continuous
  · intro t ht
    rw [hGOn t ht]
    exact hLimitHigh (⟨t, ht⟩ : PlTime244 a)
  · intro t ht
    have hQT := hQMass (⟨t, ht⟩ : PlTime244 a)
    have hEq : Q (⟨t, ht⟩ : PlTime244 a) =
        thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) := by
      funext n
      rw [hGOn t ht]
      exact hIdent (⟨t, ht⟩ : PlTime244 a) n
    simpa only [hEq] using hQT
  · intro t ht n
    have hFTC := hEquation t ht n
    rw [hInitialTrace n] at hFTC
    exact hFTC

set_option maxHeartbeats 200000

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinFixedCoreCompactness
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# One common Fourier subsequence by uniform-time Arzelà–Ascoli and Tychonoff

The cutoff-free Galerkin envelope supplies two dimension-independent facts:
pointwise coefficient bounds and 51000 temporal Lipschitz control. The
present module proves the compactness theorem matching those estimates:
for every Z³-indexed sequence of bounded continuous time curves obeying the
same numerical controls, a SINGLE strictly monotone subsequence converges
uniformly on the WHOLE common time interval at EVERY integer frequency.

The proof is not a formal assumption of convergent coordinates: it derives
compactness of the common time-curve class by Arzelà–Ascoli, then takes a
sequentially compact countable product by Tychonoff. The separate interface
mapping actual finite Galerkin zero-extensions into these bounded continuous
functions, and the subsequent strong Wiener and nonlinear limit passages,
remain further proof obligations. No infinite PDE solution is asserted here.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter Metric
noncomputable section

private abbrev DiagonalIndex244 := thirdFullThreeBandZ3Index244
private abbrev DiagonalBand244 := EuclideanSpace ℂ (Fin 3)
private abbrev DiagonalTime244 (a : ℝ) :=
  Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)
private abbrev DiagonalCurve244 (a : ℝ) :=
  BoundedContinuousFunction (DiagonalTime244 a) DiagonalBand244

/-- One COMMON bounded/Lipschitz class for every Fourier coordinate.
Its definition is independent of the Galerkin cutoff and of the frequency. -/
def thirdFullThreeBandZ3GalerkinTimeCompactClass244 (a : ℝ) :
    Set (DiagonalCurve244 a) :=
  {f | LipschitzWith (51000 : NNReal) (fun t => f t) ∧
    ∀ t : DiagonalTime244 a, ‖f t‖ ≤ 100}

/-- The uniform 51000-Lipschitz, 100-bounded class has compact closure
in the SUPREMUM METRIC on continuous time curves. This is exactly the
Arzelà–Ascoli compactness implication needed for Galerkin coefficients. -/
theorem thirdFullThreeBand_z3GalerkinTimeCompactClass_isCompactClosure244
    (a : ℝ) :
    IsCompact (closure (thirdFullThreeBandZ3GalerkinTimeCompactClass244 a)) := by
  classical
  letI : CompactSpace (DiagonalTime244 a) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let A : Set (DiagonalCurve244 a) :=
    thirdFullThreeBandZ3GalerkinTimeCompactClass244 a
  have hRange : ∀ (f : DiagonalCurve244 a) (t : DiagonalTime244 a),
      f ∈ A → f t ∈ Metric.closedBall (0 : DiagonalBand244) 100 := by
    intro f t hf
    change dist (f t) 0 ≤ 100
    simpa only [dist_zero_right] using hf.2 t
  have hEq : Equicontinuous ((↑) : A → DiagonalTime244 a → DiagonalBand244) := by
    intro t
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨ε / 51001, div_pos hε (by norm_num), ?_⟩
    intro v hv f
    have hLip : LipschitzWith (51000 : NNReal)
        (fun z : DiagonalTime244 a => f.1 z) := f.2.1
    have hDist : dist t v < ε / 51001 := by
      simpa only [dist_comm] using hv
    have hDen : (51001 : ℝ) * (ε / 51001) = ε := by
      field_simp
    have hSmall : (51000 : ℝ) * (ε / 51001) < ε := by
      have hp : 0 < ε / 51001 := div_pos hε (by norm_num)
      linarith
    calc
      dist (f.1 t) (f.1 v) ≤ (51000 : ℝ) * dist t v := by
        simpa using hLip.dist_le_mul t v
      _ < (51000 : ℝ) * (ε / 51001) :=
        mul_lt_mul_of_pos_left hDist (by norm_num)
      _ < ε := hSmall
  exact BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : DiagonalBand244) 100)
    (isCompact_closedBall _ _) A hRange hEq

/-- Tychonoff + sequential compactness extracts ONE subsequence of
complete time trajectories, valid SIMULTANEOUSLY at every Fourier mode.
The compact sets may depend on frequency and need not be identical. -/
theorem thirdFullThreeBand_z3Galerkin_countableProduct_subsequence244
    {X : Type*} [PseudoMetricSpace X] [T2Space X]
    (K : DiagonalIndex244 → Set X)
    (hK : ∀ n, IsCompact (K n))
    (f : ℕ → DiagonalIndex244 → X)
    (hf : ∀ k n, f k n ∈ K n) :
    ∃ g : DiagonalIndex244 → X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      ∀ n, Tendsto (fun k => f (φ k) n) atTop (nhds (g n)) := by
  classical
  have hProduct : IsCompact (Set.pi Set.univ K) :=
    isCompact_univ_pi hK
  have hMem (k : ℕ) : f k ∈ Set.pi Set.univ K := by
    intro n _hn
    exact hf k n
  obtain ⟨g, _hg, φ, hφ, hTendsto⟩ :=
    hProduct.tendsto_subseq (x := f) hMem
  refine ⟨g, φ, hφ, ?_⟩
  intro n
  have hEval := (continuous_apply n).continuousAt.tendsto.comp hTendsto
  simpa only [Function.comp_def] using hEval

/-- Genuine UNIFORM-TIME convergence for every frequency, after a
SINGLE diagonal subsequence. The sequence hypotheses are precisely the
dimension-independent coefficient bounds supplied by the finite Galerkin
envelope; no prior convergence or Cauchy property is assumed. -/
theorem thirdFullThreeBand_z3Galerkin_ArzelaDiagonal_uniformTime244
    (a : ℝ)
    (f : ℕ → DiagonalIndex244 → DiagonalCurve244 a)
    (hEnvelope : ∀ k n,
      f k n ∈ thirdFullThreeBandZ3GalerkinTimeCompactClass244 a) :
    ∃ g : DiagonalIndex244 → DiagonalCurve244 a,
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ n, Tendsto (fun k => f (φ k) n) atTop (nhds (g n))) ∧
      (∀ n, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ k in atTop, ∀ t : DiagonalTime244 a,
          dist (f (φ k) n t) (g n t) < ε) := by
  classical
  let K : DiagonalIndex244 → Set (DiagonalCurve244 a) :=
    fun _ => closure (thirdFullThreeBandZ3GalerkinTimeCompactClass244 a)
  have hCompact : ∀ n, IsCompact (K n) := by
    intro n
    exact thirdFullThreeBand_z3GalerkinTimeCompactClass_isCompactClosure244 a
  have hMember : ∀ k n, f k n ∈ K n := by
    intro k n
    exact subset_closure (hEnvelope k n)
  obtain ⟨g, φ, hStrict, hConverges⟩ :=
    thirdFullThreeBand_z3Galerkin_countableProduct_subsequence244
      K hCompact f hMember
  refine ⟨g, φ, hStrict, hConverges, ?_⟩
  intro n ε hε
  have hEventually : ∀ᶠ k in atTop,
      dist (f (φ k) n) (g n) < ε :=
    Filter.eventually_atTop.mpr
      ((Metric.tendsto_atTop.mp (hConverges n)) ε hε)
  filter_upwards [hEventually] with k hk t
  exact (BoundedContinuousFunction.dist_coe_le_dist t).trans_lt hk

/-- Uniform 9/5 Wiener mass controls EACH zero-extended Fourier
coefficient, including modes absent from the given Galerkin cutoff. -/
theorem thirdFullThreeBand_z3Galerkin_zeroExtend_modeNorm100_244
    (s : Finset DiagonalIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hHigh : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) ≤ 100)
    (n : DiagonalIndex244) :
    ‖thirdFullThreeBandZ3GalerkinFiniteExtend244 s x n‖ ≤ 100 := by
  classical
  by_cases hn : n ∈ s
  · rw [thirdFullThreeBand_z3GalerkinFiniteExtend_on244 s x n hn]
    have hState := thirdFullThreeBand_z3GalerkinFiniteState_norm_le_of_Wiener244
      (Real.log (9 / 5 : ℝ)) (Real.log_nonneg (by norm_num))
      s x 100 (by norm_num) hHigh
    exact (norm_le_pi_norm x ⟨n, hn⟩).trans hState
  · rw [thirdFullThreeBand_z3GalerkinFiniteExtend_off244 s x n hn]
    norm_num

/-- Coordinate projection of the finite-state 51000-Lipschitz path
preserves the SAME cutoff-independent modulus after zero extension. -/
theorem thirdFullThreeBand_z3Galerkin_zeroExtend_modeLipschitz244
    (a : ℝ) (s : Finset DiagonalIndex244)
    (gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hLip : LipschitzOnWith (51000 : NNReal) gamma
      (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)))
    (n : DiagonalIndex244) :
    LipschitzOnWith (51000 : NNReal)
      (fun t => thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t) n)
      (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)) := by
  classical
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht v hv
  by_cases hn : n ∈ s
  · rw [thirdFullThreeBand_z3GalerkinFiniteExtend_on244 s (gamma t) n hn,
        thirdFullThreeBand_z3GalerkinFiniteExtend_on244 s (gamma v) n hn]
    calc
      dist ((gamma t) ⟨n, hn⟩) ((gamma v) ⟨n, hn⟩) ≤
          dist (gamma t) (gamma v) := by
            simpa only [NNReal.coe_one, one_mul] using
              (LipschitzWith.eval ⟨n, hn⟩).dist_le_mul (gamma t) (gamma v)
      _ ≤ (51000 : NNReal) * dist t v := hLip.dist_le_mul t ht v hv
  · simp [thirdFullThreeBand_z3GalerkinFiniteExtend_off244 s _ n hn]

/-- Regard an actual zero-extended Galerkin coefficient as a bounded
continuous curve on the common compact time interval. -/
noncomputable def thirdFullThreeBandZ3GalerkinZeroExtendTimeCurve244
    (a : ℝ) (s : Finset DiagonalIndex244)
    (gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hLip : LipschitzOnWith (51000 : NNReal) gamma
      (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)))
    (n : DiagonalIndex244) : DiagonalCurve244 a := by
  classical
  letI : CompactSpace (DiagonalTime244 a) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  have hCont : Continuous
      (fun t : DiagonalTime244 a =>
        thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t) n) :=
    (thirdFullThreeBand_z3Galerkin_zeroExtend_modeLipschitz244
      a s gamma hLip n).continuousOn.domRestrict
  exact BoundedContinuousFunction.mkOfCompact ⟨_, hCont⟩

/-- The actual finite Fourier coordinate belongs to the COMMON
Arzelà–Ascoli class, with no cutoff- or frequency-dependent constant. -/
theorem thirdFullThreeBand_z3Galerkin_zeroExtendTimeCurve_mem244
    (a : ℝ) (s : Finset DiagonalIndex244)
    (gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hLip : LipschitzOnWith (51000 : NNReal) gamma
      (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)))
    (hHigh : ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t)) ≤ 100)
    (n : DiagonalIndex244) :
    thirdFullThreeBandZ3GalerkinZeroExtendTimeCurve244 a s gamma hLip n ∈
      thirdFullThreeBandZ3GalerkinTimeCompactClass244 a := by
  classical
  constructor
  · have hCoord := thirdFullThreeBand_z3Galerkin_zeroExtend_modeLipschitz244
      a s gamma hLip n
    have hRestrict := (lipschitzOnWith_iff_restrict).mp hCoord
    change LipschitzWith (51000 : NNReal)
      (fun t : DiagonalTime244 a =>
        thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t) n)
    exact hRestrict
  · intro t
    change ‖thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma t) n‖ ≤ 100
    exact thirdFullThreeBand_z3Galerkin_zeroExtend_modeNorm100_244
      s (gamma t) (hHigh t t.property) n

/-- The diagonal compactness theorem INSTANTIATED with genuine finite
Galerkin trajectories on arbitrary nonnested cutoffs. The full ODE
solutions and their uniform envelopes can be obtained upstream; no
convergent subsequence is assumed here. -/
theorem thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244
    (a : ℝ) (s : ℕ → Finset DiagonalIndex244)
    (gamma : (k : ℕ) → ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 (s k))
    (hLip : ∀ k, LipschitzOnWith (51000 : NNReal) (gamma k)
      (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)))
    (hHigh : ∀ k, ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (gamma k t)) ≤ 100) :
    ∃ g : DiagonalIndex244 → DiagonalCurve244 a,
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ n, Tendsto
        (fun k => thirdFullThreeBandZ3GalerkinZeroExtendTimeCurve244
          a (s (φ k)) (gamma (φ k)) (hLip (φ k)) n)
          atTop (nhds (g n))) ∧
      (∀ n, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ k in atTop, ∀ t : DiagonalTime244 a,
          dist (thirdFullThreeBandZ3GalerkinFiniteExtend244
            (s (φ k)) (gamma (φ k) t) n) (g n t) < ε) := by
  classical
  let f : ℕ → DiagonalIndex244 → DiagonalCurve244 a :=
    fun k n => thirdFullThreeBandZ3GalerkinZeroExtendTimeCurve244
      a (s k) (gamma k) (hLip k) n
  have hf : ∀ k n, f k n ∈
      thirdFullThreeBandZ3GalerkinTimeCompactClass244 a := by
    intro k n
    exact thirdFullThreeBand_z3Galerkin_zeroExtendTimeCurve_mem244
      a (s k) (gamma k) (hLip k) (hHigh k) n
  obtain ⟨g, φ, hφ, hTendsto, hUniform⟩ :=
    thirdFullThreeBand_z3Galerkin_ArzelaDiagonal_uniformTime244 a f hf
  refine ⟨g, φ, hφ, hTendsto, ?_⟩
  intro n ε hε
  filter_upwards [hUniform n ε hε] with k hk t
  exact hk t

/-- ACTUAL finite-Galerkin existence plus a SINGLE diagonal subsequence,
all constructed from independent initial data on arbitrary Fourier cutoffs.
The initial data need not be mutually compatible; no limit equation is
asserted at this stage. -/
theorem thirdFullThreeBand_z3Galerkin_exists_constructedDiagonalFamily244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : ℕ → Finset DiagonalIndex244)
    (x0 : (k : ℕ) → thirdFullThreeBandZ3GalerkinFiniteState244 (s k))
    (hInitial : ∀ k,
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (2 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x0 k)) < 100) :
    ∃ gamma : (k : ℕ) → ℝ →
        thirdFullThreeBandZ3GalerkinFiniteState244 (s k),
      (∀ k, gamma k a = x0 k ∧
        ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
          HasDerivAt (gamma k)
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu (s k) (gamma k t)) t) ∧
      ∃ g : DiagonalIndex244 → DiagonalCurve244 a,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ n, ∀ ε : ℝ, 0 < ε →
          ∀ᶠ k in atTop, ∀ t : DiagonalTime244 a,
            dist (thirdFullThreeBandZ3GalerkinFiniteExtend244
              (s (φ k)) (gamma (φ k) t) n) (g n t) < ε) := by
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
  obtain ⟨g, φ, hφ, _hModeTendsto, hUniform⟩ :=
    thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244
      a s gamma hLip hHigh
  refine ⟨gamma, ?_, g, φ, hφ, hUniform⟩
  intro k
  exact ⟨(hSpec k).1, (hSpec k).2.1⟩

end
end PrimeTensor.FirstMonomialTriad

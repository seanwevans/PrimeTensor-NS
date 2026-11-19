import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3LongitudinalHeatRigidity
import Mathlib.Tactic

/-!
# Solenoidal propagation for the *constructed* infinite Z³ Fourier flow

The exact Galerkin nonlinear source is Leray-projected.  At every finite
cutoff its longitudinal coefficient therefore obeys a homogeneous heat ODE.
Gronwall and projected initial data force every retained coefficient to be
transverse for the entire common time interval.  The actual Arzelà subsequence
is shared with the source completion and the infinite Fourier integral equation;
uniform coefficient convergence transfers this exact constraint to the limit.

Unlike the prior longitudinal rigidity result, the final existence theorem
requires NO differentiability premise for the infinite limit field and NO
assumed continuity of the completed infinite source.  This local periodic
complex Fourier result is not physical R³ H³ global regularity or Hermitian
reality; the Hermitian invariant subspace is a separate next direction.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev PlIndex244 := thirdFullThreeBandZ3Index244
private abbrev PlBand244 := EuclideanSpace ℂ (Fin 3)
private abbrev PlTime244 (a : ℝ) :=
  Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)

/-- The genuine finite Galerkin ODE preserves the output-frequency
Leray constraint.  This statement assumes only a transverse finite initial
state, not that the solution stays transverse. -/
theorem thirdFullThreeBand_z3GalerkinFiniteODE_transversePreserved244
    (mu a b : ℝ) (hmu : 0 ≤ mu)
    (s : Finset PlIndex244)
    (gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ r ∈ Icc a b,
      HasDerivAt gamma
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma r)) r)
    (hInitial : ∀ n ∈ s,
      thirdFullThreeBandZ3FourierIsTransverse244 n
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma a) n))
    (n : PlIndex244) (hn : n ∈ s) :
    ∀ r ∈ Icc a b,
      thirdFullThreeBandZ3FourierIsTransverse244 n
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma r) n) := by
  let xi := thirdFullThreeBandZ3ComplexFrequency244 n
  let lambda : ℝ := mu * ‖xi‖ ^ 2
  let v : ℝ → PlBand244 := fun r =>
    thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma r) n
  let L : PlBand244 →L[ℝ] ℂ := ((innerSL ℂ) xi).restrictScalars ℝ
  let w : ℝ → ℂ := fun r => L (v r)
  have hCoord (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivAt v
        (thirdFullThreeBandZ3GalerkinNSField244 mu s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma r)) n) r := by
    exact thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_hasDerivAt244
      mu s gamma r (hODE r hr) n hn
  have hContV : ContinuousOn v (Icc a b) := by
    intro r hr
    exact (hCoord r hr).continuousAt.continuousWithinAt
  have hContW : ContinuousOn w (Icc a b) :=
    L.continuous.comp_continuousOn hContV
  have hInitialW : w a = 0 := by
    exact hInitial n hn
  have hLam : 0 ≤ lambda := mul_nonneg hmu (sq_nonneg _)
  have hHeat (r : ℝ) :
      L (thirdFullThreeBandZ3GalerkinNSField244 mu s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma r)) n) =
      (-lambda) • L (v r) := by
    change L ((-lambda) • v r +
      thirdFullThreeBandZ3GalerkinQuadratic244 s s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma r))
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma r)) n) = _
    rw [map_add, map_smul]
    have hQ : L (thirdFullThreeBandZ3GalerkinQuadratic244 s s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma r))
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma r)) n) = 0 := by
      exact thirdFullThreeBand_z3GalerkinQuadratic_transverse244 s s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma r))
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma r)) n
    rw [hQ, add_zero]
  have hDerivW : ∀ r ∈ Ico a b,
      HasDerivAt w ((-lambda) • w r) r := by
    intro r hr
    have hComp := L.hasFDerivAt.comp_hasDerivAt r
      (hCoord r ⟨hr.1, hr.2.le⟩)
    change HasDerivAt w
      (L (thirdFullThreeBandZ3GalerkinNSField244 mu s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma r)) n)) r at hComp
    rw [hHeat r] at hComp
    exact hComp
  exact thirdFullThreeBand_z3LongitudinalHeat_scalarRigidity244
    a b lambda hLam w hContW hInitialW hDerivW

/-- Frequencywise uniform convergence of a common exhaustive subsequence
preserves the exact closed longitudinal constraint, even if no derivative
of the infinite limit has yet been constructed. -/
theorem thirdFullThreeBand_z3Galerkin_uniformLimit_transverse244
    (a b : ℝ) (s : ℕ → Finset PlIndex244)
    (gamma : (j : ℕ) → ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 (s j))
    (phi : ℕ → ℕ) (g : ℝ → PlIndex244 → PlBand244)
    (hExhaust : thirdFullThreeBandZ3GalerkinExhausts244 (fun k => s (phi k)))
    (hFinite : ∀ k (n : PlIndex244) (hn : n ∈ s (phi k)),
      ∀ r ∈ Icc a b,
        thirdFullThreeBandZ3FourierIsTransverse244 n
          (thirdFullThreeBandZ3GalerkinFiniteExtend244
            (s (phi k)) (gamma (phi k) r) n))
    (hUniform : ∀ n, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ r ∈ Icc a b,
        dist (thirdFullThreeBandZ3GalerkinFiniteExtend244
          (s (phi k)) (gamma (phi k) r) n) (g r n) < epsilon) :
    ∀ r ∈ Icc a b, ∀ n : PlIndex244,
      thirdFullThreeBandZ3FourierIsTransverse244 n (g r n) := by
  intro r hr n
  let xi := thirdFullThreeBandZ3ComplexFrequency244 n
  let f : ℕ → PlBand244 := fun k =>
    thirdFullThreeBandZ3GalerkinFiniteExtend244
      (s (phi k)) (gamma (phi k) r) n
  have hMode : Tendsto f atTop (nhds (g r n)) := by
    apply Metric.tendsto_atTop.mpr
    intro epsilon hEpsilon
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hUniform n epsilon hEpsilon)
    exact ⟨K, fun k hk => hK k hk r hr⟩
  have hPair : Tendsto (fun k => inner ℂ xi (f k)) atTop
      (nhds (inner ℂ xi (g r n))) :=
    (((innerSL ℂ) xi).continuous.tendsto (g r n)).comp hMode
  have hZero : ∀ᶠ k : ℕ in atTop, inner ℂ xi (f k) = 0 := by
    filter_upwards [hExhaust n] with k hk
    exact hFinite k n hk r hr
  have hPairZero : Tendsto (fun k => inner ℂ xi (f k)) atTop
      (nhds (0 : ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hZero] with k hk
    exact hk.symm
  exact tendsto_nhds_unique hPair hPairZero

set_option maxHeartbeats 1500000

/-- A genuine LOCAL Fourier Navier--Stokes solution from arbitrary analytic
initial data after Leray projection, now with divergence-free velocity
at EVERY time of the common existence interval.  The proof uses the same
finite ODE family, Arzelà subsequence, infinite source identification, and
integral evolution; the solenoidal property is NOT a premise on the limit. -/
theorem thirdFullThreeBand_z3ProjectedInitial_solenoidalLocalExistence244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : ℕ → Finset PlIndex244)
    (hExhaust : thirdFullThreeBandZ3GalerkinExhausts244 s)
    (uInitial : PlIndex244 → PlBand244)
    (hSummable : Summable (fun n : PlIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n * ‖uInitial n‖))
    (hInitial : thirdFullThreeBandZ3InfiniteWienerMass244
      (Real.log (2 : ℝ)) uInitial < 100) :
    ∃ g : ℝ → PlIndex244 → PlBand244,
      (∀ n, ContinuousOn (fun t => g t n)
        (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a))) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        Summable (fun n : PlIndex244 =>
          thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n * ‖g t n‖) ∧
        thirdFullThreeBandZ3InfiniteWienerMass244
          (Real.log (9 / 5 : ℝ)) (g t) ≤ 100) ∧
      (∀ n, g a n = thirdFullThreeBandZ3ProjectedInitial244 uInitial n) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        Summable (fun n : PlIndex244 =>
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
            ‖thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n‖) ∧
        thirdFullThreeBandZ3InfiniteWienerMass244
          (Real.log (5 / 4 : ℝ))
          (thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t)) ≤ 50000) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        ∀ n : PlIndex244,
          thirdFullThreeBandZ3FourierIsTransverse244 n (g t n)) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        ∀ n : PlIndex244,
          g t n - thirdFullThreeBandZ3ProjectedInitial244 uInitial n =
            ∫ r in a..t,
              (-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
                g r n + thirdFullThreeBandZ3InfiniteOrderedLeray244 (g r) n) := by
  classical
  obtain ⟨hProjectedSum, hProjectedMass⟩ :=
    thirdFullThreeBand_z3ProjectedInitial_admissible244
      uInitial hSummable hInitial
  let u0 : PlIndex244 → PlBand244 :=
    thirdFullThreeBandZ3ProjectedInitial244 uInitial
  have hSummable : Summable (fun n : PlIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n * ‖u0 n‖) :=
    hProjectedSum
  have hInitial : thirdFullThreeBandZ3InfiniteWienerMass244
      (Real.log (2 : ℝ)) u0 < 100 := hProjectedMass
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
  have hInitialFiniteTrans (j : ℕ) (n : PlIndex244) (hn : n ∈ s j) :
      thirdFullThreeBandZ3FourierIsTransverse244 n
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s j) (gamma j a) n) := by
    have hGamma : gamma j a = x0 j := (hSpec j).1
    have hAt : thirdFullThreeBandZ3GalerkinFiniteExtend244
        (s j) (gamma j a) n = u0 n := by
      rw [hGamma, thirdFullThreeBand_z3GalerkinFiniteExtend_on244 (s j) (x0 j) n hn]
    rw [hAt]
    exact thirdFullThreeBand_z3ProjectedInitial_transverse244 uInitial n
  have hFiniteTrans (k : ℕ) (n : PlIndex244) (hn : n ∈ s (phi k))
      (r : ℝ) (hr : r ∈ Icc a b) :
      thirdFullThreeBandZ3FourierIsTransverse244 n
        (thirdFullThreeBandZ3GalerkinFiniteExtend244
          (s (phi k)) (gamma (phi k) r) n) := by
    exact thirdFullThreeBand_z3GalerkinFiniteODE_transversePreserved244
      mu a b hmu (s (phi k)) (gamma (phi k))
      (hODE (phi k)) (hInitialFiniteTrans (phi k)) n hn r hr
  have hTransverseLimit : ∀ r ∈ Icc a b, ∀ n : PlIndex244,
      thirdFullThreeBandZ3FourierIsTransverse244 n (g r n) := by
    apply thirdFullThreeBand_z3Galerkin_uniformLimit_transverse244
      a b s gamma phi g hExhaustPhi hFiniteTrans
    intro n epsilon hEpsilon
    filter_upwards [hState n epsilon hEpsilon] with k hk r hr
    simpa [f, x] using hk r hr
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
  refine ⟨g, ?_, ?_, hInitialTrace, ?_, hTransverseLimit, ?_⟩
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

/-- A concrete standard-cube local Fourier solution, with the full
Navier--Stokes integral equation AND the longitudinal constraint proved
from the finite ODE construction rather than assumed on the limit. -/
theorem thirdFullThreeBand_z3FixedCubes_solenoidalLocalExistence244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (uInitial : PlIndex244 → PlBand244)
    (hSummable : Summable (fun n : PlIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n * ‖uInitial n‖))
    (hInitial : thirdFullThreeBandZ3InfiniteWienerMass244
      (Real.log (2 : ℝ)) uInitial < 100) :
    ∃ g : ℝ → PlIndex244 → PlBand244,
      (∀ n, g a n = thirdFullThreeBandZ3ProjectedInitial244 uInitial n) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        ∀ n : PlIndex244, thirdFullThreeBandZ3FourierIsTransverse244 n (g t n)) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        ∀ n : PlIndex244,
          g t n - thirdFullThreeBandZ3ProjectedInitial244 uInitial n =
            ∫ r in a..t,
              (-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
                g r n + thirdFullThreeBandZ3InfiniteOrderedLeray244 (g r) n) := by
  obtain ⟨g, _hCont, _hHigh, hTrace, _hSource, hTrans, hEq⟩ :=
    thirdFullThreeBand_z3ProjectedInitial_solenoidalLocalExistence244
      mu a hmu hmuMax
      (fun k => thirdFullThreeBandZ3GalerkinFixedCoreCube244 k)
      thirdFullThreeBand_z3GalerkinFixedCubes_exhaust244
      uInitial hSummable hInitial
  exact ⟨g, hTrace, hTrans, hEq⟩

set_option maxHeartbeats 200000

end
end PrimeTensor.FirstMonomialTriad

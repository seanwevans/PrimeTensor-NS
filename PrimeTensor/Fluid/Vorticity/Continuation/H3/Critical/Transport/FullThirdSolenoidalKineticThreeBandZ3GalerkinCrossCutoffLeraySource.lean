import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinInfiniteWienerLimit
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinStrongTemporalFTC
import Mathlib.Tactic

/-!
# Genuine Z³ Leray source stability across unrelated Galerkin cutoffs

The constructed infinite Wiener limit has strong W_log(3/2) approximation
on a common time interval. To pass the exact Navier--Stokes Fourier equation
to the limit, the COMPLETE Leray source must also converge, not merely an
abstract scalar majorant.

This module proves that the original complex Leray interaction vanishes if
either Fourier input vanishes; hence zero-extension from an arbitrary finite
cutoff does not change its full quadratic source at ANY output frequency.
Enlarging two unrelated cutoffs to their union allows the already-proved
1000-Lipschitz quadratic estimate to compare their actual full sources,
with arbitrary finite output sets and NO loss proportional to the output
cardinality. Adding viscosity gives the exact 1010 full-vector-field bound.

The uniform W_log(3/2) Cauchy estimate for actual strong Galerkin trajectories
then implies uniform-in-time Cauchy convergence in W_log(5/4) of the complete
projected quadratic sources, simultaneously on ALL finite output sets.
The same holds for the full viscous-plus-Leray fields on union supports.

These theorems DO NOT yet construct the infinite source as a complete-space
limit, or pass the time integral / derivative to the infinite equation.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

private abbrev CLIndex244 := thirdFullThreeBandZ3Index244
private abbrev CLBand244 := EuclideanSpace ℂ (Fin 3)
private abbrev CLTime244 (a : ℝ) :=
  Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)

/-- The physical ordered Leray interaction is zero when the advecting
coefficient vanishes, for every Fourier output and transported mode. -/
theorem thirdFullThreeBand_z3ComplexTransport_zeroLeft244
    (n q : CLIndex244) (v : CLBand244) :
    thirdFullThreeBandZ3ComplexTransport244 n q 0 v = 0 := by
  simp [thirdFullThreeBandZ3ComplexTransport244]

/-- The same complete complex Leray interaction vanishes when the
transported coefficient is zero. -/
theorem thirdFullThreeBand_z3ComplexTransport_zeroRight244
    (n q : CLIndex244) (u : CLBand244) :
    thirdFullThreeBandZ3ComplexTransport244 n q u 0 = 0 := by
  simp [thirdFullThreeBandZ3ComplexTransport244]

/-- Enlarge BOTH finite convolution input sets by arbitrary extra modes.
If the input field vanishes off the smaller cutoff, every new ordered pair
vanishes, including at output modes outside the original cutoff.
Crucially no assumption is made that the output mode belongs to either set. -/
theorem thirdFullThreeBand_z3GalerkinQuadratic_enlargeZeroSupport244
    (s q : Finset CLIndex244) (hsq : s ⊆ q)
    (u : CLIndex244 → CLBand244)
    (hu : ∀ n, n ∉ s → u n = 0)
    (n : CLIndex244) :
    thirdFullThreeBandZ3GalerkinQuadratic244 q q u u n =
      thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n := by
  classical
  unfold thirdFullThreeBandZ3GalerkinQuadratic244
  calc
    (∑ p ∈ q, ∑ z ∈ q,
      if p + z = n then
        thirdFullThreeBandZ3ComplexTransport244 n z (u p) (u z)
      else 0) =
      ∑ p ∈ s, ∑ z ∈ q,
        if p + z = n then
          thirdFullThreeBandZ3ComplexTransport244 n z (u p) (u z)
        else 0 := by
          symm
          apply Finset.sum_subset hsq
          intro p hpq hps
          rw [hu p hps]
          simp [thirdFullThreeBand_z3ComplexTransport_zeroLeft244]
    _ = ∑ p ∈ s, ∑ z ∈ s,
        if p + z = n then
          thirdFullThreeBandZ3ComplexTransport244 n z (u p) (u z)
        else 0 := by
          apply Finset.sum_congr rfl
          intro p hps
          symm
          apply Finset.sum_subset hsq
          intro z hzq hzs
          rw [hu z hzs]
          simp [thirdFullThreeBand_z3ComplexTransport_zeroRight244]

/-- Two unrelated cutoffs have a COMMON full Leray source after their
coefficients are zero-extended. Any finite output set is allowed, including
frequencies omitted by both cutoffs. The exact quadratic source, not a
surrogate convolution, is 1000-Lipschitz from W_(3/2) to W_(5/4). -/
theorem thirdFullThreeBand_z3GalerkinTwoCutoff_sourceLipschitz1000_244
    (outputs s t : Finset CLIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (y : thirdFullThreeBandZ3GalerkinFiniteState244 t)
    (hX : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) ≤ 100)
    (hY : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) t
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 t y) ≤ 100) :
    (∑ n ∈ outputs, thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
      ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x)
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) n -
        thirdFullThreeBandZ3GalerkinQuadratic244 t t
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 t y)
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 t y) n‖) ≤
      1000 * thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) (s ∪ t)
        (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 s x n -
          thirdFullThreeBandZ3GalerkinFiniteExtend244 t y n) := by
  classical
  let big := s ∪ t
  let u := thirdFullThreeBandZ3GalerkinFiniteExtend244 s x
  let v := thirdFullThreeBandZ3GalerkinFiniteExtend244 t y
  have hu (n : CLIndex244) (hn : n ∉ s) : u n = 0 :=
    thirdFullThreeBand_z3GalerkinFiniteExtend_off244 s x n hn
  have hv (n : CLIndex244) (hn : n ∉ t) : v n = 0 :=
    thirdFullThreeBand_z3GalerkinFiniteExtend_off244 t y n hn
  have hQu (n : CLIndex244) :
      thirdFullThreeBandZ3GalerkinQuadratic244 big big u u n =
        thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n :=
    thirdFullThreeBand_z3GalerkinQuadratic_enlargeZeroSupport244
      s big Finset.subset_union_left u hu n
  have hQv (n : CLIndex244) :
      thirdFullThreeBandZ3GalerkinQuadratic244 big big v v n =
        thirdFullThreeBandZ3GalerkinQuadratic244 t t v v n :=
    thirdFullThreeBand_z3GalerkinQuadratic_enlargeZeroSupport244
      t big Finset.subset_union_right v hv n
  have hBigU : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) big u ≤ 100 := by
    rw [thirdFullThreeBand_z3GalerkinWiener_zeroExtend_superset244
      (Real.log (9 / 5 : ℝ)) s big Finset.subset_union_left x]
    exact hX
  have hBigV : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) big v ≤ 100 := by
    rw [thirdFullThreeBand_z3GalerkinWiener_zeroExtend_superset244
      (Real.log (9 / 5 : ℝ)) t big Finset.subset_union_right y]
    exact hY
  have hRadius : Real.log (3 / 2 : ℝ) ≤ Real.log (9 / 5 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hMidU : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) big u ≤ 100 :=
    (thirdFullThreeBand_z3WienerMass_radius_mono244
      _ _ hRadius big u).trans hBigU
  have hMidV : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) big v ≤ 100 :=
    (thirdFullThreeBand_z3WienerMass_radius_mono244
      _ _ hRadius big v).trans hBigV
  have hSource := thirdFullThreeBand_z3GalerkinSourceDiff_1000_lower244
    outputs big u v hMidU hMidV
  simp only [hQu, hQv] at hSource
  exact hSource

/-- The exact viscous-plus-projected-Leray vector fields on two unrelated
finite cutoffs admit a 1010 comparison on their union support; no cutoff
size or omitted mode appears. In particular the viscosity coefficient is
the SAME on both sides. -/
theorem thirdFullThreeBand_z3GalerkinTwoCutoff_fullFieldLipschitz1010_244
    (mu : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s t : Finset CLIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (y : thirdFullThreeBandZ3GalerkinFiniteState244 t)
    (hX : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) ≤ 100)
    (hY : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) t
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 t y) ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (5 / 4 : ℝ))
      (s ∪ t)
      (fun n => thirdFullThreeBandZ3GalerkinNSField244 mu s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) n -
        thirdFullThreeBandZ3GalerkinNSField244 mu t
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 t y) n) ≤
      1010 * thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) (s ∪ t)
        (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 s x n -
          thirdFullThreeBandZ3GalerkinFiniteExtend244 t y n) := by
  classical
  let big := s ∪ t
  let u := thirdFullThreeBandZ3GalerkinFiniteExtend244 s x
  let v := thirdFullThreeBandZ3GalerkinFiniteExtend244 t y
  have hu (n : CLIndex244) (hn : n ∉ s) : u n = 0 :=
    thirdFullThreeBand_z3GalerkinFiniteExtend_off244 s x n hn
  have hv (n : CLIndex244) (hn : n ∉ t) : v n = 0 :=
    thirdFullThreeBand_z3GalerkinFiniteExtend_off244 t y n hn
  have hQu (n : CLIndex244) :
      thirdFullThreeBandZ3GalerkinQuadratic244 big big u u n =
        thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n :=
    thirdFullThreeBand_z3GalerkinQuadratic_enlargeZeroSupport244
      s big Finset.subset_union_left u hu n
  have hQv (n : CLIndex244) :
      thirdFullThreeBandZ3GalerkinQuadratic244 big big v v n =
        thirdFullThreeBandZ3GalerkinQuadratic244 t t v v n :=
    thirdFullThreeBand_z3GalerkinQuadratic_enlargeZeroSupport244
      t big Finset.subset_union_right v hv n
  have hFu (n : CLIndex244) :
      thirdFullThreeBandZ3GalerkinNSField244 mu big u n =
        thirdFullThreeBandZ3GalerkinNSField244 mu s u n := by
    simp only [thirdFullThreeBandZ3GalerkinNSField244, hQu]
  have hFv (n : CLIndex244) :
      thirdFullThreeBandZ3GalerkinNSField244 mu big v n =
        thirdFullThreeBandZ3GalerkinNSField244 mu t v n := by
    simp only [thirdFullThreeBandZ3GalerkinNSField244, hQv]
  have hBigU : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) big u ≤ 100 := by
    rw [thirdFullThreeBand_z3GalerkinWiener_zeroExtend_superset244
      (Real.log (9 / 5 : ℝ)) s big Finset.subset_union_left x]
    exact hX
  have hBigV : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) big v ≤ 100 := by
    rw [thirdFullThreeBand_z3GalerkinWiener_zeroExtend_superset244
      (Real.log (9 / 5 : ℝ)) t big Finset.subset_union_right y]
    exact hY
  have hBound := thirdFullThreeBand_z3GalerkinNSField_Lipschitz1010_highBall244
    mu hmu hmuMax big u v hBigU hBigV
  simp only [hFu, hFv] at hBound
  exact hBound

/-- Along any Galerkin subsequence already proved uniformly Cauchy in the
middle Wiener norm, the ACTUAL complete Leray source is Cauchy, uniformly
on the closed time interval AND simultaneously over every finite set of
output frequencies. This is the spatial limit passage; no output cutoff
or operator-norm dimension factor appears in the estimate. -/
theorem thirdFullThreeBand_z3Galerkin_uniformTime_fullLeraySourceCauchy244
    (a : ℝ) (s : ℕ → Finset CLIndex244)
    (gamma : (k : ℕ) → ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 (s k))
    (φ : ℕ → ℕ)
    (hHigh : ∀ k, ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (gamma k t)) ≤ 100)
    (hCauchy : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : CLTime244 a,
        thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
          (s (φ k) ∪ s (φ l))
          (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
              (gamma (φ k) t) n -
            thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ l))
              (gamma (φ l) t) n) < epsilon) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : CLTime244 a,
        ∀ outputs : Finset CLIndex244,
          (∑ n ∈ outputs,
            thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
              ‖thirdFullThreeBandZ3GalerkinQuadratic244
                  (s (φ k)) (s (φ k))
                  (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
                    (gamma (φ k) t))
                  (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
                    (gamma (φ k) t)) n -
                thirdFullThreeBandZ3GalerkinQuadratic244
                  (s (φ l)) (s (φ l))
                  (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ l))
                    (gamma (φ l) t))
                  (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ l))
                    (gamma (φ l) t)) n‖) < epsilon := by
  intro epsilon hEpsilon
  have hSmall : 0 < epsilon / 1000 := by positivity
  obtain ⟨K, hK⟩ := hCauchy (epsilon / 1000) hSmall
  refine ⟨K, ?_⟩
  intro k hk l hl z outputs
  have hQ := thirdFullThreeBand_z3GalerkinTwoCutoff_sourceLipschitz1000_244
    outputs (s (φ k)) (s (φ l))
    (gamma (φ k) z) (gamma (φ l) z)
    (hHigh (φ k) z z.property) (hHigh (φ l) z z.property)
  have hW := hK k hk l hl z
  exact lt_of_le_of_lt hQ (by nlinarith)

/-- The complete finite NS vector fields (viscosity AND full Leray source)
are uniformly Cauchy at the lower analytic radius on each union support.
Unlike the source-only theorem, the field is evaluated on retained output
modes, where the finite Galerkin ODE actually lives. -/
theorem thirdFullThreeBand_z3Galerkin_uniformTime_fullNSFieldCauchy244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : ℕ → Finset CLIndex244)
    (gamma : (k : ℕ) → ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 (s k))
    (φ : ℕ → ℕ)
    (hHigh : ∀ k, ∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (gamma k t)) ≤ 100)
    (hCauchy : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : CLTime244 a,
        thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
          (s (φ k) ∪ s (φ l))
          (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
              (gamma (φ k) t) n -
            thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ l))
              (gamma (φ l) t) n) < epsilon) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : CLTime244 a,
        thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (5 / 4 : ℝ))
          (s (φ k) ∪ s (φ l))
          (fun n => thirdFullThreeBandZ3GalerkinNSField244 mu (s (φ k))
              (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ k))
                (gamma (φ k) t)) n -
            thirdFullThreeBandZ3GalerkinNSField244 mu (s (φ l))
              (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s (φ l))
                (gamma (φ l) t)) n) < epsilon := by
  intro epsilon hEpsilon
  have hSmall : 0 < epsilon / 1010 := by positivity
  obtain ⟨K, hK⟩ := hCauchy (epsilon / 1010) hSmall
  refine ⟨K, ?_⟩
  intro k hk l hl z
  have hF := thirdFullThreeBand_z3GalerkinTwoCutoff_fullFieldLipschitz1010_244
    mu hmu hmuMax (s (φ k)) (s (φ l))
    (gamma (φ k) z) (gamma (φ l) z)
    (hHigh (φ k) z z.property) (hHigh (φ l) z z.property)
  have hW := hK k hk l hl z
  exact lt_of_le_of_lt hF (by nlinarith)


/-- From independent initial data on arbitrary nonnested Fourier cutoffs,
construct actual strong finite Galerkin ODE solutions, extract a common
Fourier subsequence, and derive uniform-time Cauchy convergence of the
COMPLETE projected Leray source at ALL output frequencies simultaneously.
The output set is universally quantified AFTER the Cauchy threshold. -/
theorem thirdFullThreeBand_z3Galerkin_exists_constructedFullLeraySourceCauchy244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : ℕ → Finset CLIndex244)
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
        (∀ epsilon : ℝ, 0 < epsilon →
          ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ z : CLTime244 a,
            ∀ outputs : Finset CLIndex244,
              (∑ n ∈ outputs,
                thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
                  ‖thirdFullThreeBandZ3GalerkinQuadratic244
                      (s (φ k)) (s (φ k))
                      (thirdFullThreeBandZ3GalerkinFiniteExtend244
                        (s (φ k)) (gamma (φ k) z))
                      (thirdFullThreeBandZ3GalerkinFiniteExtend244
                        (s (φ k)) (gamma (φ k) z)) n -
                    thirdFullThreeBandZ3GalerkinQuadratic244
                      (s (φ l)) (s (φ l))
                      (thirdFullThreeBandZ3GalerkinFiniteExtend244
                        (s (φ l)) (gamma (φ l) z))
                      (thirdFullThreeBandZ3GalerkinFiniteExtend244
                        (s (φ l)) (gamma (φ l) z)) n‖) < epsilon) := by
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
  have hHigh (k : ℕ) (z : ℝ)
      (hz : z ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (gamma k z)) ≤ 100 :=
    (hSpec k).2.2.2.2.1 z hz
  obtain ⟨g, φ, hStrict, _hMode, hUniform⟩ :=
    thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244
      a s gamma hLip hHigh
  have hCauchy := thirdFullThreeBand_z3Galerkin_uniformTime_strongWienerCauchy244
    a s gamma hHigh g φ hUniform
  have hSource := thirdFullThreeBand_z3Galerkin_uniformTime_fullLeraySourceCauchy244
    a s gamma φ hHigh hCauchy
  refine ⟨gamma, ?_, φ, hStrict, hSource⟩
  intro k
  exact ⟨(hSpec k).1, (hSpec k).2.1⟩

end
end PrimeTensor.FirstMonomialTriad

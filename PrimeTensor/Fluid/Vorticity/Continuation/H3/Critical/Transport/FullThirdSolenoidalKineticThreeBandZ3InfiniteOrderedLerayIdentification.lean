import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinInfiniteLeraySourceLimit
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
# Identifying the completed Fourier source with the infinite ordered Leray convolution

The earlier module constructed a completed source as the uniform strong Wiener
limit of the FULL finite Leray sources. This module proves that the physical
ordered convolution is absolutely summable for any high-radius Wiener field,
and that finite Galerkin convolutions of that field converge to its actual
infinite ordered convolution along exhaustive (not necessarily nested) cutoffs.

The final identification uses the already proved 1000-Lipschitz source
stability and strong convergence of Galerkin states. Exhaustion of the cutoffs
is an explicit hypothesis: without it the limiting source can omit modes.
This module does NOT claim a time-integrated PDE or a global continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

private abbrev OqIndex244 := thirdFullThreeBandZ3Index244
private abbrev OqBand244 := EuclideanSpace ℂ (Fin 3)
private abbrev OqTime244 (a : ℝ) :=
  Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)

/-- The infinite Fourier Leray convolution at the exact output frequency.
Here the partner of p is n-p, so every collision and ordered pair occurs
once, with the physical complex Leray projector at n. -/
noncomputable def thirdFullThreeBandZ3InfiniteOrderedLeray244
    (u : OqIndex244 → OqBand244) (n : OqIndex244) : OqBand244 :=
  ∑' p : OqIndex244,
    thirdFullThreeBandZ3ComplexTransport244 n (n - p) (u p) (u (n - p))

/-- A 9/5 Wiener bound controls the sum of UNWEIGHTED Fourier amplitudes.
The argument works for any Fourier field, not just finitely supported ones. -/
theorem thirdFullThreeBand_z3InfiniteWiener_unweightedSummable244
    (u : OqIndex244 → OqBand244)
    (hHigh : ∀ q : Finset OqIndex244,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q u ≤ 100) :
    Summable (fun p : OqIndex244 => ‖u p‖) := by
  classical
  apply summable_of_sum_le (fun p => norm_nonneg (u p))
  intro q
  calc
    (∑ p ∈ q, ‖u p‖) ≤
        ∑ p ∈ q,
          thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) p * ‖u p‖ := by
            apply Finset.sum_le_sum
            intro p hp
            have hw := thirdFullThreeBand_z3GalerkinWeight_one_le244
              (Real.log (9 / 5 : ℝ)) (Real.log_nonneg (by norm_num)) p
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hw (norm_nonneg (u p))
    _ ≤ 100 := hHigh q

/-- At every frequency a high-radius 100-ball pays the FULL derivative
of the transported Fourier coefficient. There is no dependence on n. -/
theorem thirdFullThreeBand_z3InfiniteWiener_frequencyAmplitude500_244
    (u : OqIndex244 → OqBand244)
    (hHigh : ∀ q : Finset OqIndex244,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q u ≤ 100)
    (q : OqIndex244) :
    ‖thirdFullThreeBandZ3ComplexFrequency244 q‖ * ‖u q‖ ≤ 500 := by
  have hDegree := thirdFullThreeBand_z3ComplexFrequency_norm_le_degree244 q
  have hPosDegree := thirdFullThreeBand_z3Degree_nonneg244 q
  have hMiddle := thirdFullThreeBand_z3GalerkinWeight_one_le244
    (Real.log (3 / 2 : ℝ)) (Real.log_nonneg (by norm_num)) q
  have hBridge : thirdFullThreeBandZ3Degree244 q ≤
      thirdFullThreeBandZ3Degree244 q *
        thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hMiddle hPosDegree
  have hReserve := thirdFullThreeBand_z3ThreeRadiusDerivativeEnvelope244 q
  have hOne : thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) q *
      ‖u q‖ ≤ 100 := by
    simpa [thirdFullThreeBandZ3GalerkinWienerMass244] using
      hHigh ({q} : Finset OqIndex244)
  calc
    _ ≤ (5 * thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) q) *
          ‖u q‖ :=
      mul_le_mul_of_nonneg_right ((hDegree.trans hBridge).trans hReserve)
        (norm_nonneg (u q))
    _ = 5 * (thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) q *
          ‖u q‖) := by ring
    _ ≤ 5 * 100 := mul_le_mul_of_nonneg_left hOne (by norm_num)
    _ = 500 := by norm_num

/-- The complete ordered Fourier series is ABSOLUTELY summable at every
output mode, not merely defined through a limit of Galerkin cutoffs. -/
theorem thirdFullThreeBand_z3InfiniteOrderedLeray_summable244
    (u : OqIndex244 → OqBand244)
    (hHigh : ∀ q : Finset OqIndex244,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q u ≤ 100)
    (n : OqIndex244) :
    Summable (fun p : OqIndex244 =>
      thirdFullThreeBandZ3ComplexTransport244 n (n - p) (u p) (u (n - p))) := by
  have hAmp := thirdFullThreeBand_z3InfiniteWiener_unweightedSummable244
    u hHigh
  apply Summable.of_norm_bounded (hAmp.mul_left 500)
  intro p
  calc
    ‖thirdFullThreeBandZ3ComplexTransport244 n (n - p)
        (u p) (u (n - p))‖ ≤
      ‖thirdFullThreeBandZ3ComplexFrequency244 (n - p)‖ * ‖u p‖ *
        ‖u (n - p)‖ :=
      thirdFullThreeBand_z3ComplexTransport_norm_le244 n (n - p)
        (u p) (u (n - p))
    _ = (‖thirdFullThreeBandZ3ComplexFrequency244 (n - p)‖ *
        ‖u (n - p)‖) * ‖u p‖ := by ring
    _ ≤ 500 * ‖u p‖ :=
      mul_le_mul_of_nonneg_right
        (thirdFullThreeBand_z3InfiniteWiener_frequencyAmplitude500_244
          u hHigh (n - p)) (norm_nonneg (u p))

/-- Finite full-output quadratic Fourier convolution equals the original
ordered-pair expression indexed by p, with the partner n-p included only
when it belongs to the same input cutoff. -/
theorem thirdFullThreeBand_z3GalerkinQuadratic_partnerFilter244
    (s : Finset OqIndex244) (u : OqIndex244 → OqBand244)
    (n : OqIndex244) :
    thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n =
      ∑ p ∈ s.filter (fun p => n - p ∈ s),
        thirdFullThreeBandZ3ComplexTransport244 n (n - p) (u p) (u (n - p)) := by
  classical
  unfold thirdFullThreeBandZ3GalerkinQuadratic244
  calc
    (∑ p ∈ s, ∑ q ∈ s,
        if p + q = n then
          thirdFullThreeBandZ3ComplexTransport244 n q (u p) (u q)
        else 0) =
      ∑ p ∈ s, if n - p ∈ s then
        thirdFullThreeBandZ3ComplexTransport244 n (n - p) (u p) (u (n - p))
        else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          have hEquiv (q : OqIndex244) : (p + q = n) ↔ (q = n - p) := by
            constructor
            · intro h
              calc
                q = (p + q) - p := by abel
                _ = n - p := by rw [h]
            · intro h
              rw [h]
              abel
          simp_rw [hEquiv]
          rw [Finset.sum_ite_eq']
    _ = _ := by rw [Finset.sum_filter]

/-- Exhaustion means every integer Fourier mode is eventually retained.
No nesting or prescribed geometrical shape of the finite cutoffs is needed. -/
def thirdFullThreeBandZ3GalerkinExhausts244
    (s : ℕ → Finset OqIndex244) : Prop :=
  ∀ p : OqIndex244, ∀ᶠ k : ℕ in atTop, p ∈ s k

/-- Under eventual exhaustion, the filtered input pair sets are cofinal
among ALL finite sets of Fourier frequencies. This ensures no ordered
Leray interaction disappears in the infinite-frequency limit. -/
theorem thirdFullThreeBand_z3Galerkin_partnerFilter_tendsto244
    (s : ℕ → Finset OqIndex244)
    (hExhaust : thirdFullThreeBandZ3GalerkinExhausts244 s)
    (n : OqIndex244) :
    Tendsto (fun k => (s k).filter (fun p => n - p ∈ s k)) atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro q
  have hAll : ∀ᶠ k : ℕ in atTop,
      ∀ p ∈ q, p ∈ (s k).filter (fun z => n - z ∈ s k) := by
    apply (Finset.eventually_all q).2
    intro p hp
    filter_upwards [hExhaust p, hExhaust (n - p)] with k hk1 hk2
    exact Finset.mem_filter.mpr ⟨hk1, hk2⟩
  exact hAll.mono (fun k hk p hp => hk p hp)

/-- The full Galerkin quadratic convolution evaluated on an INFINITE
analytic field tends to the absolutely convergent ordered Fourier tsum
along ANY exhaustive sequence of finite input sets. -/
theorem thirdFullThreeBand_z3GalerkinQuadratic_exhausting_tendstoInfinite244
    (s : ℕ → Finset OqIndex244)
    (hExhaust : thirdFullThreeBandZ3GalerkinExhausts244 s)
    (u : OqIndex244 → OqBand244)
    (hHigh : ∀ q : Finset OqIndex244,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q u ≤ 100)
    (n : OqIndex244) :
    Tendsto (fun k => thirdFullThreeBandZ3GalerkinQuadratic244
        (s k) (s k) u u n) atTop
      (nhds (thirdFullThreeBandZ3InfiniteOrderedLeray244 u n)) := by
  classical
  let F : OqIndex244 → OqBand244 := fun p =>
    thirdFullThreeBandZ3ComplexTransport244 n (n - p) (u p) (u (n - p))
  have hSum : Tendsto (fun q : Finset OqIndex244 => ∑ p ∈ q, F p)
      atTop (nhds (∑' p : OqIndex244, F p)) :=
    (thirdFullThreeBand_z3InfiniteOrderedLeray_summable244 u hHigh n).hasSum
  have hChoose := thirdFullThreeBand_z3Galerkin_partnerFilter_tendsto244
    s hExhaust n
  have hResult := hSum.comp hChoose
  have hEq (k : ℕ) :
      thirdFullThreeBandZ3GalerkinQuadratic244 (s k) (s k) u u n =
        ∑ p ∈ (s k).filter (fun p => n - p ∈ s k), F p :=
    thirdFullThreeBand_z3GalerkinQuadratic_partnerFilter244 (s k) u n
  simpa only [Function.comp_def, F,
    thirdFullThreeBandZ3InfiniteOrderedLeray244, hEq] using hResult

/-- A finite-source-to-infinite-source stability estimate on ONE output
mode. It uses the existing exact 1000-Lipschitz polarization, plus
summability of the full lower-radius difference. -/
theorem thirdFullThreeBand_z3GalerkinQuadratic_toInfiniteField_stability244
    (s : Finset OqIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (v : OqIndex244 → OqBand244)
    (hX : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) ≤ 100)
    (hV : ∀ q : Finset OqIndex244,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q v ≤ 100)
    (n : OqIndex244) :
    thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
      ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x)
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) n -
        thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖ ≤
      1000 * thirdFullThreeBandZ3InfiniteWienerMass244
        (Real.log (3 / 2 : ℝ))
        (fun p => thirdFullThreeBandZ3GalerkinFiniteExtend244 s x p - v p) := by
  classical
  let u := thirdFullThreeBandZ3GalerkinFiniteExtend244 s x
  have hUH (q : Finset OqIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q u ≤ 100 :=
    (thirdFullThreeBand_z3Galerkin_zeroExtend_arbitraryFiniteMass_le244
      (Real.log (9 / 5 : ℝ)) s q x).trans hX
  have hRadius : Real.log (3 / 2 : ℝ) ≤ Real.log (9 / 5 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hUMid (q : Finset OqIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) q u ≤ 100 :=
    (thirdFullThreeBand_z3WienerMass_radius_mono244
      _ _ hRadius q u).trans (hUH q)
  have hVMid (q : Finset OqIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) q v ≤ 100 :=
    (thirdFullThreeBand_z3WienerMass_radius_mono244
      _ _ hRadius q v).trans (hV q)
  have hDiffBound (q : Finset OqIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
        q (fun p => u p - v p) ≤ 200 := by
    calc
      _ ≤ thirdFullThreeBandZ3GalerkinWienerMass244
            (Real.log (3 / 2 : ℝ)) q u +
          thirdFullThreeBandZ3GalerkinWienerMass244
            (Real.log (3 / 2 : ℝ)) q v :=
        thirdFullThreeBand_z3GalerkinWiener_sub_le244 _ q u v
      _ ≤ 200 := by linarith [hUMid q, hVMid q]
  have hSummable : Summable (fun p : OqIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) p *
        ‖u p - v p‖) := by
    apply summable_of_sum_le
      (fun p => mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ p).le
        (norm_nonneg _))
    exact hDiffBound
  have hFinite : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s (fun p => u p - v p) ≤
      thirdFullThreeBandZ3InfiniteWienerMass244
        (Real.log (3 / 2 : ℝ)) (fun p => u p - v p) := by
    unfold thirdFullThreeBandZ3GalerkinWienerMass244
      thirdFullThreeBandZ3InfiniteWienerMass244
    exact hSummable.sum_le_tsum s (fun p hp =>
      mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ p).le (norm_nonneg _))
  have hSource := thirdFullThreeBand_z3GalerkinSourceDiff_1000_lower244
    ({n} : Finset OqIndex244) s u v (hUMid s) (hVMid s)
  simp only [Finset.sum_singleton] at hSource
  exact hSource.trans (mul_le_mul_of_nonneg_left hFinite (by norm_num))

/-- The previously completed infinite source is THE genuine absolutely
convergent ordered Leray convolution, assuming the Galerkin cutoffs exhaust
Z³. This theorem identifies the source by uniqueness of limits; it does not
assume the desired convolution equality as a premise. -/
theorem thirdFullThreeBand_z3Galerkin_completedSource_eq_orderedLeray244
    {T : Type*}
    (s : ℕ → Finset OqIndex244)
    (x : (k : ℕ) → T → thirdFullThreeBandZ3GalerkinFiniteState244 (s k))
    (g Q : T → OqIndex244 → OqBand244)
    (hExhaust : thirdFullThreeBandZ3GalerkinExhausts244 s)
    (hHigh : ∀ k t,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) ≤ 100)
    (hLimitHigh : ∀ t (q : Finset OqIndex244),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q (g t) ≤ 100)
    (hStrong : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t : T,
        thirdFullThreeBandZ3InfiniteWienerMass244
          (Real.log (3 / 2 : ℝ))
          (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244
            (s k) (x k t) n - g t n) < epsilon)
    (hSource : ∀ t n, Tendsto
      (fun k => thirdFullThreeBandZ3GalerkinQuadratic244
        (s k) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t))
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) n)
      atTop (nhds (Q t n))) :
    ∀ t n, Q t n = thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n := by
  classical
  intro t n
  have hFiniteG := thirdFullThreeBand_z3GalerkinQuadratic_exhausting_tendstoInfinite244
    s hExhaust (g t) (hLimitHigh t) n
  have hError : Tendsto
      (fun k => thirdFullThreeBandZ3GalerkinQuadratic244
        (s k) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t))
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) n -
        thirdFullThreeBandZ3GalerkinQuadratic244
          (s k) (s k) (g t) (g t) n)
      atTop (nhds (0 : OqBand244)) := by
    apply Metric.tendsto_atTop.mpr
    intro epsilon hEpsilon
    have hE := hStrong (epsilon / 1000) (by positivity)
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hE
    refine ⟨K, ?_⟩
    intro k hk
    have hBound := thirdFullThreeBand_z3GalerkinQuadratic_toInfiniteField_stability244
      (s k) (x k t) (g t) (hHigh k t) (hLimitHigh t) n
    have hw := thirdFullThreeBand_z3GalerkinWeight_one_le244
      (Real.log (5 / 4 : ℝ)) (Real.log_nonneg (by norm_num)) n
    have hNorm : ‖thirdFullThreeBandZ3GalerkinQuadratic244 (s k) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t))
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) n -
      thirdFullThreeBandZ3GalerkinQuadratic244 (s k) (s k) (g t) (g t) n‖ ≤
        thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 (s k) (s k)
            (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t))
            (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) n -
          thirdFullThreeBandZ3GalerkinQuadratic244 (s k) (s k) (g t) (g t) n‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    have hStrongK := hK k hk t
    have hFinal : ‖thirdFullThreeBandZ3GalerkinQuadratic244 (s k) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t))
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) n -
      thirdFullThreeBandZ3GalerkinQuadratic244 (s k) (s k) (g t) (g t) n‖ <
      epsilon := by
      calc
        _ ≤ thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 (s k) (s k)
            (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t))
            (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) n -
          thirdFullThreeBandZ3GalerkinQuadratic244 (s k) (s k) (g t) (g t) n‖ := hNorm
        _ ≤ 1000 * thirdFullThreeBandZ3InfiniteWienerMass244
          (Real.log (3 / 2 : ℝ))
          (fun p => thirdFullThreeBandZ3GalerkinFiniteExtend244
            (s k) (x k t) p - g t p) := hBound
        _ < 1000 * (epsilon / 1000) :=
          mul_lt_mul_of_pos_left hStrongK (by norm_num)
        _ = epsilon := by ring
    simpa only [dist_zero_right] using hFinal
  have hSourceViaG := hError.add hFiniteG
  have hSame : Tendsto
      (fun k => thirdFullThreeBandZ3GalerkinQuadratic244
        (s k) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t))
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) n)
    atTop (nhds (thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n)) := by
    simpa only [zero_add, sub_add_cancel] using hSourceViaG
  exact tendsto_nhds_unique (hSource t n) hSame


/-- Complete the exact finite Galerkin sources and IDENTIFY that completed
field with the independent absolutely convergent ordered Fourier convolution.
The input source-Cauchy property is supplied by the preceding cross-cutoff
Galerkin theorem; the exhaustivity and analytic convergence hypotheses are
kept visible instead of hiding an infinite-PDE assumption. -/
theorem thirdFullThreeBand_z3Galerkin_exists_identifiedInfiniteLeray244
    {T : Type*}
    (s : ℕ → Finset OqIndex244)
    (x : (k : ℕ) → T → thirdFullThreeBandZ3GalerkinFiniteState244 (s k))
    (g : T → OqIndex244 → OqBand244)
    (hExhaust : thirdFullThreeBandZ3GalerkinExhausts244 s)
    (hHigh : ∀ k t,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) (s k)
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) ≤ 100)
    (hLimitHigh : ∀ t (q : Finset OqIndex244),
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q (g t) ≤ 100)
    (hStrong : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k : ℕ in atTop, ∀ t : T,
        thirdFullThreeBandZ3InfiniteWienerMass244
          (Real.log (3 / 2 : ℝ))
          (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244
            (s k) (x k t) n - g t n) < epsilon)
    (hSourceCauchy : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ t : T,
        ∀ q : Finset OqIndex244,
          thirdFullThreeBandZ3GalerkinWienerMass244
            (Real.log (5 / 4 : ℝ)) q
            (fun n => thirdFullThreeBandZ3GalerkinQuadratic244
                (s k) (s k)
                (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t))
                (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) n -
              thirdFullThreeBandZ3GalerkinQuadratic244
                (s l) (s l)
                (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s l) (x l t))
                (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s l) (x l t)) n)
            < epsilon) :
    ∃ Q : T → OqIndex244 → OqBand244,
      (∀ t,
        Summable (fun n : OqIndex244 =>
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n * ‖Q t n‖) ∧
        thirdFullThreeBandZ3InfiniteWienerMass244
          (Real.log (5 / 4 : ℝ)) (Q t) ≤ 50000) ∧
      (∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ k : ℕ in atTop, ∀ t : T,
          thirdFullThreeBandZ3InfiniteWienerMass244
            (Real.log (5 / 4 : ℝ))
            (fun n => thirdFullThreeBandZ3GalerkinQuadratic244
                (s k) (s k)
                (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t))
                (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) n -
              Q t n) < epsilon) ∧
      ∀ t n, Q t n = thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n := by
  classical
  let f : ℕ → T → OqIndex244 → OqBand244 := fun k t n =>
    thirdFullThreeBandZ3GalerkinQuadratic244 (s k) (s k)
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t))
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 (s k) (x k t)) n
  have hBound (k : ℕ) (t : T) (q : Finset OqIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (5 / 4 : ℝ)) q (f k t) ≤ 50000 :=
    thirdFullThreeBand_z3GalerkinQuadratic_allOutputs50000_244
      (s k) q (x k t) (hHigh k t)
  obtain ⟨Q, hModes, hMass, hConverges⟩ :=
    thirdFullThreeBand_z3Galerkin_uniformSourceCompletion244
      f hSourceCauchy hBound
  have hIdentity := thirdFullThreeBand_z3Galerkin_completedSource_eq_orderedLeray244
    s x g Q hExhaust hHigh hLimitHigh hStrong hModes
  exact ⟨Q, hMass, hConverges, hIdentity⟩

end
end PrimeTensor.FirstMonomialTriad

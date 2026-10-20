import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientFinitePair244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzMatchedSobolevJets244
import Mathlib.Tactic

/-!
# Automatic vanishing of the full 972-term spectral H³ gradient pair error

This eliminates the separately assumed error-gauge condition from the prior
full-gradient Cauchy theorem. The input is only (i) a convergent weighted H³
spectral sequence and (ii) the already constructed genuine E₂/E₃ Schwartz
energy-Cauchy family. The 81 third-order L² roots are bounded and Cauchy;
all spectral component norms are bounded and their differences Cauchy.

For every signed 3+3+1 triple, the pair modulus is at most
  6 C K² D
provided all roots and spectral norms are ≤ K and all relevant differences
are ≤ D. Four triples per five-axis slot give 24 C K² D. A finite-index
Cauchy argument handles all 243 slots, without inserting an extra transport
limit as a hypothesis. The resulting scalar is the canonical *gradient
completion*, NOT yet the independently defined physical PDE pairing.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev Slot5 := A3 × (A3 × (A3 × (A3 × A3)))

noncomputable local instance axisFintypeGradientAutomatic244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev gradientAutomaticThird244
    (f : A3 → SchwartzMap V3 ℝ) (j i k l : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (f j)))

/-- Explicit cubic scalar estimate for the THREE 2–2–infinity perturbation
terms, including the physical pairing factor two. -/
theorem fullGradientTripleSpectralPairEnvelope_le_uniform244
    (a b a' b' : SchwartzMap V3 ℝ)
    (F G : H3SpectralScalarState)
    (K D : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (ha : schwartzIntegralL2Root244 (a - a') ≤ D)
    (hb : schwartzIntegralL2Root244 (b - b') ≤ D)
    (hA : schwartzIntegralL2Root244 a' ≤ K)
    (hB : schwartzIntegralL2Root244 b ≤ K)
    (hB' : schwartzIntegralL2Root244 b' ≤ K)
    (hF : ‖F‖ ≤ K)
    (hFG : ‖F - G‖ ≤ D) :
    fullGradientTripleSpectralPairEnvelope244 a b a' b' F G ≤
      6 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * K ^ 2 * D := by
  let C : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  have hC : 0 ≤ C := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hDa : 0 ≤ schwartzIntegralL2Root244 (a - a') := schwartzIntegralL2Root244_nonneg _
  have hDb : 0 ≤ schwartzIntegralL2Root244 (b - b') := schwartzIntegralL2Root244_nonneg _
  have hNa : 0 ≤ schwartzIntegralL2Root244 a' := schwartzIntegralL2Root244_nonneg _
  have hNb : 0 ≤ schwartzIntegralL2Root244 b := schwartzIntegralL2Root244_nonneg _
  have hNb' : 0 ≤ schwartzIntegralL2Root244 b' := schwartzIntegralL2Root244_nonneg _
  change 2 * ((C * ‖F‖) *
      (schwartzIntegralL2Root244 (a - a') * schwartzIntegralL2Root244 b) +
      (C * ‖F‖) *
      (schwartzIntegralL2Root244 a' * schwartzIntegralL2Root244 (b - b')) +
      (C * ‖F - G‖) *
      (schwartzIntegralL2Root244 a' * schwartzIntegralL2Root244 b')) ≤
    6 * C * K ^ 2 * D
  calc
    _ ≤ 2 * ((C * K) * (D * K) +
        (C * K) * (K * D) + (C * D) * (K * K)) := by
          gcongr <;> assumption
    _ = 6 * C * K ^ 2 * D := by ring

/-- Finite sums of arbitrary real errors inherit two-index tail smallness.
No unproved uniformity in the finite index enters the argument. -/
private theorem gradientAutomatic_finitePairSumSmall244
    {J : Type*} [Fintype J]
    (E : ℕ → ℕ → J → ℝ)
    (hE : ∀ p : J, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n → E m n p < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
        (∑ p : J, E m n p) < ε := by
  classical
  have hFin (s : Finset J) :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
          (∑ p ∈ s, E m n p) < ε := by
    induction s using Finset.induction_on with
    | empty =>
        intro ε hε
        refine ⟨0, ?_⟩
        intro m _ n _
        simpa using hε
    | @insert p s hp ih =>
        intro ε hε
        have hHalf : 0 < ε / 2 := by positivity
        obtain ⟨N1, h1⟩ := hE p (ε / 2) hHalf
        obtain ⟨N2, h2⟩ := ih (ε / 2) hHalf
        refine ⟨max N1 N2, ?_⟩
        intro m hm n hn
        have hm1 : N1 ≤ m := (le_max_left N1 N2).trans hm
        have hn1 : N1 ≤ n := (le_max_left N1 N2).trans hn
        have hm2 : N2 ≤ m := (le_max_right N1 N2).trans hm
        have hn2 : N2 ≤ n := (le_max_right N1 N2).trans hn
        have hpSmall := h1 m hm1 n hn1
        have hsSmall := h2 m hm2 n hn2
        rw [Finset.sum_insert hp]
        linarith
  exact hFin (Finset.univ : Finset J)

/-- Each weighted-H³ coordinate of a convergent spectral sequence has a
GLOBAL norm bound, valid even at initial indices. -/
private theorem gradientAutomatic_spectralCoordinateBound244
    (V : ℕ → H3SpectralVelocityState)
    (U : H3SpectralVelocityState)
    (hV : Tendsto V atTop (𝓝 U))
    (j : Fin 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖V n j‖ ≤ B := by
  have hCoord : CauchySeq (fun n => V n j) :=
    (((tendsto_pi_nhds.mp hV) j)).cauchySeq
  obtain ⟨B, hBpos, hB⟩ := cauchySeq_bdd hCoord
  refine ⟨‖V 0 j‖ + B, add_nonneg (norm_nonneg _) (le_of_lt hBpos), ?_⟩
  intro n
  have hDist := hB n 0
  rw [dist_eq_norm] at hDist
  have hTriangle :
      ‖V n j‖ ≤ ‖V n j - V 0 j‖ + ‖V 0 j‖ := by
    simpa only [sub_add_cancel] using
      (norm_add_le (V n j - V 0 j) (V 0 j))
  linarith only [hTriangle, hDist]

/-- The previously conditional 972-term gradient error is automatically
Cauchy-small for every synchronized H³ spectral/E₂/E₃ Schwartz family.
All four gradient triples at each of the 243 physical slots are included. -/
theorem fullSchwartzGradientSpectralPairEnvelope_cauchySmall_of_H3Energy244
    (V : ℕ → H3SpectralVelocityState)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (U : H3SpectralVelocityState)
    (hV : Tendsto V atTop (𝓝 U))
    (hEnergy : SchwartzH3DifferenceEnergyCauchy244 f) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
        fullSchwartzGradientSpectralPairEnvelope244
          (f m) (f n) (V m) (V n) < ε := by
  classical
  obtain ⟨K₀, hK₀⟩ := hEnergy.toStrongJets.uniformRoots
  have hSpecEach (j : Fin 3) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖V n j‖ ≤ B :=
    gradientAutomatic_spectralCoordinateBound244 V U hV j
  choose B hBpos hB using hSpecEach
  let K : ℝ := 1 + K₀ + ∑ j : Fin 3, B j
  have hBSum : 0 ≤ ∑ j : Fin 3, B j := by
    apply Finset.sum_nonneg
    intro j _
    exact hBpos j
  have hK0le : K₀ ≤ K := by
    dsimp [K]
    linarith
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith [hK₀.1]
  have hRoot (n : ℕ) (j i k l : A3) :
      schwartzIntegralL2Root244
        (gradientAutomaticThird244 (f n) j i k l) ≤ K := by
    have h := (hK₀.2 n (i, (k, (l, (j, j))))).1
    change schwartzIntegralL2Root244
      (gradientAutomaticThird244 (f n) j i k l) ≤ K₀ at h
    exact h.trans hK0le
  have hSpectralBound (n : ℕ) (j : Fin 3) : ‖V n j‖ ≤ K := by
    have hSingle : B j ≤ ∑ q : Fin 3, B q :=
      Finset.single_le_sum (fun q _ => hBpos q) (Finset.mem_univ j)
    have hBound := hB j n
    dsimp [K]
    linarith [hK₀.1]
  have hMixed : SchwartzMixedJetGraphCauchy244 f :=
    hEnergy.toMixedGraph
  have hSpecCauchy (j : Fin 3) : CauchySeq (fun n => V n j) :=
    (((tendsto_pi_nhds.mp hV) j)).cauchySeq
  let E : ℕ → ℕ → Slot5 → ℝ := fun m n p =>
    fullGradientAxisSpectralPairEnvelope244 (f m) (f n) (V m) (V n)
      p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  have hSlot : ∀ p : Slot5, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
        E m n p < ε := by
    rintro ⟨j, i, k, l, r⟩ ε hε
    let C : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
    have hC : 0 ≤ C := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
    let Q : ℝ := 24 * C * K ^ 2
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    let D : ℝ := ε / (Q + 1)
    have hDpos : 0 < D := div_pos hε (by linarith)
    obtain ⟨Ng, hNg⟩ := hMixed D hDpos
    obtain ⟨Nj, hNj⟩ := (Metric.cauchySeq_iff.mp
      (hSpecCauchy (h3ClassicalizationFinOfAxis j))) D hDpos
    obtain ⟨Nr, hNr⟩ := (Metric.cauchySeq_iff.mp
      (hSpecCauchy (h3ClassicalizationFinOfAxis r))) D hDpos
    refine ⟨max Ng (max Nj Nr), ?_⟩
    intro m hm n hn
    have hmg : Ng ≤ m := (le_max_left _ _).trans hm
    have hng : Ng ≤ n := (le_max_left _ _).trans hn
    have hmj : Nj ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
    have hnj : Nj ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    have hmr : Nr ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
    have hnr : Nr ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    have hGraph := hNg m hmg n hng
    have hDistJ : ‖V m (h3ClassicalizationFinOfAxis j) -
        V n (h3ClassicalizationFinOfAxis j)‖ ≤ D := by
      have h := hNj m hmj n hnj
      simpa only [dist_eq_norm] using le_of_lt h
    have hDistR : ‖V m (h3ClassicalizationFinOfAxis r) -
        V n (h3ClassicalizationFinOfAxis r)‖ ≤ D := by
      have h := hNr m hmr n hnr
      simpa only [dist_eq_norm] using le_of_lt h
    have hThirdDiff (a b c d : A3) :
        schwartzIntegralL2Root244
          (gradientAutomaticThird244 (f m) a b c d -
            gradientAutomaticThird244 (f n) a b c d) ≤ D := by
      have hSlotBound :=
        (schwartzMixedJetGraphDistance_bounds_slots244
          (f m) (f n) (b, (c, (d, (a, a))))).1
      change schwartzIntegralL2Root244
        (gradientAutomaticThird244 (f m) a b c d -
          gradientAutomaticThird244 (f n) a b c d) ≤
        schwartzMixedJetGraphDistance244 (f m) (f n) at hSlotBound
      exact hSlotBound.trans (le_of_lt hGraph)
    let R : ℝ := 6 * C * K ^ 2 * D
    have hTerm (a b c d e f' g h z : A3)
        (hz : z = j ∨ z = r) :
        fullGradientTripleSpectralPairEnvelope244
          (gradientAutomaticThird244 (f m) a b c d)
          (gradientAutomaticThird244 (f m) e f' g h)
          (gradientAutomaticThird244 (f n) a b c d)
          (gradientAutomaticThird244 (f n) e f' g h)
          (V m (h3ClassicalizationFinOfAxis z))
          (V n (h3ClassicalizationFinOfAxis z)) ≤ R := by
      have hDistance : ‖V m (h3ClassicalizationFinOfAxis z) -
          V n (h3ClassicalizationFinOfAxis z)‖ ≤ D := by
        rcases hz with rfl | rfl
        · exact hDistJ
        · exact hDistR
      exact fullGradientTripleSpectralPairEnvelope_le_uniform244
        _ _ _ _ _ _ K D (le_trans (by norm_num) hK) (le_of_lt hDpos)
        (hThirdDiff a b c d) (hThirdDiff e f' g h)
        (hRoot n a b c d) (hRoot m e f' g h)
        (hRoot n e f' g h) (hSpectralBound m _)
        hDistance
    have h1 := hTerm j i k l r i k l j (Or.inl rfl)
    have h2 := hTerm j i k l j i k r r (Or.inr rfl)
    have h3 := hTerm j i k l j i r l r (Or.inr rfl)
    have h4 := hTerm j i k l j r k l r (Or.inr rfl)
    have hAxis :
        fullGradientAxisSpectralPairEnvelope244
          (f m) (f n) (V m) (V n) j i k l r ≤ 4 * R := by
      unfold fullGradientAxisSpectralPairEnvelope244
      linarith only [h1, h2, h3, h4]
    have hEq : 4 * R = Q * D := by
      dsimp [R, Q, C]
      ring
    have hSmall : Q * D < ε := by
      have hIdentity : D * (Q + 1) = ε := by
        dsimp [D]
        exact div_mul_cancel₀ _ (ne_of_gt (by linarith : 0 < Q + 1))
      nlinarith only [hIdentity, hDpos]
    have hBound :
        fullGradientAxisSpectralPairEnvelope244
          (f m) (f n) (V m) (V n) j i k l r ≤ Q * D := by
      calc
        _ ≤ 4 * R := hAxis
        _ = Q * D := hEq
    exact lt_of_le_of_lt hBound hSmall
  intro ε hε
  obtain ⟨N, hN⟩ := gradientAutomatic_finitePairSumSmall244 E hSlot ε hε
  refine ⟨N, ?_⟩
  intro m hm n hn
  have h := hN m hm n hn
  simpa only [Fintype.sum_prod_type, E,
    fullSchwartzGradientSpectralPairEnvelope244] using h

/-- Every matched E₂/E₃ Schwartz realization of a convergent spectral H³
state therefore has a genuine real completion of the whole 3–3–1 channel,
without a separate gauge assumption. -/
theorem exists_fullSchwartzGradientTransport_limit_of_H3Energy244
    (V : ℕ → H3SpectralVelocityState)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (U : H3SpectralVelocityState)
    (hV : Tendsto V atTop (𝓝 U))
    (hMatch : ∀ n j,
      h3SchwartzPoint3Scalar (f n j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (V n (h3ClassicalizationFinOfAxis j)))
    (hEnergy : SchwartzH3DifferenceEnergyCauchy244 f) :
    ∃ L : ℝ, Tendsto (fun n => fullSchwartzGradientTransport244 (f n))
      atTop (𝓝 L) :=
  exists_fullSchwartzGradientTransport_limit_of_spectralPairGauge244
    V f hMatch
    (fullSchwartzGradientSpectralPairEnvelope_cauchySmall_of_H3Energy244
      V f U hV hEnergy)

/-- For every weighted H³ spectral velocity, the SAME genuinely real
Schwartz sequence realizes both the canonical signed 3–2–2 scalar and a
convergent complete 3–3–1 gradient channel. Neither limit is assumed. -/
theorem exists_thirdFullSchwartz_matchedSignedAndGradientLimits244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
    ∃ L : ℝ,
      Tendsto V atTop (𝓝 U) ∧
      (∀ n j, h3SchwartzPoint3Scalar (Ψ n j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3 (V n j)) ∧
      Tendsto (fun n => fullSchwartzGradientTransport244
          (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 L) ∧
      Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial
          (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (weightedH3CanonicalSignedFirstMonomial244 U)) := by
  obtain ⟨V, Ψ, hV, hMatch, hEnergy, _hMixed, hSecond, hThird⟩ :=
    exists_thirdFullSchwartz_matchedDecoderAndMixedGraph244 U
  let f : ℕ → A3 → SchwartzMap V3 ℝ :=
    fun n j => Ψ n (h3ClassicalizationFinOfAxis j)
  have hMatchAxis (n : ℕ) (j : A3) :
      h3SchwartzPoint3Scalar (f n j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (V n (h3ClassicalizationFinOfAxis j)) := by
    exact hMatch n (h3ClassicalizationFinOfAxis j)
  obtain ⟨L, hL⟩ :=
    exists_fullSchwartzGradientTransport_limit_of_H3Energy244
      V f U hV hMatchAxis hEnergy
  let H : SchwartzH3CauchyFamily244 := ⟨f, hEnergy⟩
  let W : WeightedH3MatchedSchwartzCompletion244 U := {
    spectral := V
    family := H
    spectral_tendsto := hV
    second_exact := by
      intro n j a b
      change (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (Ψ n (h3ClassicalizationFinOfAxis j)))).toLp
            2 (volume : Measure V3) =
        h3ToFourierRealL2
          (h3SpectralVelocitySecondPhysicalJetFamily244 (V n)
            (h3ClassicalizationFinOfAxis j) a b)
      exact hSecond n j a b
    third_exact := by
      intro n j a b c
      change (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c}
            (Ψ n (h3ClassicalizationFinOfAxis j))))).toLp
              2 (volume : Measure V3) =
        h3ToFourierRealL2
          (h3SpectralVelocityThirdPhysicalJetFamily244 (V n)
            (h3ClassicalizationFinOfAxis j) a b c)
      exact hThird n j a b c
  }
  have hSigned := weightedH3CanonicalSignedFirstMonomial_tendsto244 U W
  refine ⟨V, Ψ, L, hV, hMatch, ?_, ?_⟩
  · simpa only [f] using hL
  · simpa only [H, f] using hSigned

end
end PrimeTensor.FirstMonomialTriad

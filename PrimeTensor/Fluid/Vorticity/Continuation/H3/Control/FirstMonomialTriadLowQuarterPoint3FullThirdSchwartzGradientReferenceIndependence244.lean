import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientAutomaticGauge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzWeightedReferenceIndependence244
import Mathlib.Tactic

/-!
# Choice independence of the complete third-order gradient completion

The 972-term two-profile gradient estimate is paired with the already-proved
cross E₂/E₃ energy equivalence for TWO independently chosen derivative-matched
Schwartz families approaching the SAME weighted spectral H³ velocity.
The mixed L²/L⁴ graph tends to zero; ordinary spectral H³ convergence makes
all first-jet spectral differences tend to zero. The full 3–3–1 gradient
therefore has the SAME limit for both sequences.

We retain zeroth-order pointwise matching in the completion structure:
older matched H³ completion records deliberately did not store it.
The result is a well-defined canonical gradient scalar on the weighted
spectral H³ space, not yet an equality with the separately specified
physical Navier–Stokes transport integral.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1900000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev Slot5 := A3 × (A3 × (A3 × (A3 × A3)))

noncomputable local instance axisFintypeGradientIndependent244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev gradientIndependentThird244
    (f : A3 → SchwartzMap V3 ℝ) (j i k l : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (f j)))

/-- The full 972-term error tends to zero *across two independent sequences*,
provided their existing Sobolev cross energies vanish. The spectral sequences
are allowed to differ at every finite index. -/
theorem fullSchwartzGradientSpectralPairEnvelope_cross_tendsto_zero244
    (U : H3SpectralVelocityState)
    (V W : ℕ → H3SpectralVelocityState)
    (f g : ℕ → A3 → SchwartzMap V3 ℝ)
    (hV : Tendsto V atTop (𝓝 U))
    (hW : Tendsto W atTop (𝓝 U))
    (hF : SchwartzH3DifferenceEnergyCauchy244 f)
    (hG : SchwartzH3DifferenceEnergyCauchy244 g)
    (hCross : SchwartzH3CrossEnergyVanishing244 f g) :
    Tendsto (fun n => fullSchwartzGradientSpectralPairEnvelope244
      (f n) (g n) (V n) (W n)) atTop (𝓝 0) := by
  classical
  obtain ⟨KF, hKF⟩ := hF.toStrongJets.uniformRoots
  obtain ⟨KG, hKG⟩ := hG.toStrongJets.uniformRoots
  have hEach (j : Fin 3) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖V n j‖ ≤ B := by
    have hCoord : CauchySeq (fun n => V n j) :=
      ((tendsto_pi_nhds.mp hV) j).cauchySeq
    obtain ⟨R, hRpos, hR⟩ := cauchySeq_bdd hCoord
    refine ⟨‖V 0 j‖ + R,
      add_nonneg (norm_nonneg _) (le_of_lt hRpos), ?_⟩
    intro n
    have hDist := hR n 0
    rw [dist_eq_norm] at hDist
    have hTriangle :
        ‖V n j‖ ≤ ‖V n j - V 0 j‖ + ‖V 0 j‖ := by
      simpa only [sub_add_cancel] using
        (norm_add_le (V n j - V 0 j) (V 0 j))
    linarith only [hTriangle, hDist]
  choose B hBpos hB using hEach
  let K : ℝ := 1 + KF + KG + ∑ j : Fin 3, B j
  have hBSum : 0 ≤ ∑ j : Fin 3, B j := by
    apply Finset.sum_nonneg
    intro j _
    exact hBpos j
  have hK : 0 ≤ K := by
    dsimp [K]
    linarith [hKF.1, hKG.1]
  have hKFle : KF ≤ K := by
    dsimp [K]
    linarith [hKG.1]
  have hKGle : KG ≤ K := by
    dsimp [K]
    linarith [hKF.1]
  have hRootF (n : ℕ) (j i k l : A3) :
      schwartzIntegralL2Root244
        (gradientIndependentThird244 (f n) j i k l) ≤ K := by
    have h := (hKF.2 n (i, (k, (l, (j, j))))).1
    change schwartzIntegralL2Root244
      (gradientIndependentThird244 (f n) j i k l) ≤ KF at h
    exact h.trans hKFle
  have hRootG (n : ℕ) (j i k l : A3) :
      schwartzIntegralL2Root244
        (gradientIndependentThird244 (g n) j i k l) ≤ K := by
    have h := (hKG.2 n (i, (k, (l, (j, j))))).1
    change schwartzIntegralL2Root244
      (gradientIndependentThird244 (g n) j i k l) ≤ KG at h
    exact h.trans hKGle
  have hSpecF (n : ℕ) (j : Fin 3) : ‖V n j‖ ≤ K := by
    have hs : B j ≤ ∑ q : Fin 3, B q :=
      Finset.single_le_sum (fun q _ => hBpos q) (Finset.mem_univ j)
    have hb := hB j n
    dsimp [K]
    linarith [hKF.1, hKG.1]
  have hGraph : Tendsto (fun n =>
      schwartzMixedJetGraphDistance244 (f n) (g n)) atTop (𝓝 0) :=
    schwartzMixedJetGraph_tendsto_zero_of_crossEnergy244 f g hCross
  have hSpecDiff (j : Fin 3) : Tendsto
      (fun n => ‖V n j - W n j‖) atTop (𝓝 0) := by
    have hv := (tendsto_pi_nhds.mp hV) j
    have hw := (tendsto_pi_nhds.mp hW) j
    simpa only [sub_self, norm_zero] using (hv.sub hw).norm
  have hSpecSum : Tendsto
      (fun n => ∑ j : Fin 3, ‖V n j - W n j‖) atTop (𝓝 0) := by
    have hFin (s : Finset (Fin 3)) : Tendsto
        (fun n => ∑ j ∈ s, ‖V n j - W n j‖) atTop (𝓝 0) := by
      induction s using Finset.induction_on with
      | empty =>
          simpa using (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      | @insert j s hj ih =>
          simpa only [Finset.sum_insert hj, zero_add] using (hSpecDiff j).add ih
    exact hFin Finset.univ
  let D : ℕ → ℝ := fun n =>
    schwartzMixedJetGraphDistance244 (f n) (g n) +
      ∑ j : Fin 3, ‖V n j - W n j‖
  have hD : Tendsto D atTop (𝓝 0) := by
    simpa only [D, zero_add] using hGraph.add hSpecSum
  have hDnonneg (n : ℕ) : 0 ≤ D n := by
    have hg := (schwartzMixedJetGraphDistance_nonneg244 (f n) (g n)).2.2
    have hs : 0 ≤ ∑ j : Fin 3, ‖V n j - W n j‖ := by
      apply Finset.sum_nonneg
      intro j _
      exact norm_nonneg _
    exact add_nonneg hg hs
  have hDiffRoot (n : ℕ) (j i k l : A3) :
      schwartzIntegralL2Root244
        (gradientIndependentThird244 (f n) j i k l -
         gradientIndependentThird244 (g n) j i k l) ≤ D n := by
    have h := (schwartzMixedJetGraphDistance_bounds_slots244
      (f n) (g n) (i, (k, (l, (j, j))))).1
    change schwartzIntegralL2Root244
      (gradientIndependentThird244 (f n) j i k l -
       gradientIndependentThird244 (g n) j i k l) ≤
      schwartzMixedJetGraphDistance244 (f n) (g n) at h
    exact h.trans (le_add_of_nonneg_right (by
      apply Finset.sum_nonneg
      intro j _
      exact norm_nonneg _))
  have hDiffSpec (n : ℕ) (j : Fin 3) : ‖V n j - W n j‖ ≤ D n := by
    have hs : ‖V n j - W n j‖ ≤
        ∑ q : Fin 3, ‖V n q - W n q‖ := by
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 3)))
        (f := fun q : Fin 3 => ‖V n q - W n q‖)
        (fun q _ => norm_nonneg (V n q - W n q))
        (Finset.mem_univ j)
    exact hs.trans (le_add_of_nonneg_left
      (schwartzMixedJetGraphDistance_nonneg244 (f n) (g n)).2.2)
  let C : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  have hC : 0 ≤ C := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  let Q : ℝ := 24 * C * K ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQzero : Tendsto (fun n => Q * D n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => Q) atTop (𝓝 Q)).mul hD
  have hTerm (n : ℕ) (a b c d e f' g' h z : A3) :
      fullGradientTripleSpectralPairEnvelope244
        (gradientIndependentThird244 (f n) a b c d)
        (gradientIndependentThird244 (f n) e f' g' h)
        (gradientIndependentThird244 (g n) a b c d)
        (gradientIndependentThird244 (g n) e f' g' h)
        (V n (h3ClassicalizationFinOfAxis z))
        (W n (h3ClassicalizationFinOfAxis z)) ≤
      6 * C * K ^ 2 * D n := by
    exact fullGradientTripleSpectralPairEnvelope_le_uniform244
      _ _ _ _ _ _ K (D n) hK (hDnonneg n)
      (hDiffRoot n a b c d) (hDiffRoot n e f' g' h)
      (hRootG n a b c d) (hRootF n e f' g' h)
      (hRootG n e f' g' h) (hSpecF n _) (hDiffSpec n _)
  have hSlot (p : Slot5) : Tendsto (fun n =>
      fullGradientAxisSpectralPairEnvelope244 (f n) (g n) (V n) (W n)
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) atTop (𝓝 0) := by
    rcases p with ⟨j, i, k, l, r⟩
    have hBound (n : ℕ) :
        fullGradientAxisSpectralPairEnvelope244 (f n) (g n)
          (V n) (W n) j i k l r ≤ Q * D n := by
      have h1 := hTerm n j i k l r i k l j
      have h2 := hTerm n j i k l j i k r r
      have h3 := hTerm n j i k l j i r l r
      have h4 := hTerm n j i k l j r k l r
      have hs : fullGradientAxisSpectralPairEnvelope244 (f n) (g n)
          (V n) (W n) j i k l r ≤
          4 * (6 * C * K ^ 2 * D n) := by
        unfold fullGradientAxisSpectralPairEnvelope244
        linarith only [h1, h2, h3, h4]
      calc
        _ ≤ 4 * (6 * C * K ^ 2 * D n) := hs
        _ = Q * D n := by dsimp [Q]; ring
    apply squeeze_zero
    · intro n
      unfold fullGradientAxisSpectralPairEnvelope244
      apply add_nonneg
      · apply add_nonneg
        · apply add_nonneg
          · exact fullGradientTripleSpectralPairEnvelope_nonneg244 _ _ _ _ _ _
          · exact fullGradientTripleSpectralPairEnvelope_nonneg244 _ _ _ _ _ _
        · exact fullGradientTripleSpectralPairEnvelope_nonneg244 _ _ _ _ _ _
      · exact fullGradientTripleSpectralPairEnvelope_nonneg244 _ _ _ _ _ _
    · exact hBound
    · exact hQzero
  have hSum (s : Finset Slot5) : Tendsto
      (fun n => ∑ p ∈ s,
        fullGradientAxisSpectralPairEnvelope244 (f n) (g n) (V n) (W n)
          p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) atTop (𝓝 0) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | @insert p s hp ih =>
        simpa only [Finset.sum_insert hp, zero_add] using (hSlot p).add ih
  have hAll := hSum (Finset.univ : Finset Slot5)
  simpa only [Fintype.sum_prod_type, fullSchwartzGradientSpectralPairEnvelope244]
    using hAll

/-- A pointwise-matched completion retains precisely the reconstruction
hypothesis needed to identify first Schwartz derivatives. Second/third L²
matching identifies cross energy for independently chosen families. -/
structure H3MatchedSchwartzGradientCompletion244 (U : H3SpectralVelocityState) where
  spectral : ℕ → H3SpectralVelocityState
  family : SchwartzH3CauchyFamily244
  spectral_tendsto : Tendsto spectral atTop (𝓝 U)
  zero_exact : ∀ n j,
    h3SchwartzPoint3Scalar (family.approximants n j) =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (spectral n (h3ClassicalizationFinOfAxis j))
  second_exact : ∀ n j a b,
    (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b} (family.approximants n j))).toLp
        2 (volume : Measure V3) =
      matchedSpectralSecondFourierJets244 (spectral n) (j, (a, b))
  third_exact : ∀ n j a b c,
    (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (∂_{h3FourierAxisDirection c} (family.approximants n j)))).toLp
          2 (volume : Measure V3) =
      matchedSpectralThirdFourierJets244 (spectral n) (j, (a, (b, c)))
  gradientLimit : ℝ
  gradient_tendsto : Tendsto
    (fun n => fullSchwartzGradientTransport244 (family.approximants n))
    atTop (𝓝 gradientLimit)

/-- For any two decoder- and jet-matched completions of a common H³ state,
the full signed 972-term gradient limits are EXACTLY equal. -/
theorem h3MatchedSchwartzGradientCompletion_limit_unique244
    (U : H3SpectralVelocityState)
    (F G : H3MatchedSchwartzGradientCompletion244 U) :
    F.gradientLimit = G.gradientLimit := by
  have hCross : SchwartzH3FamiliesCrossEnergyVanishing244
      F.family G.family :=
    matchedSpectral_crossEnergy_vanishes_of_sameLimit244
      U F.family G.family F.spectral G.spectral
      F.spectral_tendsto G.spectral_tendsto
      F.second_exact G.second_exact F.third_exact G.third_exact
  have hGauge := fullSchwartzGradientSpectralPairEnvelope_cross_tendsto_zero244
    U F.spectral G.spectral F.family.approximants G.family.approximants
    F.spectral_tendsto G.spectral_tendsto
    F.family.energyCauchy G.family.energyCauchy hCross
  have hDifference : Tendsto (fun n =>
      fullSchwartzGradientTransport244 (F.family.approximants n) -
        fullSchwartzGradientTransport244 (G.family.approximants n))
      atTop (𝓝 0) := by
    have hAbs : Tendsto (fun n =>
        |fullSchwartzGradientTransport244 (F.family.approximants n) -
          fullSchwartzGradientTransport244 (G.family.approximants n)|)
        atTop (𝓝 0) := by
      apply squeeze_zero
      · intro n
        exact abs_nonneg _
      · intro n
        exact fullSchwartzGradientTransport_spectralPair_modulus244
          (F.family.approximants n) (G.family.approximants n)
          (F.spectral n) (G.spectral n)
          (F.zero_exact n) (G.zero_exact n)
      · exact hGauge
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero, Real.norm_eq_abs] using hAbs
  have hBoth := F.gradient_tendsto.sub G.gradient_tendsto
  have hEq : F.gradientLimit - G.gradientLimit = 0 :=
    tendsto_nhds_unique hBoth hDifference
  exact sub_eq_zero.mp hEq

/-- Build one valid pointwise/second/third-matched completion of EVERY
weighted H³ spectral velocity, without a nonlinear transport hypothesis. -/
theorem exists_h3MatchedSchwartzGradientCompletion244
    (U : H3SpectralVelocityState) :
    Nonempty (H3MatchedSchwartzGradientCompletion244 U) := by
  obtain ⟨V, Ψ, hV, hZero, hEnergy, _hGraph, hSecond, hThird⟩ :=
    exists_thirdFullSchwartz_matchedDecoderAndMixedGraph244 U
  let f : ℕ → A3 → SchwartzMap V3 ℝ :=
    fun n j => Ψ n (h3ClassicalizationFinOfAxis j)
  have hExact (n : ℕ) (j : A3) :
      h3SchwartzPoint3Scalar (f n j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (V n (h3ClassicalizationFinOfAxis j)) :=
    hZero n (h3ClassicalizationFinOfAxis j)
  obtain ⟨L, hL⟩ := exists_fullSchwartzGradientTransport_limit_of_H3Energy244
    V f U hV hExact hEnergy
  let H : SchwartzH3CauchyFamily244 := ⟨f, hEnergy⟩
  refine ⟨{
    spectral := V
    family := H
    spectral_tendsto := hV
    zero_exact := hExact
    second_exact := ?_
    third_exact := ?_
    gradientLimit := L
    gradient_tendsto := hL
  }⟩
  · intro n j a b
    change (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (Ψ n (h3ClassicalizationFinOfAxis j)))).toLp
          2 (volume : Measure V3) =
      h3ToFourierRealL2
        (h3SpectralVelocitySecondPhysicalJetFamily244 (V n)
          (h3ClassicalizationFinOfAxis j) a b)
    exact hSecond n j a b
  · intro n j a b c
    change (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (∂_{h3FourierAxisDirection c}
          (Ψ n (h3ClassicalizationFinOfAxis j))))).toLp
            2 (volume : Measure V3) =
      h3ToFourierRealL2
        (h3SpectralVelocityThirdPhysicalJetFamily244 (V n)
          (h3ClassicalizationFinOfAxis j) a b c)
    exact hThird n j a b c

/-- Choice-independent complete 3–3–1 gradient scalar on arbitrary
weighted spectral H³ velocity data. The physical PDE pairing remains
separately defined and is not silently identified here. -/
noncomputable def weightedH3CanonicalGradientTransport244
    (U : H3SpectralVelocityState) : ℝ :=
  (Classical.choice (exists_h3MatchedSchwartzGradientCompletion244 U)).gradientLimit

/-- Every matched Schwartz gradient approximation has precisely the same
canonical numerical limit, independently of its selected approximants. -/
theorem weightedH3CanonicalGradientTransport_tendsto244
    (U : H3SpectralVelocityState)
    (F : H3MatchedSchwartzGradientCompletion244 U) :
    Tendsto (fun n => fullSchwartzGradientTransport244 (F.family.approximants n))
      atTop (𝓝 (weightedH3CanonicalGradientTransport244 U)) := by
  have hEq := h3MatchedSchwartzGradientCompletion_limit_unique244 U F
    (Classical.choice (exists_h3MatchedSchwartzGradientCompletion244 U))
  rw [weightedH3CanonicalGradientTransport244]
  rw [← hEq]
  exact F.gradient_tendsto

end
end PrimeTensor.FirstMonomialTriad

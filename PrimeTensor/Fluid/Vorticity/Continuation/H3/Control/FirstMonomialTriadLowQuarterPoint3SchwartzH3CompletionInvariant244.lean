import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzH3EnergyCauchy244

/-!
# Completed signed transport observable: invariance under strong mixed-jet equivalence

Each Schwartz velocity family Cauchy in the actual E₂/E₃ difference energies
has a convergent signed 243-slot first transport monomial. We package its
canonical real limit. For two families, one common uniform root bound exists
by the already proved automatic-boundedness theorem. We prove the explicit
cross-family modulus

  |M(f)-M(g)| <= 6 * card(Slots) * K² * mixedGraph(f,g).

Thus approximating families whose mixed graph discrepancies tend to zero
assign the SAME completed signed scalar. This is a reference-independent
completion statement on the analytic approximation class. It does not yet
prove Schwartz density for an arbitrary physical H³ field, or identify that
field's separately defined physical trilinear transport pairing.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeH3CompletionInvariant244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev completionThird244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.1}
      (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.2)))

private abbrev completionMiddle244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.2.1}
    (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.1))

private abbrev completionCross244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.2.2.1} (f p.2.2.2.2))

/-- Common real bounds for all three actual jet roots for one field. -/
def Schwartz243SingleFieldRootBound244
    (f : A3 → SchwartzMap V3 ℝ) (K : ℝ) : Prop :=
  ∀ p : SchwartzStrongJetSlots244,
    schwartzIntegralL2Root244 (completionThird244 f p) ≤ K ∧
    schwartzIntegralL4Root244 (completionMiddle244 f p) ≤ K ∧
    schwartzIntegralL4Root244 (completionCross244 f p) ≤ K

private theorem completion_two_roots_le244
    (K δ x a b : ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hx : x ≤ δ)
    (ha : 0 ≤ a) (haK : a ≤ K)
    (hb : 0 ≤ b) (hbK : b ≤ K) :
    x * (a * b) ≤ δ * (K * K) := by
  have hProduct : a * b ≤ K * K := by
    calc
      a * b ≤ K * b := mul_le_mul_of_nonneg_right haK hb
      _ ≤ K * K := mul_le_mul_of_nonneg_left hbK hK
  calc
    x * (a * b) ≤ δ * (a * b) :=
      mul_le_mul_of_nonneg_right hx (mul_nonneg ha hb)
    _ ≤ δ * (K * K) := mul_le_mul_of_nonneg_left hProduct hδ

/-- The three true Hölder errors are bounded by three copies of δK². -/
private theorem completion_three_roots_le244
    (K δ x y z a b c d : ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hx : x ≤ δ) (hy : y ≤ δ) (hz : z ≤ δ)
    (ha : 0 ≤ a) (haK : a ≤ K)
    (hb : 0 ≤ b) (hbK : b ≤ K)
    (hc : 0 ≤ c) (hcK : c ≤ K)
    (hd : 0 ≤ d) (hdK : d ≤ K) :
    x * (a * b) + c * (y * b) + c * (d * z) ≤
      3 * (δ * (K * K)) := by
  have hFirst := completion_two_roots_le244 K δ x a b
    hK hδ hx ha haK hb hbK
  have hSecond := completion_two_roots_le244 K δ y c b
    hK hδ hy hc hcK hb hbK
  have hThird := completion_two_roots_le244 K δ z c d
    hK hδ hz hc hcK hd hdK
  calc
    x * (a * b) + c * (y * b) + c * (d * z) =
        x * (a * b) + y * (c * b) + z * (c * d) := by ring
    _ ≤ δ * (K * K) + δ * (K * K) + δ * (K * K) :=
      add_le_add (add_le_add hFirst hSecond) hThird
    _ = 3 * (δ * (K * K)) := by ring

/-- For two Schwartz fields with bounded actual jet roots, every one of the
243 spatial perturbation envelopes is at most 3K² times their mixed graph. -/
theorem schwartzPhysicalSlotPerturbation_le_mixedGraph244
    (f g : A3 → SchwartzMap V3 ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hf : Schwartz243SingleFieldRootBound244 f K)
    (hg : Schwartz243SingleFieldRootBound244 g K)
    (p : SchwartzStrongJetSlots244) :
    schwartzPhysicalSlotPerturbation244 f g p ≤
      3 * (schwartzMixedJetGraphDistance244 f g * (K * K)) := by
  let δ : ℝ := schwartzMixedJetGraphDistance244 f g
  let x : ℝ := schwartzIntegralL2Root244
    (completionThird244 f p - completionThird244 g p)
  let y : ℝ := schwartzIntegralL4Root244
    (completionMiddle244 f p - completionMiddle244 g p)
  let z : ℝ := schwartzIntegralL4Root244
    (completionCross244 f p - completionCross244 g p)
  let a : ℝ := schwartzIntegralL4Root244 (completionMiddle244 f p)
  let b : ℝ := schwartzIntegralL4Root244 (completionCross244 f p)
  let c : ℝ := schwartzIntegralL2Root244 (completionThird244 g p)
  let d : ℝ := schwartzIntegralL4Root244 (completionMiddle244 g p)
  have hδ : 0 ≤ δ :=
    (schwartzMixedJetGraphDistance_nonneg244 f g).2.2
  have hBounds := schwartzMixedJetGraphDistance_bounds_slots244 f g p
  have hx : x ≤ δ := hBounds.1
  have hy : y ≤ δ := hBounds.2.1
  have hz : z ≤ δ := hBounds.2.2
  have ha : 0 ≤ a := schwartzIntegralL4Root244_nonneg _
  have hb : 0 ≤ b := schwartzIntegralL4Root244_nonneg _
  have hc : 0 ≤ c := schwartzIntegralL2Root244_nonneg _
  have hd : 0 ≤ d := schwartzIntegralL4Root244_nonneg _
  have haK : a ≤ K := (hf p).2.1
  have hbK : b ≤ K := (hf p).2.2
  have hcK : c ≤ K := (hg p).1
  have hdK : d ≤ K := (hg p).2.1
  have hExact :
      schwartzPhysicalSlotPerturbation244 f g p =
        x * (a * b) + c * (y * b) + c * (d * z) := by
    rfl
  rw [hExact]
  exact completion_three_roots_le244 K δ x y z a b c d
    hK hδ hx hy hz ha haK hb hbK hc hcK hd hdK

/-- Quantitative Lipschitz modulus on every jet-root bounded set.
The factor 2 from the signed aggregate and all 243 slots are retained. -/
theorem lowNormalRealSchwartz_firstMonomial_crossGraph_bound244
    (f g : A3 → SchwartzMap V3 ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hf : Schwartz243SingleFieldRootBound244 f K)
    (hg : Schwartz243SingleFieldRootBound244 g K) :
    2 * (∑ p : SchwartzStrongJetSlots244,
      schwartzPhysicalSlotPerturbation244 f g p) ≤
      (6 * (Fintype.card SchwartzStrongJetSlots244 : ℝ) *
        (K * K)) * schwartzMixedJetGraphDistance244 f g := by
  classical
  have hTerms :
      (∑ p : SchwartzStrongJetSlots244,
        schwartzPhysicalSlotPerturbation244 f g p) ≤
      ∑ _p : SchwartzStrongJetSlots244,
        3 * (schwartzMixedJetGraphDistance244 f g * (K * K)) := by
    apply Finset.sum_le_sum
    intro p _
    exact schwartzPhysicalSlotPerturbation_le_mixedGraph244 f g K hK hf hg p
  calc
    2 * (∑ p : SchwartzStrongJetSlots244,
      schwartzPhysicalSlotPerturbation244 f g p) ≤
        2 * (∑ _p : SchwartzStrongJetSlots244,
          3 * (schwartzMixedJetGraphDistance244 f g * (K * K))) :=
      mul_le_mul_of_nonneg_left hTerms (by norm_num)
    _ = (6 * (Fintype.card SchwartzStrongJetSlots244 : ℝ) *
          (K * K)) * schwartzMixedJetGraphDistance244 f g := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- An actual Cauchy Schwartz approximation in the genuine E₂/E₃
quadratic energies, rather than in an artificial scalar graph. -/
structure SchwartzH3CauchyFamily244 where
  approximants : ℕ → A3 → SchwartzMap V3 ℝ
  energyCauchy : SchwartzH3DifferenceEnergyCauchy244 approximants

/-- The real signed first-monomial value assigned to an H³-Cauchy
Schwartz approximation. Existence follows from the proven nonlinear
Cauchy theorem and completeness of ℝ. -/
noncomputable def completedSchwartzH3FirstMonomial244
    (F : SchwartzH3CauchyFamily244) : ℝ :=
  Classical.choose
    (lowNormalRealSchwartz_firstMonomial_existsLimit_of_H3EnergyCauchy244
      F.approximants F.energyCauchy)

/-- The chosen completed observable genuinely is the numerical limit of
the signed first monomial of the Schwartz approximants. -/
theorem completedSchwartzH3FirstMonomial_tendsto244
    (F : SchwartzH3CauchyFamily244) :
    Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (F.approximants n))
      atTop (𝓝 (completedSchwartzH3FirstMonomial244 F)) :=
  Classical.choose_spec
    (lowNormalRealSchwartz_firstMonomial_existsLimit_of_H3EnergyCauchy244
      F.approximants F.energyCauchy)

/-- The two approximations agree in the actual 81+27 mixed jet graph.
This is the explicit analytic equivalence required for invariance. -/
def SchwartzH3FamiliesCrossGraphVanishing244
    (F G : SchwartzH3CauchyFamily244) : Prop :=
  Tendsto (fun n => schwartzMixedJetGraphDistance244
    (F.approximants n) (G.approximants n)) atTop (𝓝 0)

/-- Equivalent mixed-jet approximations determine the same completed
signed 243-slot monomial. No nonlinear agreement is assumed: it follows
from the quantitative cross-graph estimate and the actual H³ Cauchy bounds. -/
theorem completedSchwartzH3FirstMonomial_eq_of_crossGraph244
    (F G : SchwartzH3CauchyFamily244)
    (hCross : SchwartzH3FamiliesCrossGraphVanishing244 F G) :
    completedSchwartzH3FirstMonomial244 F =
      completedSchwartzH3FirstMonomial244 G := by
  obtain ⟨Kf, hKf⟩ := F.energyCauchy.toStrongJets.uniformRoots
  obtain ⟨Kg, hKg⟩ := G.energyCauchy.toStrongJets.uniformRoots
  let K : ℝ := Kf + Kg
  have hK : 0 ≤ K := by
    have hf := hKf.1
    have hg := hKg.1
    dsimp [K]
    linarith
  have hKf_le : Kf ≤ K := by
    dsimp [K]
    linarith [hKg.1]
  have hKg_le : Kg ≤ K := by
    dsimp [K]
    linarith [hKf.1]
  have hf (n : ℕ) :
      Schwartz243SingleFieldRootBound244 (F.approximants n) K := by
    intro p
    obtain ⟨ha, hb, hc⟩ := hKf.2 n p
    exact ⟨ha.trans hKf_le, hb.trans hKf_le, hc.trans hKf_le⟩
  have hg (n : ℕ) :
      Schwartz243SingleFieldRootBound244 (G.approximants n) K := by
    intro p
    obtain ⟨ha, hb, hc⟩ := hKg.2 n p
    exact ⟨ha.trans hKg_le, hb.trans hKg_le, hc.trans hKg_le⟩
  let C : ℝ := 6 * (Fintype.card SchwartzStrongJetSlots244 : ℝ) * (K * K)
  have hUpper (n : ℕ) :
      2 * (∑ p : SchwartzStrongJetSlots244,
        schwartzPhysicalSlotPerturbation244
          (F.approximants n) (G.approximants n) p) ≤
        C * schwartzMixedJetGraphDistance244
          (F.approximants n) (G.approximants n) := by
    exact lowNormalRealSchwartz_firstMonomial_crossGraph_bound244
      (F.approximants n) (G.approximants n) K hK (hf n) (hg n)
  have hNonneg (n : ℕ) :
      0 ≤ 2 * (∑ p : SchwartzStrongJetSlots244,
        schwartzPhysicalSlotPerturbation244
          (F.approximants n) (G.approximants n) p) :=
    (abs_nonneg _).trans
      (lowNormalRealSchwartz_fullMonomial_integratedStability244
        (F.approximants n) (G.approximants n))
  have hScaled :
      Tendsto (fun n => C * schwartzMixedJetGraphDistance244
        (F.approximants n) (G.approximants n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hCross
  have hCrossError :
      Tendsto (fun n => 2 * (∑ p : SchwartzStrongJetSlots244,
        schwartzPhysicalSlotPerturbation244
          (F.approximants n) (G.approximants n) p)) atTop (𝓝 0) := by
    apply squeeze_zero
    · exact hNonneg
    · exact hUpper
    · exact hScaled
  exact lowNormalRealSchwartz_firstMonomial_limits_eq_of_crossError244
    F.approximants G.approximants
    (completedSchwartzH3FirstMonomial244 F)
    (completedSchwartzH3FirstMonomial244 G)
    (completedSchwartzH3FirstMonomial_tendsto244 F)
    (completedSchwartzH3FirstMonomial_tendsto244 G)
    hCrossError

end
end PrimeTensor.FirstMonomialTriad

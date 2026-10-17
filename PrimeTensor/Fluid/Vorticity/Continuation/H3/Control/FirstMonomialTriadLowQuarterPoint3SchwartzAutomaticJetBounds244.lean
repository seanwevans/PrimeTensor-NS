import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzUniformJetCauchy244
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Automatic uniform Schwartz jet bounds from strong jet Cauchy control

The preceding 243-slot signed-mononomial completion required (i) Cauchy
smallness of the three actual derivative differences in L²/L⁴ and
(ii) an independent global bound K on all third/second jet norms.

This module proves that (ii) is a consequence of (i). The real L² norm is
first identified with mathlib's eLpNorm; Minkowski yields its reverse
triangle estimate. The already proved L⁴ reverse triangle is reused.
Each scalar jet-root sequence is then Cauchy and therefore bounded. One
finite sum of 243 individual bounds supplies a common K, valid at EVERY n.

No Sobolev density or identification with the physical H³ path is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeAutomaticJet244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact integral L² square-root is the genuine extended-real L² norm. -/
private theorem schwartzL2Root_eq_eLpNorm244 (f : SchwartzMap V3 ℝ) :
    eLpNorm (f : V3 → ℝ) (ENNReal.ofReal (2 : ℝ)) (volume : Measure V3) =
      ENNReal.ofReal (schwartzIntegralL2Root244 f) := by
  have hRaw :
      realLpEnorm volume 2 (f : V3 → ℝ) =
        eLpNorm (f : V3 → ℝ) (ENNReal.ofReal (2 : ℝ))
          (volume : Measure V3) := by
    unfold realLpEnorm
    have hELp :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (p := ENNReal.ofReal (2 : ℝ))
        (μ := (volume : Measure V3))
        (f := (f : V3 → ℝ)) (by norm_num) (by simp)
    symm
    simpa only [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 : ℝ))] using hELp
  calc
    eLpNorm (f : V3 → ℝ) (ENNReal.ofReal (2 : ℝ)) (volume : Measure V3) =
        realLpEnorm volume 2 (f : V3 → ℝ) := hRaw.symm
    _ = ENNReal.ofReal (schwartzIntegralL2Root244 f) := by
      simpa only [schwartzIntegralL2Root244] using
        lowNormalSchwartz_realLpEnorm_two_eq_actualRoot244 f

/-- The actual L² square-root satisfies Minkowski in ordinary reals. -/
theorem schwartzIntegralL2Root_le_add_difference244
    (f g : SchwartzMap V3 ℝ) :
    schwartzIntegralL2Root244 f ≤
      schwartzIntegralL2Root244 (f - g) +
        schwartzIntegralL2Root244 g := by
  let p : ENNReal := ENNReal.ofReal (2 : ℝ)
  have hp : (1 : ENNReal) ≤ p := by
    dsimp [p]
    norm_num
  have hFn :
      (((f - g : SchwartzMap V3 ℝ) : V3 → ℝ) + (g : V3 → ℝ)) =
        (f : V3 → ℝ) := by
    funext x
    simp only [Pi.add_apply, sub_apply]
    ring
  have hTriangle :
      eLpNorm (f : V3 → ℝ) p (volume : Measure V3) ≤
        eLpNorm ((f - g : SchwartzMap V3 ℝ) : V3 → ℝ) p
          (volume : Measure V3) +
        eLpNorm (g : V3 → ℝ) p (volume : Measure V3) := by
    have hDiffMeas :
        AEStronglyMeasurable
          ((f - g : SchwartzMap V3 ℝ) : V3 → ℝ)
          (volume : Measure V3) :=
      (f - g).continuous.aestronglyMeasurable
    have hGMeas :
        AEStronglyMeasurable (g : V3 → ℝ) (volume : Measure V3) :=
      g.continuous.aestronglyMeasurable
    have h := MeasureTheory.eLpNorm_add_le
      (f := ((f - g : SchwartzMap V3 ℝ) : V3 → ℝ))
      (g := (g : V3 → ℝ)) (μ := (volume : Measure V3))
      (p := p) hDiffMeas hGMeas hp
    rw [hFn] at h
    exact h
  have hRoots :
      ENNReal.ofReal (schwartzIntegralL2Root244 f) ≤
        ENNReal.ofReal (schwartzIntegralL2Root244 (f - g)) +
          ENNReal.ofReal (schwartzIntegralL2Root244 g) := by
    dsimp [p] at hTriangle
    simpa only [schwartzL2Root_eq_eLpNorm244] using hTriangle
  have hd := schwartzIntegralL2Root244_nonneg (f - g)
  have hg := schwartzIntegralL2Root244_nonneg g
  have hPacked :
      ENNReal.ofReal (schwartzIntegralL2Root244 f) ≤
        ENNReal.ofReal
          (schwartzIntegralL2Root244 (f - g) +
            schwartzIntegralL2Root244 g) := by
    rw [ENNReal.ofReal_add hd hg]
    exact hRoots
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hd hg)).mp hPacked

/-- L² is insensitive to swapping the order of a Schwartz difference. -/
theorem schwartzIntegralL2Root_sub_comm244
    (f g : SchwartzMap V3 ℝ) :
    schwartzIntegralL2Root244 (f - g) =
      schwartzIntegralL2Root244 (g - f) := by
  have hIntegral :
      (∫ x : V3, ((f - g) x) ^ 2) =
        (∫ x : V3, ((g - f) x) ^ 2) := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [sub_apply]
    ring
  unfold schwartzIntegralL2Root244
  exact congrArg Real.sqrt hIntegral

/-- Exact real L² reverse triangle inequality, including zero norms. -/
theorem schwartzIntegralL2Root_abs_sub_le_difference244
    (f g : SchwartzMap V3 ℝ) :
    |schwartzIntegralL2Root244 f - schwartzIntegralL2Root244 g| ≤
      schwartzIntegralL2Root244 (f - g) := by
  have hfg := schwartzIntegralL2Root_le_add_difference244 f g
  have hgf := schwartzIntegralL2Root_le_add_difference244 g f
  rw [← schwartzIntegralL2Root_sub_comm244 f g] at hgf
  apply abs_le.mpr
  constructor <;> linarith

private abbrev automaticThird244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.1}
      (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.2)))

private abbrev automaticMiddle244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.2.1}
    (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.1))

private abbrev automaticCross244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.2.2.1} (f p.2.2.2.2))

/-- A scalar root sequence is Cauchy if its pairwise difference roots vanish. -/
private theorem automaticThird_root_cauchy244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hJets : Schwartz243StrongJetCauchy244 f)
    (p : SchwartzStrongJetSlots244) :
    CauchySeq (fun n =>
      schwartzIntegralL2Root244 (automaticThird244 (f n) p)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hJets p ε hε
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (schwartzIntegralL2Root_abs_sub_le_difference244
      (automaticThird244 (f m) p) (automaticThird244 (f n) p))
    (hN m hm n hn).1

private theorem automaticMiddle_root_cauchy244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hJets : Schwartz243StrongJetCauchy244 f)
    (p : SchwartzStrongJetSlots244) :
    CauchySeq (fun n =>
      schwartzIntegralL4Root244 (automaticMiddle244 (f n) p)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hJets p ε hε
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (schwartzIntegralL4Root_abs_sub_le_difference244
      (automaticMiddle244 (f m) p) (automaticMiddle244 (f n) p))
    (hN m hm n hn).2.1

private theorem automaticCross_root_cauchy244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hJets : Schwartz243StrongJetCauchy244 f)
    (p : SchwartzStrongJetSlots244) :
    CauchySeq (fun n =>
      schwartzIntegralL4Root244 (automaticCross244 (f n) p)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hJets p ε hε
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (schwartzIntegralL4Root_abs_sub_le_difference244
      (automaticCross244 (f m) p) (automaticCross244 (f n) p))
    (hN m hm n hn).2.2

/-- A Cauchy sequence of real numbers has a GLOBAL scalar upper bound.
This follows from cauchySeq_bdd; initial indices are included. -/
private theorem real_root_upperBound_of_cauchy244
    (u : ℕ → ℝ) (hu : CauchySeq u) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, u n ≤ u 0 + B := by
  obtain ⟨B, hB, hBB⟩ := cauchySeq_bdd hu
  refine ⟨B, le_of_lt hB, ?_⟩
  intro n
  have hn := hBB n 0
  rw [Real.dist_eq] at hn
  have hlo := le_abs_self (u n - u 0)
  linarith

/-- Strong Cauchy convergence ALREADY forces all 243 jet-root norms
bounded by one real K ≥ 1. Thus the separate norm-boundedness assumption
in the preceding completion result can be discharged. -/
theorem Schwartz243StrongJetCauchy244.uniformRoots
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    (hJets : Schwartz243StrongJetCauchy244 f) :
    ∃ K : ℝ, Schwartz243UniformJetRoots244 f K := by
  classical
  have hPerSlot :
      ∀ p : SchwartzStrongJetSlots244,
        ∃ B : ℝ, 1 ≤ B ∧ ∀ n : ℕ,
          schwartzIntegralL2Root244 (automaticThird244 (f n) p) ≤ B ∧
          schwartzIntegralL4Root244 (automaticMiddle244 (f n) p) ≤ B ∧
          schwartzIntegralL4Root244 (automaticCross244 (f n) p) ≤ B := by
    intro p
    let A : ℕ → ℝ := fun n =>
      schwartzIntegralL2Root244 (automaticThird244 (f n) p)
    let B : ℕ → ℝ := fun n =>
      schwartzIntegralL4Root244 (automaticMiddle244 (f n) p)
    let C : ℕ → ℝ := fun n =>
      schwartzIntegralL4Root244 (automaticCross244 (f n) p)
    obtain ⟨RA, hRA0, hRA⟩ :=
      real_root_upperBound_of_cauchy244 A
        (automaticThird_root_cauchy244 f hJets p)
    obtain ⟨RB, hRB0, hRB⟩ :=
      real_root_upperBound_of_cauchy244 B
        (automaticMiddle_root_cauchy244 f hJets p)
    obtain ⟨RC, hRC0, hRC⟩ :=
      real_root_upperBound_of_cauchy244 C
        (automaticCross_root_cauchy244 f hJets p)
    let bound : ℝ := 1 + (A 0 + RA) + (B 0 + RB) + (C 0 + RC)
    have hA0 : 0 ≤ A 0 := schwartzIntegralL2Root244_nonneg _
    have hB0 : 0 ≤ B 0 := schwartzIntegralL4Root244_nonneg _
    have hC0 : 0 ≤ C 0 := schwartzIntegralL4Root244_nonneg _
    have hBound : 1 ≤ bound := by
      dsimp [bound]
      linarith
    refine ⟨bound, hBound, ?_⟩
    intro n
    have ha := hRA n
    have hb := hRB n
    have hc := hRC n
    dsimp [bound]
    constructor
    · linarith
    constructor
    · linarith
    · linarith
  choose κ hκ using hPerSlot
  let K : ℝ := 1 + ∑ p : SchwartzStrongJetSlots244, κ p
  have hκnonneg (p : SchwartzStrongJetSlots244) : 0 ≤ κ p :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (hκ p).1
  have hSumNonneg : 0 ≤ ∑ p : SchwartzStrongJetSlots244, κ p := by
    apply Finset.sum_nonneg
    intro p _
    exact hκnonneg p
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith
  have hSingle (p : SchwartzStrongJetSlots244) : κ p ≤ K := by
    have hp : κ p ≤ ∑ q : SchwartzStrongJetSlots244, κ q :=
      Finset.single_le_sum (fun q _ => hκnonneg q) (Finset.mem_univ p)
    dsimp [K]
    linarith
  refine ⟨K, ⟨hK, ?_⟩⟩
  intro n p
  obtain ⟨ha, hb, hc⟩ := (hκ p).2 n
  exact ⟨le_trans ha (hSingle p),
    le_trans hb (hSingle p), le_trans hc (hSingle p)⟩

/-- The signed first monomial has a real Cauchy limit from the THREE
strong jet Cauchy properties alone, with no extra global root bound. -/
theorem lowNormalRealSchwartz_firstMonomial_existsLimit_of_strongJetCauchy244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hJets : Schwartz243StrongJetCauchy244 f) :
    ∃ M : ℝ,
      Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (f n))
        atTop (𝓝 M) := by
  obtain ⟨K, hK⟩ := hJets.uniformRoots
  exact lowNormalRealSchwartz_firstMonomial_existsLimit_of_uniformStrongJets244
    f K hK hJets

end
end PrimeTensor.FirstMonomialTriad

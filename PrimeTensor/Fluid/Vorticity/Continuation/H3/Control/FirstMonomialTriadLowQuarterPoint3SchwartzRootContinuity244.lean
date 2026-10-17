import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzStrongJetContinuity244
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Remove the redundant L4 root limits from Schwartz strong-jet continuity

The previous physical 243-slot convergence theorem asked for three DIFFERENCE
jet norms tending to zero and, separately, two unperturbed second-jet norms
converging to the norm of a fixed Schwartz target. The latter two requirements
follow from the reverse triangle inequality in genuine L4.

We transport mathlib's extended Lp Minkowski inequality through the project's
proved real fourth-root integral formula. The resulting real inequality

  |N4(f) - N4(g)| <= N4(f-g)

is valid for every pair of real Schwartz fields, including zero norms.
Consequently THREE per-slot limits (D3 in L2; both D2 factors in L4) suffice
to derive convergence of the complete signed 243-slot first monomial.

No Schwartz approximation of an arbitrary H3 physical path, and no H4 graph
density theorem, is asserted here. These remain substantive separate tasks.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeRootContinuity244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The already-proved real L4 root is precisely mathlib's ENNReal L4 norm
on the actual Euclidean Schwartz carrier, with no hidden normalization. -/
private theorem schwartzL4Root_eq_eLpNorm244 (f : SchwartzMap V3 ℝ) :
    eLpNorm (f : V3 → ℝ) (ENNReal.ofReal (4 : ℝ)) (volume : Measure V3) =
      ENNReal.ofReal (schwartzIntegralL4Root244 f) := by
  have hRaw :
      realLpEnorm volume 4 (f : V3 → ℝ) =
        eLpNorm (f : V3 → ℝ) (ENNReal.ofReal (4 : ℝ))
          (volume : Measure V3) := by
    unfold realLpEnorm
    have hELp :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (p := ENNReal.ofReal (4 : ℝ))
        (μ := (volume : Measure V3))
        (f := (f : V3 → ℝ)) (by norm_num) (by simp)
    symm
    simpa only [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (4 : ℝ))] using hELp
  calc
    eLpNorm (f : V3 → ℝ) (ENNReal.ofReal (4 : ℝ)) (volume : Measure V3) =
        realLpEnorm volume 4 (f : V3 → ℝ) := hRaw.symm
    _ = ENNReal.ofReal (schwartzIntegralL4Root244 f) := by
      simpa only [schwartzIntegralL4Root244] using
        lowNormalSchwartz_realLpEnorm_four_eq_actualRoot244 f

/-- Genuine Minkowski inequality for the *real fourth-root integral*.
Its proof uses mathlib L4, not a pointwise surrogate for the spatial norm. -/
theorem schwartzIntegralL4Root_le_add_difference244
    (f g : SchwartzMap V3 ℝ) :
    schwartzIntegralL4Root244 f ≤
      schwartzIntegralL4Root244 (f - g) +
        schwartzIntegralL4Root244 g := by
  let p : ENNReal := ENNReal.ofReal (4 : ℝ)
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
      ENNReal.ofReal (schwartzIntegralL4Root244 f) ≤
        ENNReal.ofReal (schwartzIntegralL4Root244 (f - g)) +
          ENNReal.ofReal (schwartzIntegralL4Root244 g) := by
    dsimp [p] at hTriangle
    simpa only [schwartzL4Root_eq_eLpNorm244] using hTriangle
  have hd := schwartzIntegralL4Root244_nonneg (f - g)
  have hg := schwartzIntegralL4Root244_nonneg g
  have hPacked :
      ENNReal.ofReal (schwartzIntegralL4Root244 f) ≤
        ENNReal.ofReal
          (schwartzIntegralL4Root244 (f - g) +
            schwartzIntegralL4Root244 g) := by
    rw [ENNReal.ofReal_add hd hg]
    exact hRoots
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hd hg)).mp hPacked

/-- Fourth-power integration does not depend on the order of subtraction. -/
theorem schwartzIntegralL4Root_sub_comm244
    (f g : SchwartzMap V3 ℝ) :
    schwartzIntegralL4Root244 (f - g) =
      schwartzIntegralL4Root244 (g - f) := by
  have hIntegral :
      (∫ x : V3, ((f - g) x) ^ 4) =
        (∫ x : V3, ((g - f) x) ^ 4) := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [sub_apply]
    ring
  unfold schwartzIntegralL4Root244
  exact congrArg (fun x : ℝ => Real.sqrt (Real.sqrt x)) hIntegral

/-- Reverse triangle inequality for genuine Schwartz L4 integral roots.
In particular the estimate includes functions having zero L4 norm. -/
theorem schwartzIntegralL4Root_abs_sub_le_difference244
    (f g : SchwartzMap V3 ℝ) :
    |schwartzIntegralL4Root244 f - schwartzIntegralL4Root244 g| ≤
      schwartzIntegralL4Root244 (f - g) := by
  have hfg := schwartzIntegralL4Root_le_add_difference244 f g
  have hgf := schwartzIntegralL4Root_le_add_difference244 g f
  rw [← schwartzIntegralL4Root_sub_comm244 f g] at hgf
  apply abs_le.mpr
  constructor <;> linarith

/-- A vanishing L4 difference norm forces convergence of the original
L4 norms. This is the exact previously missing pair of root limits. -/
theorem schwartzIntegralL4Root_tendsto_of_difference244
    (f : ℕ → SchwartzMap V3 ℝ) (g : SchwartzMap V3 ℝ)
    (hDiff : Tendsto (fun n => schwartzIntegralL4Root244 (f n - g))
      atTop (𝓝 0)) :
    Tendsto (fun n => schwartzIntegralL4Root244 (f n))
      atTop (𝓝 (schwartzIntegralL4Root244 g)) := by
  have hAbs :
      Tendsto (fun n =>
        |schwartzIntegralL4Root244 (f n) -
          schwartzIntegralL4Root244 g|) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact abs_nonneg _
    · intro n
      exact schwartzIntegralL4Root_abs_sub_le_difference244 (f n) g
    · exact hDiff
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hAbs

/-- The same actual derivative-index arrangement as the earlier strong-jet
module, repeated locally because that module correctly keeps its abbreviations
private. -/
private abbrev rootThird244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.1}
      (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.2)))

private abbrev rootMiddle244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.2.1}
    (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.1))

private abbrev rootCross244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.2.2.1} (f p.2.2.2.2))

/-- Only the three actual DIFFERENCE jet norms need to tend to zero:
one third-derivative L2 norm and two second-derivative L4 norms per slot. -/
def SchwartzThreeDifferenceJetConvergence244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ) : Prop :=
  ∀ p : SchwartzStrongJetSlots244,
    Tendsto (fun n => schwartzIntegralL2Root244
      (rootThird244 (f n) p - rootThird244 g p)) atTop (𝓝 0) ∧
    Tendsto (fun n => schwartzIntegralL4Root244
      (rootMiddle244 (f n) p - rootMiddle244 g p)) atTop (𝓝 0) ∧
    Tendsto (fun n => schwartzIntegralL4Root244
      (rootCross244 (f n) p - rootCross244 g p)) atTop (𝓝 0)

/-- Supply the two previously independent L4-root limits using Minkowski.
No new assumptions are added to the difference-jet convergence predicate. -/
theorem SchwartzThreeDifferenceJetConvergence244.toStrongJets
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    (hJets : SchwartzThreeDifferenceJetConvergence244 f g) :
    SchwartzStrongJetConvergence244 f g := by
  intro p
  obtain ⟨hThird, hMiddle, hCross⟩ := hJets p
  exact ⟨hThird, hMiddle, hCross,
    schwartzIntegralL4Root_tendsto_of_difference244
      (fun n => rootMiddle244 (f n) p) (rootMiddle244 g p) hMiddle,
    schwartzIntegralL4Root_tendsto_of_difference244
      (fun n => rootCross244 (f n) p) (rootCross244 g p) hCross⟩

/-- The complete signed 243-slot monomial converges from just three
strong difference jets per slot, with no extra L4-root hypotheses. -/
theorem lowNormalRealSchwartz_firstMonomial_tendsto_of_threeDifferenceJets244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ)
    (hJets : SchwartzThreeDifferenceJetConvergence244 f g) :
    Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (f n)) atTop
      (𝓝 (lowNormalRealSchwartzPoint3Monomial g)) := by
  exact lowNormalRealSchwartz_firstMonomial_tendsto_of_strongJets244
    f g hJets.toStrongJets

/-- PDE-facing packaging: the nonlinear limit now follows from just three
per-slot difference limits, while physical identification, E0, E1, and
fourth-order energy convergence remain explicit independent obligations. -/
theorem h3PathCanonical_approximable_of_threeDifferenceJets244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ)
    (hJets : SchwartzThreeDifferenceJetConvergence244 f g)
    (hPhysical : lowNormalRealSchwartzPoint3Monomial g =
      h3PathCanonicalFirstMonomialAggregateAt u t)
    (h0 : Tendsto (fun n => lowNormalRealSchwartzH3Energy0 (f n)) atTop
      (𝓝 (velocityH3Energy0At u t)))
    (h1 : Tendsto (fun n => lowNormalRealSchwartzH3Energy1 (f n)) atTop
      (𝓝 (velocityH3Energy1At u t)))
    (hD : Tendsto (fun n => lowNormalRealSchwartzH3TopDissipation (f n)) atTop
      (𝓝 (velocityH3Dissipation3At u t))) :
    H3SchwartzCriticalHalfApproximable244 u t := by
  exact h3PathCanonical_approximable_of_strongSchwartzJets244
    u t f g hJets.toStrongJets hPhysical h0 h1 hD

end
end PrimeTensor.FirstMonomialTriad

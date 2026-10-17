import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzH3CompletionInvariant244

/-!
# The completed signed first monomial is invariant under H³ energy equivalence

The preceding approximation-independence result requires the mixed 81+27
L²/L⁴ jet graph between two Schwartz Cauchy families to converge to zero.
Here we derive this cross-graph convergence from the ordinary second- and
third-order quadratic energies of their *difference* converging to zero.

For every third jet the square of the actual L² root is bounded by E₃,
and for every second jet the eighth power of its L⁴ root is bounded by
S⁶ E₂ (card(Axis 3) E₃)³. Continuity of the square root and threefold
square root transfers vanishing energy to each actual root. Finite sums
then give vanishing of the entire mixed graph, so the completed monomial
is independent of the approximation whenever cross E₂ and E₃ vanish.

This does not construct Schwartz approximants to arbitrary physical H³
velocities or identify a separate physical transport distribution.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeCrossEnergy244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- A nonnegative scalar with square at most `B` is at most `sqrt B`. -/
private theorem crossEnergy_nonneg_le_sqrt244
    {r B : ℝ} (hr : 0 ≤ r) (h : r ^ 2 ≤ B) :
    r ≤ Real.sqrt B := by
  calc
    r = Real.sqrt (r ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hr]
    _ ≤ Real.sqrt B := Real.sqrt_le_sqrt h

/-- Repeated monotonicity of the genuine real square root converts an
actual eighth-power bound to an eighth-root bound, including at zero. -/
private theorem crossEnergy_nonneg_le_eighthRoot244
    {r B : ℝ} (hr : 0 ≤ r) (h : r ^ 8 ≤ B) :
    r ≤ Real.sqrt (Real.sqrt (Real.sqrt B)) := by
  have h4 : r ^ 4 ≤ Real.sqrt B := by
    calc
      r ^ 4 = Real.sqrt (r ^ 8) := by
        rw [show r ^ 8 = (r ^ 4) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hr 4)]
      _ ≤ Real.sqrt B := Real.sqrt_le_sqrt h
  have h2 : r ^ 2 ≤ Real.sqrt (Real.sqrt B) := by
    calc
      r ^ 2 = Real.sqrt (r ^ 4) := by
        rw [show r ^ 4 = (r ^ 2) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hr 2)]
      _ ≤ Real.sqrt (Real.sqrt B) := Real.sqrt_le_sqrt h4
  calc
    r = Real.sqrt (r ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hr]
    _ ≤ Real.sqrt (Real.sqrt (Real.sqrt B)) := Real.sqrt_le_sqrt h2

/-- Pointwise convergence of finitely many real sequences to zero implies
convergence of their entire finite sum to zero. -/
private theorem crossEnergy_finiteSum_tendsto_zero244
    {J : Type*} [Fintype J]
    (e : ℕ → J → ℝ)
    (he : ∀ p : J, Tendsto (fun n => e n p) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ p : J, e n p) atTop (𝓝 0) := by
  classical
  have hs (s : Finset J) :
      Tendsto (fun n => Finset.sum s (e n)) atTop (𝓝 0) := by
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert p s hp ih =>
        simpa only [Finset.sum_insert hp, zero_add] using (he p).add ih
  exact hs (Finset.univ : Finset J)

/-- The ordinary E₂ and E₃ difference energies of two Schwartz sequences
both converge to zero at corresponding indices. -/
def SchwartzH3CrossEnergyVanishing244
    (f g : ℕ → A3 → SchwartzMap V3 ℝ) : Prop :=
  Tendsto (fun n => lowNormalRealSchwartzH3Energy2
      (schwartzVelocityDifference244 (f n) (g n))) atTop (𝓝 0) ∧
  Tendsto (fun n => lowNormalRealSchwartzH3Energy3
      (schwartzVelocityDifference244 (f n) (g n))) atTop (𝓝 0)

/-- Actual H³ energy convergence controls the ENTIRE 81+27 mixed graph.
The two fourth-root factors are not postulated convergent: their convergence
is derived using the established full 27-slot quartic GN inequality. -/
theorem schwartzMixedJetGraph_tendsto_zero_of_crossEnergy244
    (f g : ℕ → A3 → SchwartzMap V3 ℝ)
    (hCross : SchwartzH3CrossEnergyVanishing244 f g) :
    Tendsto (fun n => schwartzMixedJetGraphDistance244 (f n) (g n))
      atTop (𝓝 0) := by
  let E2 : ℕ → ℝ := fun n => lowNormalRealSchwartzH3Energy2
    (schwartzVelocityDifference244 (f n) (g n))
  let E3 : ℕ → ℝ := fun n => lowNormalRealSchwartzH3Energy3
    (schwartzVelocityDifference244 (f n) (g n))
  have hE2 : Tendsto E2 atTop (𝓝 0) := hCross.1
  have hE3 : Tendsto E3 atTop (𝓝 0) := hCross.2
  have hSqrtE3 :
      Tendsto (fun n => Real.sqrt (E3 n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hE3)
  let B : ℕ → ℝ := fun n =>
    lowNormalSecondJetSobolevRealConstant ^ 6 *
      (E2 n * (((Fintype.card A3 : ℝ) * E3 n) ^ 3))
  have hScaledE3 :
      Tendsto (fun n => (Fintype.card A3 : ℝ) * E3 n)
        atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (Fintype.card A3 : ℝ))
        atTop (𝓝 (Fintype.card A3 : ℝ))).mul hE3
  have hCubed :
      Tendsto (fun n => ((Fintype.card A3 : ℝ) * E3 n) ^ 3)
        atTop (𝓝 0) := by
    simpa using hScaledE3.pow 3
  have hB : Tendsto B atTop (𝓝 0) := by
    have hProduct := hE2.mul hCubed
    have hCoefficient : Tendsto
        (fun _ : ℕ => lowNormalSecondJetSobolevRealConstant ^ 6)
        atTop (𝓝 (lowNormalSecondJetSobolevRealConstant ^ 6)) :=
      tendsto_const_nhds
    simpa only [B, zero_mul, mul_zero] using hCoefficient.mul hProduct
  have hSqrt1 :
      Tendsto (fun n => Real.sqrt (B n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hB)
  have hSqrt2 :
      Tendsto (fun n => Real.sqrt (Real.sqrt (B n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hSqrt1)
  have hSqrt3 :
      Tendsto (fun n => Real.sqrt (Real.sqrt (Real.sqrt (B n))))
        atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hSqrt2)
  have hThird (j i k l : A3) :
      Tendsto (fun n => schwartzThirdJetDifferenceRoot244
        (f n) (g n) j i k l) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact schwartzIntegralL2Root244_nonneg _
    · intro n
      have hSq := schwartzThirdJetDifferenceRoot_sq_le_E3244
        (f n) (g n) j i k l
      change (schwartzThirdJetDifferenceRoot244
        (f n) (g n) j i k l) ^ 2 ≤ E3 n at hSq
      exact crossEnergy_nonneg_le_sqrt244
        (schwartzIntegralL2Root244_nonneg _) hSq
    · exact hSqrtE3
  have hSecond (j i k : A3) :
      Tendsto (fun n => schwartzSecondJetDifferenceRoot244
        (f n) (g n) j i k) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact schwartzIntegralL4Root244_nonneg _
    · intro n
      have hEight := schwartzSecondJetDifferenceRoot_pow_eight_le_E2E3244
        (f n) (g n) j i k
      change (schwartzSecondJetDifferenceRoot244
        (f n) (g n) j i k) ^ 8 ≤ B n at hEight
      exact crossEnergy_nonneg_le_eighthRoot244
        (schwartzIntegralL4Root244_nonneg _) hEight
    · exact hSqrt3
  have hThirdSum :
      Tendsto (fun n => schwartzThirdJetGraphDistance244 (f n) (g n))
        atTop (𝓝 0) := by
    have hTerms : ∀ p : A3 × (A3 × (A3 × A3)),
        Tendsto (fun n => schwartzThirdJetDifferenceRoot244
          (f n) (g n) p.1 p.2.1 p.2.2.1 p.2.2.2)
          atTop (𝓝 0) := by
      rintro ⟨j, i, k, l⟩
      exact hThird j i k l
    have hFinite := crossEnergy_finiteSum_tendsto_zero244
      (fun n (p : A3 × (A3 × (A3 × A3))) =>
        schwartzThirdJetDifferenceRoot244
          (f n) (g n) p.1 p.2.1 p.2.2.1 p.2.2.2) hTerms
    simpa only [schwartzThirdJetGraphDistance244,
      Fintype.sum_prod_type] using hFinite
  have hSecondSum :
      Tendsto (fun n => schwartzSecondJetGraphDistance244 (f n) (g n))
        atTop (𝓝 0) := by
    have hTerms : ∀ p : A3 × (A3 × A3),
        Tendsto (fun n => schwartzSecondJetDifferenceRoot244
          (f n) (g n) p.1 p.2.1 p.2.2) atTop (𝓝 0) := by
      rintro ⟨j, i, k⟩
      exact hSecond j i k
    have hFinite := crossEnergy_finiteSum_tendsto_zero244
      (fun n (p : A3 × (A3 × A3)) =>
        schwartzSecondJetDifferenceRoot244
          (f n) (g n) p.1 p.2.1 p.2.2) hTerms
    simpa only [schwartzSecondJetGraphDistance244,
      Fintype.sum_prod_type] using hFinite
  simpa only [schwartzMixedJetGraphDistance244, zero_add] using
    hThirdSum.add hSecondSum

/-- Two completed H³ Schwartz families are equivalent in their genuine
quadratic difference energies, rather than in a separately postulated graph. -/
def SchwartzH3FamiliesCrossEnergyVanishing244
    (F G : SchwartzH3CauchyFamily244) : Prop :=
  SchwartzH3CrossEnergyVanishing244 F.approximants G.approximants

/-- Approximation independence of the signed completed transport observable
under ordinary E₂/E₃ Sobolev-energy equivalence. -/
theorem completedSchwartzH3FirstMonomial_eq_of_crossEnergy244
    (F G : SchwartzH3CauchyFamily244)
    (hCross : SchwartzH3FamiliesCrossEnergyVanishing244 F G) :
    completedSchwartzH3FirstMonomial244 F =
      completedSchwartzH3FirstMonomial244 G :=
  completedSchwartzH3FirstMonomial_eq_of_crossGraph244 F G
    (schwartzMixedJetGraph_tendsto_zero_of_crossEnergy244
      F.approximants G.approximants hCross)

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzIntegratedStability244
import Mathlib.Topology.Algebra.Order.Field

/-!
# Strong Schwartz jet convergence implies signed 243-slot monomial convergence

The earlier integrated 2-4-4 inequality bounds the change in the full signed
first monomial by a finite sum of explicit error envelopes. Here each of the
243 envelopes is proved to vanish when its third derivative converges in the
actual L2 root and both second derivatives converge in the actual L4 roots,
provided the two undifferenced, variable L4 roots also converge to their
finite Schwartz targets.

This is a genuine nonlinear continuity argument: convergence of the monomial
is the conclusion, not a premise. The extra L4-root convergence assumptions
are explicit (they should ultimately follow from L4 norm continuity).

The target in this file is a fixed real Schwartz family g. Extending to an
arbitrary H3 physical Sobolev slice still requires a graph-density theorem
and identification of its physical triple-product pairings with the limits.
No regularity or continuation conclusion is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

/-- The five ordered physical indices, with 3^5 = 243 slots. -/
abbrev SchwartzStrongJetSlots244 := A3 × (A3 × (A3 × (A3 × A3)))

noncomputable local instance axisFintypeStrongJet244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exactly the third-order factor of one physical signed slot. -/
private abbrev strongThird244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.1}
      (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.2)))

/-- Exactly the first second-order factor of one physical signed slot. -/
private abbrev strongMiddle244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.2.1}
    (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.1))

/-- Exactly the other second-order factor of one physical signed slot. -/
private abbrev strongCross244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.2.2.1} (f p.2.2.2.2))

/-- Five explicit strong-jet/root limits at each of the 243 slots.
The first three are difference norms; the last two are convergence of
undifferenced L4 roots, needed to control the other factors of the product. -/
def SchwartzStrongJetConvergence244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ) : Prop :=
  ∀ p : SchwartzStrongJetSlots244,
    Tendsto (fun n => schwartzIntegralL2Root244
      (strongThird244 (f n) p - strongThird244 g p)) atTop (𝓝 0) ∧
    Tendsto (fun n => schwartzIntegralL4Root244
      (strongMiddle244 (f n) p - strongMiddle244 g p)) atTop (𝓝 0) ∧
    Tendsto (fun n => schwartzIntegralL4Root244
      (strongCross244 (f n) p - strongCross244 g p)) atTop (𝓝 0) ∧
    Tendsto (fun n => schwartzIntegralL4Root244
      (strongMiddle244 (f n) p)) atTop
      (𝓝 (schwartzIntegralL4Root244 (strongMiddle244 g p))) ∧
    Tendsto (fun n => schwartzIntegralL4Root244
      (strongCross244 (f n) p)) atTop
      (𝓝 (schwartzIntegralL4Root244 (strongCross244 g p)))

/-- One integrated 2-4-4 error envelope converges to zero under the five
actual root limits. No trilinear integral limit is assumed. -/
theorem schwartzPhysicalSlotPerturbation_tendsto_zero244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ)
    (hJets : SchwartzStrongJetConvergence244 f g)
    (p : SchwartzStrongJetSlots244) :
    Tendsto (fun n => schwartzPhysicalSlotPerturbation244 (f n) g p)
      atTop (𝓝 0) := by
  obtain ⟨hThird, hMiddle, hCross, hMiddleNorm, hCrossNorm⟩ := hJets p
  have hFirst :
      Tendsto (fun n =>
        schwartzIntegralL2Root244
          (strongThird244 (f n) p - strongThird244 g p) *
        (schwartzIntegralL4Root244 (strongMiddle244 (f n) p) *
          schwartzIntegralL4Root244 (strongCross244 (f n) p)))
        atTop (𝓝 0) := by
    simpa only [zero_mul] using hThird.mul (hMiddleNorm.mul hCrossNorm)
  have hSecond :
      Tendsto (fun n =>
        schwartzIntegralL2Root244 (strongThird244 g p) *
        (schwartzIntegralL4Root244
          (strongMiddle244 (f n) p - strongMiddle244 g p) *
          schwartzIntegralL4Root244 (strongCross244 (f n) p)))
        atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => schwartzIntegralL2Root244 (strongThird244 g p))
        atTop (𝓝 (schwartzIntegralL2Root244 (strongThird244 g p)))).mul
        (hMiddle.mul hCrossNorm)
  have hThirdTerm :
      Tendsto (fun n =>
        schwartzIntegralL2Root244 (strongThird244 g p) *
        (schwartzIntegralL4Root244 (strongMiddle244 g p) *
          schwartzIntegralL4Root244
            (strongCross244 (f n) p - strongCross244 g p)))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => schwartzIntegralL2Root244 (strongThird244 g p))
        atTop (𝓝 (schwartzIntegralL2Root244 (strongThird244 g p)))).mul
        ((tendsto_const_nhds : Tendsto
          (fun _ : ℕ => schwartzIntegralL4Root244 (strongMiddle244 g p))
          atTop (𝓝 (schwartzIntegralL4Root244 (strongMiddle244 g p)))).mul
          hCross)
  change Tendsto (fun n =>
    schwartzIntegralL2Root244
      (strongThird244 (f n) p - strongThird244 g p) *
      (schwartzIntegralL4Root244 (strongMiddle244 (f n) p) *
        schwartzIntegralL4Root244 (strongCross244 (f n) p)) +
    schwartzIntegralL2Root244 (strongThird244 g p) *
      (schwartzIntegralL4Root244
        (strongMiddle244 (f n) p - strongMiddle244 g p) *
        schwartzIntegralL4Root244 (strongCross244 (f n) p)) +
    schwartzIntegralL2Root244 (strongThird244 g p) *
      (schwartzIntegralL4Root244 (strongMiddle244 g p) *
        schwartzIntegralL4Root244
          (strongCross244 (f n) p - strongCross244 g p)))
    atTop (𝓝 0)
  simpa only [zero_add] using (hFirst.add hSecond).add hThirdTerm

/-- A finite sum of nonnegative (or signed) real errors tending to zero
also tends to zero. This does not hide any uniform-in-index assumption. -/
private theorem finiteSchwartzSlotError_tendsto_zero244
    {J : Type*} [Fintype J]
    (E : ℕ → J → ℝ)
    (hE : ∀ p : J, Tendsto (fun n => E n p) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ p : J, E n p) atTop (𝓝 0) := by
  classical
  have hs (s : Finset J) :
      Tendsto (fun n => Finset.sum s (E n)) atTop (𝓝 0) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using
          (tendsto_const_nhds : Tendsto
            (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | @insert p s hp ih =>
        simpa only [Finset.sum_insert hp, zero_add] using (hE p).add ih
  exact hs (Finset.univ : Finset J)

/-- The entire signed 243-slot Schwartz first monomial is sequentially
continuous under explicit physical L2/L4 jet-root convergence. The signed
monomial convergence is derived from the integrated inequality; it is NOT
part of `SchwartzStrongJetConvergence244`. -/
theorem lowNormalRealSchwartz_firstMonomial_tendsto_of_strongJets244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ)
    (hJets : SchwartzStrongJetConvergence244 f g) :
    Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (f n)) atTop
      (𝓝 (lowNormalRealSchwartzPoint3Monomial g)) := by
  have hSum :
      Tendsto (fun n =>
        ∑ p : SchwartzStrongJetSlots244,
          schwartzPhysicalSlotPerturbation244 (f n) g p)
        atTop (𝓝 0) :=
    finiteSchwartzSlotError_tendsto_zero244
      (fun n p => schwartzPhysicalSlotPerturbation244 (f n) g p)
      (schwartzPhysicalSlotPerturbation_tendsto_zero244 f g hJets)
  have hUpper :
      Tendsto (fun n => 2 *
        (∑ p : SchwartzStrongJetSlots244,
          schwartzPhysicalSlotPerturbation244 (f n) g p))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 (2 : ℝ))).mul hSum
  have hAbs :
      Tendsto (fun n =>
        |lowNormalRealSchwartzPoint3Monomial (f n) -
          lowNormalRealSchwartzPoint3Monomial g|) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact abs_nonneg _
    · intro n
      exact lowNormalRealSchwartz_fullMonomial_integratedStability244 (f n) g
    · exact hUpper
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hAbs

/-- The PDE-facing approximation predicate follows once the physical signed
aggregate is identified with a fixed Schwartz limit and the three physical
quadratic energy limits are provided. The nonlinear limit is now DERIVED from
jet convergence, not separately assumed. -/
theorem h3PathCanonical_approximable_of_strongSchwartzJets244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ)
    (hJets : SchwartzStrongJetConvergence244 f g)
    (hPhysical : lowNormalRealSchwartzPoint3Monomial g =
      h3PathCanonicalFirstMonomialAggregateAt u t)
    (h0 : Tendsto (fun n => lowNormalRealSchwartzH3Energy0 (f n)) atTop
      (𝓝 (velocityH3Energy0At u t)))
    (h1 : Tendsto (fun n => lowNormalRealSchwartzH3Energy1 (f n)) atTop
      (𝓝 (velocityH3Energy1At u t)))
    (hD : Tendsto (fun n => lowNormalRealSchwartzH3TopDissipation (f n)) atTop
      (𝓝 (velocityH3Dissipation3At u t))) :
    H3SchwartzCriticalHalfApproximable244 u t := by
  refine ⟨f, ?_, h0, h1, hD⟩
  rw [← hPhysical]
  exact lowNormalRealSchwartz_firstMonomial_tendsto_of_strongJets244 f g hJets

end
end PrimeTensor.FirstMonomialTriad

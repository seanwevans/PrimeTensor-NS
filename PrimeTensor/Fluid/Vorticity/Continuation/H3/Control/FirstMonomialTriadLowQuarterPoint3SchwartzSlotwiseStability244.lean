import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzApproximationClosure244
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Trilinear perturbations and 243-slot convergence toward physical H³ slices

The former approximation closure requires convergence of one global signed
nonlinear observable. This module reduces that requirement to limits of the
243 genuine physical triple-product slots. In parallel it proves the exact
three-term telescoping identity and a coefficient-one finite-sum perturbation
bound for arbitrary real arrays. These are the algebraic estimates needed to
prove the slot limits from L² × L⁴ × L⁴ derivative convergence.

Importantly, the scalar limits of the actual physical slots are still inputs:
this file does NOT claim that mere L² Schwartz density implies convergence of
any triple-product integral. Finite-index passage to the limit is proved here.
There is no new axiom, incompressibility assumption, or continuation result.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSlotwiseStability244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact three-factor telescoping with the signs retained. -/
theorem criticalHalf_trilinear_telescoping244
    (a b c a' b' c' : ℝ) :
    a * (b * c) - a' * (b' * c') =
      (a - a') * (b * c) +
        a' * ((b - b') * c) +
          a' * (b' * (c - c')) := by
  ring

/-- Coefficient-one stability envelope for a REAL signed triple product.
Neither factors nor their perturbations are required to be nonnegative. -/
theorem criticalHalf_trilinear_abs_difference_le244
    (a b c a' b' c' : ℝ) :
    |a * (b * c) - a' * (b' * c')| ≤
      |a - a'| * (|b| * |c|) +
        |a'| * (|b - b'| * |c|) +
          |a'| * (|b'| * |c - c'|) := by
  rw [criticalHalf_trilinear_telescoping244]
  calc
    |(a - a') * (b * c) + a' * ((b - b') * c) +
      a' * (b' * (c - c'))| ≤
        |(a - a') * (b * c) + a' * ((b - b') * c)| +
          |a' * (b' * (c - c'))| := abs_add_le _ _
    _ ≤ (|(a - a') * (b * c)| + |a' * ((b - b') * c)|) +
          |a' * (b' * (c - c'))| :=
      add_le_add (abs_add_le _ _) (le_refl _)
    _ = _ := by simp only [abs_mul]

/-- Finite-sum stability for the entire signed trilinear polynomial. The
bound has no combinatorial prefactor: each slot is counted exactly once. -/
theorem criticalHalf_finite_trilinear_difference_le244
    {J : Type*} [Fintype J]
    (a b c a' b' c' : J → ℝ) :
    |(∑ p : J, a p * (b p * c p)) -
      (∑ p : J, a' p * (b' p * c' p))| ≤
      ∑ p : J,
        (|a p - a' p| * (|b p| * |c p|) +
          |a' p| * (|b p - b' p| * |c p|) +
            |a' p| * (|b' p| * |c p - c' p|)) := by
  classical
  calc
    |(∑ p : J, a p * (b p * c p)) -
      (∑ p : J, a' p * (b' p * c' p))| =
        |∑ p : J, (a p * (b p * c p) -
          a' p * (b' p * c' p))| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ p : J, |a p * (b p * c p) -
          a' p * (b' p * c' p)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (Finset.univ : Finset J)
          (fun p => a p * (b p * c p) - a' p * (b' p * c' p)))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p _
      exact criticalHalf_trilinear_abs_difference_le244
        (a p) (b p) (c p) (a' p) (b' p) (c' p)

/-- A finite sum of real-valued sequences converges when each summand
converges. This deliberately does not assume uniform convergence in the
spatial variable, since only the finite coordinate index is summed. -/
private theorem criticalHalf_finite_sum_tendsto244
    {J : Type*} [Fintype J]
    (F : ℕ → J → ℝ) (L : J → ℝ)
    (h : ∀ p : J, Tendsto (fun n => F n p) atTop (𝓝 (L p))) :
    Tendsto (fun n => ∑ p : J, F n p) atTop
      (𝓝 (∑ p : J, L p)) := by
  classical
  have hs (s : Finset J) :
      Tendsto (fun n => Finset.sum s (F n)) atTop
        (𝓝 (Finset.sum s L)) := by
    -- Use one actual finite index rather than reducing the 243-coordinate sum.
    induction s using Finset.induction_on with
    | empty => simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | @insert p s hp ih =>
        simpa only [Finset.sum_insert hp] using (h p).add ih
  exact hs (Finset.univ : Finset J)

/-- The five ordered coordinate sums preserve pointwise scalar limits. -/
private theorem criticalHalf_fivefold_sum_tendsto244
    (F : ℕ → A3 → A3 → A3 → A3 → A3 → ℝ)
    (L : A3 → A3 → A3 → A3 → A3 → ℝ)
    (h : ∀ j r i k l, Tendsto (fun n => F n j r i k l)
      atTop (𝓝 (L j r i k l))) :
    Tendsto (fun n => ∑ j : A3, ∑ r : A3, ∑ i : A3,
      ∑ k : A3, ∑ l : A3, F n j r i k l) atTop
      (𝓝 (∑ j : A3, ∑ r : A3, ∑ i : A3,
        ∑ k : A3, ∑ l : A3, L j r i k l)) := by
  have hL (j r i k : A3) :=
    criticalHalf_finite_sum_tendsto244
      (fun n l => F n j r i k l) (fun l => L j r i k l)
      (fun l => h j r i k l)
  have hK (j r i : A3) :=
    criticalHalf_finite_sum_tendsto244
      (fun n k => ∑ l : A3, F n j r i k l)
      (fun k => ∑ l : A3, L j r i k l)
      (hL j r i)
  have hI (j r : A3) :=
    criticalHalf_finite_sum_tendsto244
      (fun n i => ∑ k : A3, ∑ l : A3, F n j r i k l)
      (fun i => ∑ k : A3, ∑ l : A3, L j r i k l)
      (hK j r)
  have hR (j : A3) :=
    criticalHalf_finite_sum_tendsto244
      (fun n r => ∑ i : A3, ∑ k : A3, ∑ l : A3, F n j r i k l)
      (fun r => ∑ i : A3, ∑ k : A3, ∑ l : A3, L j r i k l)
      (hI j)
  exact criticalHalf_finite_sum_tendsto244
    (fun n j => ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, F n j r i k l)
    (fun j => ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, L j r i k l)
    hR

/-- Full first-monomial Schwartz aggregate written in the SAME physical
ordered slots as the canonical signed path aggregate, including factor 2. -/
private theorem criticalHalf_schwartz_monomial_physicalOrder244
    (g : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzPoint3Monomial g =
      ∑ j : A3, ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
        2 * lowNormalRealSchwartz_firstMonomialSlotIntegral g i k l r j := by
  calc
    lowNormalRealSchwartzPoint3Monomial g =
        2 * (∑ i : A3, ∑ k : A3, ∑ l : A3,
          ∑ r : A3, ∑ j : A3,
            lowNormalRealSchwartz_firstMonomialSlotIntegral g i k l r j) :=
      lowNormalRealSchwartz_firstMonomial_eq_twice_slotSum g
    _ = ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
          2 * lowNormalRealSchwartz_firstMonomialSlotIntegral g i k l r j := by
      simp only [Finset.mul_sum]
    _ = _ := by
      simp only [axis_sum_three]
      ac_rfl

/-- Slotwise strong limit criterion. Its 243 scalar limits are concrete
physical pairings, not a new global transport hypothesis. E0, E1 and top
D limits are retained until a Sobolev graph-density proof discharges them. -/
def H3SchwartzSlotwiseCriticalHalfApproximable244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
    (∀ j r i k l : A3,
      Tendsto (fun n => 2 *
        lowNormalRealSchwartz_firstMonomialSlotIntegral (f n) i k l r j)
        atTop (𝓝 (h3PathCanonicalInterpolationMonomialPairing
          u t j i k l r 0))) ∧
    Tendsto (fun n => lowNormalRealSchwartzH3Energy0 (f n)) atTop
      (𝓝 (velocityH3Energy0At u t)) ∧
    Tendsto (fun n => lowNormalRealSchwartzH3Energy1 (f n)) atTop
      (𝓝 (velocityH3Energy1At u t)) ∧
    Tendsto (fun n => lowNormalRealSchwartzH3TopDissipation (f n)) atTop
      (𝓝 (velocityH3Dissipation3At u t))

/-- All 243 physical signed-slot limits imply the FOUR-observable
approximation condition of the previously closed critical-half theorem. -/
theorem h3PathCanonical_slotwise_implies_approximable244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hApprox : H3SchwartzSlotwiseCriticalHalfApproximable244 u t) :
    H3SchwartzCriticalHalfApproximable244 u t := by
  obtain ⟨f, hSlots, h0, h1, hD⟩ := hApprox
  refine ⟨f, ?_, h0, h1, hD⟩
  have hSum := criticalHalf_fivefold_sum_tendsto244
    (fun n j r i k l =>
      2 * lowNormalRealSchwartz_firstMonomialSlotIntegral (f n) i k l r j)
    (fun j r i k l =>
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0)
    hSlots
  have hSeq :
      (fun n : ℕ => ∑ j : A3, ∑ r : A3, ∑ i : A3,
        ∑ k : A3, ∑ l : A3,
          2 * lowNormalRealSchwartz_firstMonomialSlotIntegral (f n) i k l r j) =
      (fun n : ℕ => lowNormalRealSchwartzPoint3Monomial (f n)) := by
    funext n
    exact (criticalHalf_schwartz_monomial_physicalOrder244 (f n)).symm
  rw [hSeq] at hSum
  simpa only [h3PathCanonicalFirstMonomialAggregateAt] using hSum

/-- The unconditional Schwartz estimate applies directly to a physical
slice whenever its 243 signed slot pairings and energies admit the limits
specified above. No exact Schwartz realization is required. -/
theorem h3PathCanonical_thirdTransport_criticalHalf_of_slotwise244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hSlotwise : H3SchwartzSlotwiseCriticalHalfApproximable244 u t) :
    |velocityH3TransportDerivative3At u t| ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t +
      3 * lowNormalRealSchwartz_holder244CriticalConstant *
        Real.sqrt (Real.sqrt
          (velocityH3Energy0At u t * velocityH3Energy1At u t)) *
        velocityH3DissipationAt u t := by
  exact h3PathCanonical_thirdTransport_criticalHalf_of_approx244
    hH3 hClass ht (h3PathCanonical_slotwise_implies_approximable244
      u t hSlotwise)

end
end PrimeTensor.FirstMonomialTriad

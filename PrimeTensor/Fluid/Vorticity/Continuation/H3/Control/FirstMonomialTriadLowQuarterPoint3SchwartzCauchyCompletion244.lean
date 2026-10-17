import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzRootContinuity244
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# The signed 243-slot Schwartz monomial has a canonical Cauchy limit

The exact 243-slot real 2-4-4 perturbation estimate controls the *difference*
of two full signed monomials. Thus it also controls approximation sequences
without requiring that their limit be a Schwartz function.

Here each of the 243 nonnegative spatial error envelopes is assumed to be
uniformly small on a common late-time index pair, in the usual epsilon/Cauchy
sense. A finite-index argument gives a common cutoff for the ENTIRE signed
monomial. Completeness of the real numbers then produces a limit, rather than
requiring a fixed Schwartz target. Moreover, two Schwartz approximations
whose integrated cross-error tends to zero and whose monomials converge
cannot assign different numerical limits to the same Sobolev object.

The theorem does not assert that an arbitrary physical H3 or H4 velocity
has a sequence with this Cauchy property. Constructing such sequences by
Sobolev graph density, and identifying the physical trilinear pairing with
their limit, are genuinely separate analytic obligations.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSchwartzCauchy244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Standard finite-sum diagonalization: individually Cauchy-small scalar
errors have an arbitrarily small finite sum. No spatial dominated-convergence
hypothesis is being hidden in this lemma. -/
private theorem finite_real_slot_errors_cauchy_small244
    {J : Type*} [Fintype J]
    (E : ℕ → ℕ → J → ℝ)
    (hE : ∀ p : J, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n → E m n p < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
        (∑ p : J, E m n p) < ε := by
  classical
  have hs (s : Finset J) :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
          (∑ p ∈ s, E m n p) < ε := by
    induction s using Finset.induction_on with
    | empty =>
        intro ε hε
        refine ⟨0, ?_⟩
        intro m hm n hn
        simpa using hε
    | @insert p s hp ih =>
        intro ε hε
        have hHalf : 0 < ε / 2 := by positivity
        obtain ⟨N1, h1⟩ := hE p (ε / 2) hHalf
        obtain ⟨N2, h2⟩ := ih (ε / 2) hHalf
        refine ⟨max N1 N2, ?_⟩
        intro m hm n hn
        have hm1 : N1 ≤ m := le_trans (le_max_left N1 N2) hm
        have hn1 : N1 ≤ n := le_trans (le_max_left N1 N2) hn
        have hm2 : N2 ≤ m := le_trans (le_max_right N1 N2) hm
        have hn2 : N2 ≤ n := le_trans (le_max_right N1 N2) hn
        have hpSmall := h1 m hm1 n hn1
        have hsSmall := h2 m hm2 n hn2
        rw [Finset.sum_insert hp]
        linarith
  exact hs (Finset.univ : Finset J)

/-- Actual reference-free strong approximation criterion. Unlike a
hypothesis saying that the *monomial* is Cauchy, each of its 243 spatial
2-4-4 perturbation envelopes is required to vanish on common tails. -/
def Schwartz243SlotErrorCauchy244
    (f : ℕ → A3 → SchwartzMap V3 ℝ) : Prop :=
  ∀ p : SchwartzStrongJetSlots244, ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
      schwartzPhysicalSlotPerturbation244 (f m) (f n) p < ε

/-- The signed 243-slot monomial is Cauchy as a REAL sequence, without
postulating a fixed Schwartz limit. The pairing factor 2 is not lost. -/
theorem lowNormalRealSchwartz_firstMonomial_cauchy_of_slotErrors244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hError : Schwartz243SlotErrorCauchy244 f) :
    CauchySeq (fun n => lowNormalRealSchwartzPoint3Monomial (f n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hHalf : 0 < ε / 2 := by positivity
  obtain ⟨N, hN⟩ :=
    finite_real_slot_errors_cauchy_small244
      (fun m n p => schwartzPhysicalSlotPerturbation244 (f m) (f n) p)
      hError (ε / 2) hHalf
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [Real.dist_eq]
  have hSum := hN m hm n hn
  have hBound := lowNormalRealSchwartz_fullMonomial_integratedStability244
    (f m) (f n)
  exact lt_of_le_of_lt hBound (by linarith)

/-- Existence of a real-valued signed monomial on the Cauchy completion of
the Schwartz approximation class. This is an existence theorem for each
Cauchy approximating sequence, not yet a physical carrier identification. -/
theorem lowNormalRealSchwartz_firstMonomial_existsLimit_of_slotErrors244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hError : Schwartz243SlotErrorCauchy244 f) :
    ∃ M : ℝ,
      Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (f n))
        atTop (𝓝 M) :=
  cauchySeq_tendsto_of_complete
    (lowNormalRealSchwartz_firstMonomial_cauchy_of_slotErrors244 f hError)

/-- Two sequences approaching one another in the COMPLETE signed 243-slot
integrated error envelope have the same monomial limit. There is no need
for a Schwartz representative of that common limit. -/
theorem lowNormalRealSchwartz_firstMonomial_limits_eq_of_crossError244
    (f g : ℕ → A3 → SchwartzMap V3 ℝ)
    (M N : ℝ)
    (hf : Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (f n))
      atTop (𝓝 M))
    (hg : Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (g n))
      atTop (𝓝 N))
    (hCross : Tendsto (fun n =>
        2 * (∑ p : SchwartzStrongJetSlots244,
          schwartzPhysicalSlotPerturbation244 (f n) (g n) p))
      atTop (𝓝 0)) :
    M = N := by
  have hAbs :
      Tendsto (fun n =>
        |lowNormalRealSchwartzPoint3Monomial (f n) -
          lowNormalRealSchwartzPoint3Monomial (g n)|) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact abs_nonneg _
    · intro n
      exact lowNormalRealSchwartz_fullMonomial_integratedStability244
        (f n) (g n)
    · exact hCross
  have hDiff :
      Tendsto (fun n =>
        lowNormalRealSchwartzPoint3Monomial (f n) -
          lowNormalRealSchwartzPoint3Monomial (g n)) atTop
        (𝓝 (M - N)) := hf.sub hg
  have hZero :
      Tendsto (fun n =>
        lowNormalRealSchwartzPoint3Monomial (f n) -
          lowNormalRealSchwartzPoint3Monomial (g n)) atTop
        (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using hAbs
  have hMN : M - N = 0 := tendsto_nhds_unique hDiff hZero
  exact sub_eq_zero.mp hMN

end
end PrimeTensor.FirstMonomialTriad

import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalVariableSixOrbit244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSixSectorPairing244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealGlobalSixSectors244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadIntegralBound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadSixIntegral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Genuine Fourier-pair permutation changes of variables

On the conserving momentum plane `q = -(p+r)`, six ordered triples
correspond to the six maps of the independent physical Hilbert pair `(p,r)`:

  0 (p,r), 1 (r,p), 2 (q,r), 3 (r,q), 4 (q,p), 5 (p,q).

The existing `h3TriadPermutation` maps already generate all six from a
product swap and the previously proved middle-frequency involution. The
new, explicit reindexing identifies THEIR order with the positive coherent
Schwartz sectors. Each map preserves actual product Fourier Lebesgue volume. Consequently arbitrary integrable six-sector functions
can be reindexed on a single Fourier-pair domain, without a determinant,
a change of normalization or a sign assumption.

This module proves exactly the measure-theoretic permutation step. It does
not yet assert that the genuinely ordered Schwartz windows become one
common nonnegative product, nor that the windowed six-sector integral is
negative. Those are separate analytic obligations.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

private abbrev V3 := H3FourierPoint3
private abbrev PairV244 := V3 × V3
private abbrev Freq244 := PrimeTensor.Axis Depth.three → ℝ

-- The finite positive-depth axis instance is required by the Hilbert
-- Fourier carrier's metric and Haar/product-volume instances.  The
-- older triad integral modules install this instance locally too.
noncomputable local instance axisFintypePhysicalSixPermutation244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The older Schwartz six-orbit is enumerated `pqr,prq,qpr,qrp,rpq,rqp`.
The actual positive coherent sectors use `pqr,rqp,qpr,rpq,qrp,prq`.
This explicit bijection bridges those two *different* orders. -/
def thirdFullPositivePermutationReindex244 (n : Fin 6) : Fin 6 :=
  ![(0 : Fin 6), 5, 2, 4, 3, 1] n

/-- Reindex the ALREADY VERIFIED physical Hilbert-pair volume-preserving
permutations into the six *actual* positive Schwartz sectors. No new
Jacobian or measure equivalence is postulated. -/
def thirdFullPositivePairPermutationEquiv244 (n : Fin 6) :
    PairV244 ≃ᵐ PairV244 :=
  h3TriadPermutation (thirdFullPositivePermutationReindex244 n)

/-- The six actual positive-sector Fourier-pair permutations preserve
product volume, exactly, by the previously proved triad permutation theorem. -/
theorem thirdFullPositivePairPermutation_measurePreserving244 (n : Fin 6) :
    MeasurePreserving (thirdFullPositivePairPermutationEquiv244 n)
      (volume.prod volume) (volume.prod volume) := by
  exact h3TriadPermutation_preserving (thirdFullPositivePermutationReindex244 n)

/-- The permutation reindex is an involution, hence is a true bijection
between the old six-order convention and the positive-sector convention. -/
theorem thirdFullPositivePermutationReindex_involutive244 (n : Fin 6) :
    thirdFullPositivePermutationReindex244
      (thirdFullPositivePermutationReindex244 n) = n := by
  fin_cases n <;> decide

/-- Reordering the six old physical momentum permutations into the true
positive-sector enumeration does not alter any finite commutative sum. -/
theorem thirdFullPositivePermutationReindex_sum244
    {α : Type*} [AddCommMonoid α] (F : Fin 6 → α) :
    (∑ n : Fin 6, F (thirdFullPositivePermutationReindex244 n)) =
      ∑ n : Fin 6, F n := by
  -- The six summands are a permutation, not definitionally identical.
  -- `abel` proves the additive commutative-monoid equality after the
  -- concrete Fin-6 reindexing has been reduced.
  simp [Fin.sum_univ_succ, thirdFullPositivePermutationReindex244] <;> abel

/-- The legacy six-order Schwartz orbit and the newly indexed six actual
positive-sector changes are literally the same six physical terms.
No equal-sector-sign assumption is involved. -/
theorem thirdFullPositivePairPermutation_orbit_eq_existing244
    (K : PairV244 → ℂ) (z : PairV244) :
    (∑ n : Fin 6,
      K (thirdFullPositivePairPermutationEquiv244 n z)) =
      h3TriadSixOrbit K z := by
  unfold h3TriadSixOrbit thirdFullPositivePairPermutationEquiv244
  exact thirdFullPositivePermutationReindex_sum244
    (fun k => K (h3TriadPermutation k z))

/-- Integral reindexing for any of the six physical ordered momentum pairs.
No integrability assumptions are needed for the equality itself. -/
theorem thirdFullPositivePairPermutation_integral244
    (n : Fin 6) (f : PairV244 → ℝ) :
    (∫ z : PairV244, f (thirdFullPositivePairPermutationEquiv244 n z)
      ∂volume.prod volume) =
      ∫ z : PairV244, f z ∂volume.prod volume := by
  exact (thirdFullPositivePairPermutation_measurePreserving244 n).integral_comp
    (thirdFullPositivePairPermutationEquiv244 n).measurableEmbedding f

/-- Integrability is preserved by each true momentum-plane permutation. -/
theorem thirdFullPositivePairPermutation_integrable244
    (n : Fin 6) {f : PairV244 → ℝ}
    (hf : Integrable f (volume.prod volume)) :
    Integrable (fun z : PairV244 =>
      f (thirdFullPositivePairPermutationEquiv244 n z))
      (volume.prod volume) := by
  exact ((thirdFullPositivePairPermutation_measurePreserving244 n).integrable_comp
    hf.aestronglyMeasurable).mpr hf

/-- The same change of variables works for a measurable integration domain.
The domain is transported by the actual permutation preimage. -/
theorem thirdFullPositivePairPermutation_setIntegral244
    (n : Fin 6) (s : Set PairV244) (hs : MeasurableSet s)
    (f : PairV244 → ℝ) :
    (∫ z in (thirdFullPositivePairPermutationEquiv244 n) ⁻¹' s,
      f (thirdFullPositivePairPermutationEquiv244 n z)
        ∂volume.prod volume) =
      ∫ z in s, f z ∂volume.prod volume := by
  let e := thirdFullPositivePairPermutationEquiv244 n
  have hPre : MeasurableSet (e ⁻¹' s) := hs.preimage e.measurable
  calc
    _ = ∫ z : PairV244,
          (e ⁻¹' s).indicator (fun x => f (e x)) z
            ∂volume.prod volume := (integral_indicator hPre).symm
    _ = ∫ z : PairV244, (s.indicator f) (e z)
            ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : e z ∈ s
      · have hp : z ∈ e ⁻¹' s := hz
        simp only [Set.indicator_of_mem hp, Set.indicator_of_mem hz]
      · have hp : z ∉ e ⁻¹' s := hz
        simp only [Set.indicator_of_notMem hp, Set.indicator_of_notMem hz]
    _ = ∫ z : PairV244, s.indicator f z
            ∂volume.prod volume :=
      (thirdFullPositivePairPermutation_measurePreserving244 n).integral_comp
        e.measurableEmbedding (s.indicator f)
    _ = ∫ z in s, f z ∂volume.prod volume := integral_indicator hs

/-- ALL SIX potentially signed sector integrals can be transported onto
one common physical momentum-pair carrier. The integrands need not agree,
be positive, or be invariant under permutations. -/
theorem thirdFullPositivePairPermutation_six_integrals244
    (F : Fin 6 → PairV244 → ℝ)
    (hF : ∀ n : Fin 6, Integrable (F n) (volume.prod volume)) :
    (∑ n : Fin 6, ∫ z : PairV244, F n z ∂volume.prod volume) =
      ∫ z : PairV244,
        ∑ n : Fin 6, F n (thirdFullPositivePairPermutationEquiv244 n z)
        ∂volume.prod volume := by
  calc
    _ = ∑ n : Fin 6, ∫ z : PairV244,
          F n (thirdFullPositivePairPermutationEquiv244 n z)
            ∂volume.prod volume := by
      apply Finset.sum_congr rfl
      intro n _
      exact (thirdFullPositivePairPermutation_integral244 n (F n)).symm
    _ = _ := by
      symm
      exact integral_finset_sum (Finset.univ : Finset (Fin 6))
        (fun n _ => thirdFullPositivePairPermutation_integrable244 n (hF n))


/-- The exact sum of six positive-ball integrals of the ACTUAL full-third
real Schwartz Fourier kernel, transported onto one common Hilbert-pair
measure space. No integrability hypothesis is added: Schwartz regularity
already supplies it. The six windowed integrands are not yet combined. -/
theorem thirdFullPositiveSixBallIntegral_permutation_reindex244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (δ : ℝ) :
    thirdFullPositiveSixBallIntegral244 ρ hρ A B C δ =
      ∫ z : PairV244,
        ∑ n : Fin 6,
          (Metric.ball (thirdFullPositiveCoherentPair244 n) δ).indicator
            (fun x : PairV244 =>
              (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C x).im)
            (thirdFullPositivePairPermutationEquiv244 n z)
        ∂volume.prod volume := by
  let K : PairV244 → ℝ := fun z =>
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
  let F : Fin 6 → PairV244 → ℝ := fun n =>
    (Metric.ball (thirdFullPositiveCoherentPair244 n) δ).indicator K
  have hK : Integrable K (volume.prod volume) :=
    thirdFullAxisImagKernel_integrable_global244 ρ hρ A B C
  have hF (n : Fin 6) : Integrable (F n) (volume.prod volume) :=
    hK.indicator measurableSet_ball
  calc
    thirdFullPositiveSixBallIntegral244 ρ hρ A B C δ =
        ∑ n : Fin 6, ∫ z : PairV244, F n z ∂volume.prod volume := by
      unfold thirdFullPositiveSixBallIntegral244
      apply Finset.sum_congr rfl
      intro n _
      exact (integral_indicator measurableSet_ball).symm
    _ = ∫ z : PairV244,
        ∑ n : Fin 6, F n (thirdFullPositivePairPermutationEquiv244 n z)
          ∂volume.prod volume :=
      thirdFullPositivePairPermutation_six_integrals244 F hF
    _ = _ := rfl

end
end PrimeTensor.FirstMonomialTriad

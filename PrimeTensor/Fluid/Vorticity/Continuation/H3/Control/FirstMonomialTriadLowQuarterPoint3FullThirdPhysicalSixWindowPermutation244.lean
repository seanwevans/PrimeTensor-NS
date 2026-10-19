import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSixPermutationMeasure244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSectorWindowFactor244
import Mathlib.Tactic

/-!
# A common actual three-window scalar under all six positive pair permutations

The six real positive coherent Schwartz sectors have DIFFERENT ordered pairs
of Fourier frequencies and a distinct ordered assignment of their three
scalar compact windows. The already proved six Hilbert momentum-pair
permutations preserve product volume. Here their action on the *actual*
three-window factor is identified pointwise with one reference product.

No sign is assigned to any ordered physical coefficient. Consequently the
six weighted sector integrals can be rewritten as one common scalar window
factor multiplying a sum of six transported, generally signed coefficients.
The coefficients are not yet identified pointwise with the six-orbit physical
polynomial on the zero-Fourier-mass set; that is a separate obligation.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev V3 := H3FourierPoint3
private abbrev PairV244 := V3 × V3

noncomputable local instance axisFintypeSixWindowPermutation244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- A fixed, actual Schwartz product with center labels `0,1,2` attached
respectively to the physical frequencies `p,q,r` (`q=-p-r`). -/
noncomputable def thirdFullPositiveCommonThreeWindow244
    (ρ : ℝ) (hρ : 0 < ρ) (z : PairV244) : ℝ :=
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  (thirdFullAxisWindowBump244 ρ hρ 0 : Freq244 → ℝ) p *
    (thirdFullAxisWindowBump244 ρ hρ 1 : Freq244 → ℝ) q *
    (thirdFullAxisWindowBump244 ρ hρ 2 : Freq244 → ℝ) r

/-- The six actual *Hilbert* pair maps in the exact positive coherent-sector
order `(p,r), (r,p), (q,r), (r,q), (q,p), (p,q)`.
They are not additional measure maps: they are evaluations of the already
proved `thirdFullPositivePairPermutationEquiv244`. -/
theorem thirdFullPositivePairPermutation_explicit244
    (n : Fin 6) (z : PairV244) :
    thirdFullPositivePairPermutationEquiv244 n z =
      match n.val with
      | 0 => (z.1, z.2)
      | 1 => (z.2, z.1)
      | 2 => (-(z.1 + z.2), z.2)
      | 3 => (z.2, -(z.1 + z.2))
      | 4 => (-(z.1 + z.2), z.1)
      | _ => (z.1, -(z.1 + z.2)) := by
  -- The two nontrivial composite maps carry a private product swap.
  -- `simp` does not unfold that private equivalence.  `change` exposes
  -- its definitionally equal pair action before additive normalization.
  fin_cases n
  · rfl
  · rfl
  · change (-(z.1 + z.2), -(-(z.1 + z.2) + z.1)) =
        (-(z.1 + z.2), z.2)
    apply Prod.ext
    · rfl
    · dsimp
      abel
  · change (z.2, -(z.2 + z.1)) = (z.2, -(z.1 + z.2))
    apply Prod.ext
    · rfl
    · dsimp
      abel
  · rfl
  · rfl

/-- The three dependent-middle identities needed for the reordered actual
Schwartz windows. They are conservation laws, not symmetry assumptions. -/
private theorem thirdFullPositiveWindowMiddle_qr244 (z : PairV244) :
    thirdFullMiddleFrequency244
      (WithLp.ofLp (-(z.1 + z.2)), WithLp.ofLp z.2) =
        WithLp.ofLp z.1 := by
  funext i
  simp only [thirdFullMiddleFrequency244, WithLp.ofLp_neg,
    WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]
  ring

private theorem thirdFullPositiveWindowMiddle_rq244 (z : PairV244) :
    thirdFullMiddleFrequency244
      (WithLp.ofLp z.2, WithLp.ofLp (-(z.1 + z.2))) =
        WithLp.ofLp z.1 := by
  funext i
  simp only [thirdFullMiddleFrequency244, WithLp.ofLp_neg,
    WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]
  ring

private theorem thirdFullPositiveWindowMiddle_qp244 (z : PairV244) :
    thirdFullMiddleFrequency244
      (WithLp.ofLp (-(z.1 + z.2)), WithLp.ofLp z.1) =
        WithLp.ofLp z.2 := by
  funext i
  simp only [thirdFullMiddleFrequency244, WithLp.ofLp_neg,
    WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]
  ring

private theorem thirdFullPositiveWindowMiddle_pq244 (z : PairV244) :
    thirdFullMiddleFrequency244
      (WithLp.ofLp z.1, WithLp.ofLp (-(z.1 + z.2))) =
        WithLp.ofLp z.2 := by
  funext i
  simp only [thirdFullMiddleFrequency244, WithLp.ofLp_neg,
    WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]
  ring

private theorem thirdFullPositiveWindowMiddle_rp244 (z : PairV244) :
    thirdFullMiddleFrequency244
      (WithLp.ofLp z.2, WithLp.ofLp z.1) =
    thirdFullMiddleFrequency244
      (WithLp.ofLp z.1, WithLp.ofLp z.2) := by
  funext i
  dsimp [thirdFullMiddleFrequency244]
  ring

/-- The REAL three-cutoff factor of EVERY actual positive Schwartz sector,
after the correctly reindexed volume-preserving pair permutation, is the
same reference scalar product. This statement holds at EVERY frequency,
including points where one or more cutoffs vanish. -/
theorem thirdFullPositiveSectorWindowProduct_permuted244
    (ρ : ℝ) (hρ : 0 < ρ) (n : Fin 6) (z : PairV244) :
    thirdFullPositiveSectorWindowProduct244 ρ hρ n
      (thirdFullPositivePairPermutationEquiv244 n z) =
        thirdFullPositiveCommonThreeWindow244 ρ hρ z := by
  -- The three actual Schwartz bumps stay opaque. Only their sector labels
  -- and the six momentum-pair permutations are unfolded. `change` forces
  -- the finite `match` expressions to compute *before* ring normalization.
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let qh : Freq244 := WithLp.ofLp (-(z.1 + z.2))
  let w0 : Freq244 → ℝ :=
    (thirdFullAxisWindowBump244 ρ hρ 0 : Freq244 → ℝ)
  let w1 : Freq244 → ℝ :=
    (thirdFullAxisWindowBump244 ρ hρ 1 : Freq244 → ℝ)
  let w2 : Freq244 → ℝ :=
    (thirdFullAxisWindowBump244 ρ hρ 2 : Freq244 → ℝ)
  have hq : qh = q := by
    exact (thirdFullMiddleFrequency_ofLp_pair244 z).symm
  have hrp : thirdFullMiddleFrequency244 (r, p) = q :=
    thirdFullPositiveWindowMiddle_rp244 z
  have hqr : thirdFullMiddleFrequency244 (qh, r) = p :=
    thirdFullPositiveWindowMiddle_qr244 z
  have hrq : thirdFullMiddleFrequency244 (r, qh) = p :=
    thirdFullPositiveWindowMiddle_rq244 z
  have hqp : thirdFullMiddleFrequency244 (qh, p) = r :=
    thirdFullPositiveWindowMiddle_qp244 z
  have hpq : thirdFullMiddleFrequency244 (p, qh) = r :=
    thirdFullPositiveWindowMiddle_pq244 z
  rw [thirdFullPositivePairPermutation_explicit244 n z]
  fin_cases n
  · change w0 p * w1 q * w2 r = w0 p * w1 q * w2 r
    rfl
  · change w2 r * w1 (thirdFullMiddleFrequency244 (r, p)) * w0 p =
        w0 p * w1 q * w2 r
    rw [hrp]
    ring
  · change w1 qh * w0 (thirdFullMiddleFrequency244 (qh, r)) * w2 r =
        w0 p * w1 q * w2 r
    rw [hqr, hq]
    ring
  · change w2 r * w0 (thirdFullMiddleFrequency244 (r, qh)) * w1 qh =
        w0 p * w1 q * w2 r
    rw [hrq, hq]
    ring
  · change w1 qh * w2 (thirdFullMiddleFrequency244 (qh, p)) * w0 p =
        w0 p * w1 q * w2 r
    rw [hqp, hq]
    ring
  · change w0 p * w2 (thirdFullMiddleFrequency244 (p, qh)) * w1 qh =
        w0 p * w1 q * w2 r
    rw [hpq, hq]
    ring

/-- The reference is genuinely the original sector-0 three-Schwartz-window
product; there is no invented scalar weight or new normalization. -/
theorem thirdFullPositiveCommonThreeWindow_eq_sector_zero244
    (ρ : ℝ) (hρ : 0 < ρ) (z : PairV244) :
    thirdFullPositiveCommonThreeWindow244 ρ hρ z =
      thirdFullPositiveSectorWindowProduct244 ρ hρ 0 z := by
  rfl

/-- Six *separately signed* weighted coefficients, integrated over the
original actual Fourier-pair carrier, can be combined into one common
scalar Schwartz weight times their transported six-order sum. -/
theorem thirdFullPositiveSixWindowWeighted_integral244
    (ρ : ℝ) (hρ : 0 < ρ) (G : Fin 6 → PairV244 → ℝ)
    (hInt : ∀ n : Fin 6,
      Integrable (fun z : PairV244 =>
        thirdFullPositiveSectorWindowProduct244 ρ hρ n z * G n z)
        (volume.prod volume)) :
    (∑ n : Fin 6, ∫ z : PairV244,
      thirdFullPositiveSectorWindowProduct244 ρ hρ n z * G n z
        ∂volume.prod volume) =
      ∫ z : PairV244,
        thirdFullPositiveCommonThreeWindow244 ρ hρ z *
          (∑ n : Fin 6,
            G n (thirdFullPositivePairPermutationEquiv244 n z))
        ∂volume.prod volume := by
  let F : Fin 6 → PairV244 → ℝ := fun n z =>
    thirdFullPositiveSectorWindowProduct244 ρ hρ n z * G n z
  calc
    _ = ∫ z : PairV244,
        ∑ n : Fin 6, F n (thirdFullPositivePairPermutationEquiv244 n z)
          ∂volume.prod volume :=
      thirdFullPositivePairPermutation_six_integrals244 F hInt
    _ = ∫ z : PairV244,
        thirdFullPositiveCommonThreeWindow244 ρ hρ z *
          (∑ n : Fin 6,
            G n (thirdFullPositivePairPermutationEquiv244 n z))
          ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [F]
      simp_rw [thirdFullPositiveSectorWindowProduct_permuted244]
      rw [Finset.mul_sum]

end
end PrimeTensor.FirstMonomialTriad

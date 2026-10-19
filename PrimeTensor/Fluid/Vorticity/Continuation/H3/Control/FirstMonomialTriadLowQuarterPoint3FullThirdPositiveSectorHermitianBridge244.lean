import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSixTransportedCore244
import Mathlib.Tactic

/-!
# Exact positive-sector to projected Hermitian six-orbit bridge

Each of the six genuine window-free physical coefficients uses the original
three transverse germs with a different frequency/label ordering.  The
existing physical six-orbit uses a different order of those same six terms.
This module identifies the two expressions at every Fourier-pair frequency,
including points of zero Fourier mass.  Combined with the previously proved
common Schwartz window identity, it gives the genuine pointwise polynomial
factorization through the negative projected Hermitian orbit.

No sign is inferred for the entire global Fourier integral: restricting the
actual density to its correct support and proving positivity of the window
on a non-null region remain separate analytic obligations.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev PairV244 := H3FourierPoint3 × H3FourierPoint3

noncomputable local instance axisFintypePositiveHermitianBridge244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The six transported actual corrected terms equal precisely the six
permutations of ONE assignment of the three moving solenoidal germs. -/
theorem thirdFullPositiveTransportedCorrected_eq_singlePhysicalSix244
    (A B C : Freq244) (z : PairV244) :
    thirdFullPositivePhysicalSixTransportedCorrected244 A B C z =
      thirdFullPhysicalSixSymbol244
        (WithLp.ofLp z.1)
        (thirdFullMiddleFrequency244 (WithLp.ofLp z.1, WithLp.ofLp z.2))
        (WithLp.ofLp z.2)
        (thirdFullFixedCenterTransverseGerm244
          (thirdFullAxisSixCenter244 0) (WithLp.ofLp z.1) A)
        (thirdFullFixedCenterTransverseGerm244
          (thirdFullAxisSixCenter244 1)
          (thirdFullMiddleFrequency244 (WithLp.ofLp z.1, WithLp.ofLp z.2)) B)
        (thirdFullFixedCenterTransverseGerm244
          (thirdFullAxisSixCenter244 2) (WithLp.ofLp z.2) C) := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let qh : Freq244 := WithLp.ofLp (-(z.1 + z.2))
  let U : Freq244 := thirdFullFixedCenterTransverseGerm244
    (thirdFullAxisSixCenter244 0) p A
  let V : Freq244 := thirdFullFixedCenterTransverseGerm244
    (thirdFullAxisSixCenter244 1) q B
  let W : Freq244 := thirdFullFixedCenterTransverseGerm244
    (thirdFullAxisSixCenter244 2) r C
  have hq : qh = q := (thirdFullMiddleFrequency_ofLp_pair244 z).symm
  have hrp : thirdFullMiddleFrequency244 (r, p) = q := by
    funext i
    dsimp [q, p, r, thirdFullMiddleFrequency244]
    ring
  -- Rewrite the *named* dependent Fourier momentum before ring
  -- normalization.  Without `hq`, `ring` treats `qh i` as independent
  -- of `p i` and `r i`, which is why the old four proofs stalled.
  have hqr : thirdFullMiddleFrequency244 (qh, r) = p := by
    rw [hq]
    funext i
    dsimp [q, thirdFullMiddleFrequency244]
    ring
  have hrq : thirdFullMiddleFrequency244 (r, qh) = p := by
    rw [hq]
    funext i
    dsimp [q, thirdFullMiddleFrequency244]
    ring
  have hqp : thirdFullMiddleFrequency244 (qh, p) = r := by
    rw [hq]
    funext i
    dsimp [q, thirdFullMiddleFrequency244]
    ring
  have hpq : thirdFullMiddleFrequency244 (p, qh) = r := by
    rw [hq]
    funext i
    dsimp [q, thirdFullMiddleFrequency244]
    ring
  let T : Fin 6 → ℝ := fun n =>
    let w := thirdFullPositivePairPermutationEquiv244 n z
    let x : Freq244 := WithLp.ofLp w.1
    let v : Freq244 := WithLp.ofLp w.2
    let y : Freq244 := thirdFullMiddleFrequency244 (x, v)
    let labels := lowNormalQuarterCoherentLabelPair false n
    let middle := thirdFullPositiveMiddleLabel244 n
    let X := thirdFullPositiveSectorBareGerm244 A B C labels.1 x
    let Y := thirdFullPositiveSectorBareGerm244 A B C middle y
    let Z := thirdFullPositiveSectorBareGerm244 A B C labels.2 v
    thirdFullPhysicalOrderedSymbol244 x y v X Y Z
  have h0 : T 0 =
      thirdFullPhysicalOrderedSymbol244 p q r U V W := by
    dsimp only [T]
    rw [thirdFullPositivePairPermutation_explicit244 (0 : Fin 6) z]
    change thirdFullPhysicalOrderedSymbol244
      p q r
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 0) p A)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 1) q B)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 2) r C) = _
    rfl
  have h1 : T 1 =
      thirdFullPhysicalOrderedSymbol244 r q p W V U := by
    dsimp only [T]
    rw [thirdFullPositivePairPermutation_explicit244 (1 : Fin 6) z]
    change thirdFullPhysicalOrderedSymbol244
      r (thirdFullMiddleFrequency244 (r, p)) p
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 2) r C)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 1) (thirdFullMiddleFrequency244 (r, p)) B)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 0) p A) = _
    rw [hrp]
  have h2 : T 2 =
      thirdFullPhysicalOrderedSymbol244 q p r V U W := by
    dsimp only [T]
    rw [thirdFullPositivePairPermutation_explicit244 (2 : Fin 6) z]
    change thirdFullPhysicalOrderedSymbol244
      qh (thirdFullMiddleFrequency244 (qh, r)) r
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 1) qh B)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 0) (thirdFullMiddleFrequency244 (qh, r)) A)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 2) r C) = _
    rw [hqr]
    rw [hq]
  have h3 : T 3 =
      thirdFullPhysicalOrderedSymbol244 r p q W U V := by
    dsimp only [T]
    rw [thirdFullPositivePairPermutation_explicit244 (3 : Fin 6) z]
    change thirdFullPhysicalOrderedSymbol244
      r (thirdFullMiddleFrequency244 (r, qh)) qh
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 2) r C)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 0) (thirdFullMiddleFrequency244 (r, qh)) A)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 1) qh B) = _
    rw [hrq]
    rw [hq]
  have h4 : T 4 =
      thirdFullPhysicalOrderedSymbol244 q r p V W U := by
    dsimp only [T]
    rw [thirdFullPositivePairPermutation_explicit244 (4 : Fin 6) z]
    change thirdFullPhysicalOrderedSymbol244
      qh (thirdFullMiddleFrequency244 (qh, p)) p
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 1) qh B)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 2) (thirdFullMiddleFrequency244 (qh, p)) C)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 0) p A) = _
    rw [hqp]
    rw [hq]
  have h5 : T 5 =
      thirdFullPhysicalOrderedSymbol244 p r q U W V := by
    dsimp only [T]
    rw [thirdFullPositivePairPermutation_explicit244 (5 : Fin 6) z]
    change thirdFullPhysicalOrderedSymbol244
      p (thirdFullMiddleFrequency244 (p, qh)) qh
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 0) p A)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 2) (thirdFullMiddleFrequency244 (p, qh)) C)
      (thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 1) qh B) = _
    rw [hpq]
    rw [hq]
  calc
    thirdFullPositivePhysicalSixTransportedCorrected244 A B C z =
        ∑ n : Fin 6, T n := by rfl
    _ = T 0 + T 1 + T 2 + T 3 + T 4 + T 5 := by
      -- `Fin.sum_univ_succ` introduces *five different dependent* `Fin.succ`
      -- terms. Unlike `change` or `ring`, rewriting the concrete Fin-index
      -- equalities eliminates each application of `T` at a successor index.
      -- All equalities below are closed by kernel computation (`decide`).
      have hs1 : (Fin.succ (0 : Fin 5) : Fin 6) = 1 := by decide
      have hs2 : (Fin.succ (Fin.succ (0 : Fin 4)) : Fin 6) = 2 := by decide
      have hs3 : (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))) : Fin 6) = 3 := by decide
      have hs4 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))) : Fin 6) = 4 := by decide
      have hs5 : (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))) : Fin 6) = 5 := by decide
      -- After the six successors there is an empty `Fin 0` residual sum.
      -- Explicitly discharge it before normalizing the six real terms.
      simp only [Fin.sum_univ_succ, Finset.univ_eq_empty,
        Finset.sum_empty, add_zero, hs1, hs2, hs3, hs4, hs5] <;> abel
    _ = thirdFullPhysicalSixSymbol244 p q r U V W := by
      rw [h0, h1, h2, h3, h4, h5]
      unfold thirdFullPhysicalSixSymbol244
      abel

/-- The TRUE transported five-index cores coincide, without sector-support
or nonzero-mass assumptions, with the negative-capable projected Hermitian
six-orbit using the fixed original sharp centers 0,1,2. -/
theorem thirdFullPositivePhysicalSixTransportedCore_eq_projectedHermitian244
    (A B C : Freq244) (z : PairV244) :
    thirdFullPositivePhysicalSixTransportedCore244 A B C z =
      thirdFullProjectedHermitianKernel244
        (thirdFullAxisSixCenter244 0)
        (thirdFullAxisSixCenter244 1)
        (thirdFullAxisSixCenter244 2) A B C
        (WithLp.ofLp z.1, WithLp.ofLp z.2) := by
  rw [thirdFullPositivePhysicalSixTransportedCore_eq_twice_corrected244,
    thirdFullPositiveTransportedCorrected_eq_singlePhysicalSix244]
  unfold thirdFullProjectedHermitianKernel244
  rw [thirdFullHermitianMomentumKernel_eq244]

/-- A common REAL Schwartz cutoff times the exact projected Hermitian
six-orbit.  Unlike separate signed sector estimates, this is one pointwise
symmetrized identity valid even where the Fourier window vanishes. -/
theorem thirdFullPositivePhysicalSixPolynomials_eq_window_hermitian244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) :
    (∑ n : Fin 6,
      thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n
        (thirdFullPositivePairPermutationEquiv244 n z)) =
      thirdFullPositiveCommonThreeWindow244 ρ hρ z *
        thirdFullProjectedHermitianKernel244
          (thirdFullAxisSixCenter244 0)
          (thirdFullAxisSixCenter244 1)
          (thirdFullAxisSixCenter244 2) A B C
          (WithLp.ofLp z.1, WithLp.ofLp z.2) := by
  rw [thirdFullPositivePhysicalSixPolynomials_common_window244,
    thirdFullPositivePhysicalSixTransportedCore_eq_projectedHermitian244]

/-- Integration of the exact common window times the projected Hermitian
kernel, conditional only on the separately labeled physical-polynomial
integrability already explicit in the preceding module. -/
theorem thirdFullPositivePhysicalSixPolynomialIntegrals_hermitian244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (hInt : ∀ n : Fin 6,
      Integrable (thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n)
        (volume.prod volume)) :
    (∑ n : Fin 6,
      ∫ z : PairV244,
        thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
        ∂volume.prod volume) =
      ∫ z : PairV244,
        thirdFullPositiveCommonThreeWindow244 ρ hρ z *
          thirdFullProjectedHermitianKernel244
            (thirdFullAxisSixCenter244 0)
            (thirdFullAxisSixCenter244 1)
            (thirdFullAxisSixCenter244 2) A B C
            (WithLp.ofLp z.1, WithLp.ofLp z.2)
        ∂volume.prod volume := by
  calc
    _ = ∫ z : PairV244,
          thirdFullPositiveCommonThreeWindow244 ρ hρ z *
            (2 * thirdFullPositivePhysicalSixTransportedCorrected244 A B C z)
          ∂volume.prod volume :=
      thirdFullPositivePhysicalSixPolynomialIntegrals_corrected244 ρ hρ A B C hInt
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [← thirdFullPositivePhysicalSixTransportedCore_eq_twice_corrected244,
        thirdFullPositivePhysicalSixTransportedCore_eq_projectedHermitian244]

end
end PrimeTensor.FirstMonomialTriad

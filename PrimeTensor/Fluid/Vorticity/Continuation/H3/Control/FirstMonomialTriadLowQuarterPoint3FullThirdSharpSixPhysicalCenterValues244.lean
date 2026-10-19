import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSharpFiveIndexContraction244
import Mathlib.Tactic

/-!
# Six actual five-index sharp physical coefficients

The previous module proves, without an auxiliary sharp-symbol substitution,
that the complete physical five-index H3 gradient plus the genuine 3+2+2
interpolation core equals twice the corrected ordered triad symbol. Here the
physical coefficient is evaluated at the six explicit sharp solenoidal
orders, using the already audited corrected values (-16, 28, 33, -81,
-60, 0). The positive coherent-sector ordering is (p,q,r), (r,q,p),
(q,p,r), (r,p,q), (q,r,p), (p,r,q), so the six coefficients are
(-32,0,66,-120,-162,56), summing to -192.

Every sharp ordered value here is the actual *five-index* physical core
at the corresponding Hilbert frequency pair, not just a bare symbol.
No sign of any Fourier-window integral is inferred from these center values.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ

noncomputable local instance axisFintypeSixCenterValues244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Evaluate the genuine gradient/interpolation sharp core at the Hilbert
pair of its first and third frequencies; the supplied middle frequency is
not silently replaced by any auxiliary or unconstrained vector. -/
noncomputable def thirdFullSharpPhysicalOrderedAt244
    (p q r U V W : Freq244) : ℝ :=
  thirdFullSharpPhysicalOrderedCore244
    (WithLp.toLp 2 p, WithLp.toLp 2 r) p q r U V W

/-- The committed five-index contraction applies to an honest conserving
sharp momentum triple after transporting p and r into the Hilbert carrier. -/
theorem thirdFullSharpPhysicalOrderedAt_twice_corrected244
    (p q r U V W : Freq244)
    (hMomentum : ∀ i : A3, p i + q i + r i = 0) :
    thirdFullSharpPhysicalOrderedAt244 p q r U V W =
      2 * thirdFullPhysicalOrderedSymbol244 p q r U V W := by
  unfold thirdFullSharpPhysicalOrderedAt244
  have hq :
      WithLp.ofLp (-(WithLp.toLp 2 p + WithLp.toLp 2 r)) = q := by
    have ht := (thirdFullMiddleFrequency_ofLp_pair244
      (WithLp.toLp 2 p, WithLp.toLp 2 r)).symm
    simp only [WithLp.ofLp_toLp] at ht
    rw [ht]
    funext i
    have hm := hMomentum i
    dsimp [thirdFullMiddleFrequency244]
    linarith
  exact thirdFullSharpPhysicalOrderedCore_eq_twice_corrected244
    (WithLp.toLp 2 p, WithLp.toLp 2 r) p q r U V W
    (by simp only [WithLp.ofLp_toLp]) hq
    (by simp only [WithLp.ofLp_toLp])

/-- These values come from all five physical derivative-axis sums, through
the proved core-to-symbol contraction. Their order agrees with the six
positive coherent sector labels, not the original symbolic-orbit list. -/
theorem thirdFullSharpPhysicalSixOrdered_values244 :
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpP244 thirdFullSharpQ244 thirdFullSharpR244
      thirdFullSharpA244 thirdFullSharpB244 thirdFullSharpC244 = -32 ∧
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpR244 thirdFullSharpQ244 thirdFullSharpP244
      thirdFullSharpC244 thirdFullSharpB244 thirdFullSharpA244 = 0 ∧
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpQ244 thirdFullSharpP244 thirdFullSharpR244
      thirdFullSharpB244 thirdFullSharpA244 thirdFullSharpC244 = 66 ∧
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpR244 thirdFullSharpP244 thirdFullSharpQ244
      thirdFullSharpC244 thirdFullSharpA244 thirdFullSharpB244 = -120 ∧
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpQ244 thirdFullSharpR244 thirdFullSharpP244
      thirdFullSharpB244 thirdFullSharpC244 thirdFullSharpA244 = -162 ∧
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpP244 thirdFullSharpR244 thirdFullSharpQ244
      thirdFullSharpA244 thirdFullSharpC244 thirdFullSharpB244 = 56 := by
  have hMom : ∀ i : A3,
      thirdFullSharpP244 i + thirdFullSharpQ244 i +
        thirdFullSharpR244 i = 0 := by
    exact (thirdFullPhysicalTriad_solenoidal244).1
  have hRQP : ∀ i : A3,
      thirdFullSharpR244 i + thirdFullSharpQ244 i +
        thirdFullSharpP244 i = 0 := by
    intro i
    have hm := hMom i
    linarith
  have hQPR : ∀ i : A3,
      thirdFullSharpQ244 i + thirdFullSharpP244 i +
        thirdFullSharpR244 i = 0 := by
    intro i
    have hm := hMom i
    linarith
  have hRPQ : ∀ i : A3,
      thirdFullSharpR244 i + thirdFullSharpP244 i +
        thirdFullSharpQ244 i = 0 := by
    intro i
    have hm := hMom i
    linarith
  have hQRP : ∀ i : A3,
      thirdFullSharpQ244 i + thirdFullSharpR244 i +
        thirdFullSharpP244 i = 0 := by
    intro i
    have hm := hMom i
    linarith
  have hPRQ : ∀ i : A3,
      thirdFullSharpP244 i + thirdFullSharpR244 i +
        thirdFullSharpQ244 i = 0 := by
    intro i
    have hm := hMom i
    linarith
  -- The private witness functions in the older corrected-orbit theorem
  -- and the explicit sharp coordinate functions are definitionally equal:
  -- they use exactly the same three axisRank coordinate branches.
  have hValues := thirdFullPhysicalSix_each_corrected244
  change
    thirdFullPhysicalOrderedSymbol244
      thirdFullSharpP244 thirdFullSharpQ244 thirdFullSharpR244
      thirdFullSharpA244 thirdFullSharpB244 thirdFullSharpC244 = -16 ∧
    thirdFullPhysicalOrderedSymbol244
      thirdFullSharpP244 thirdFullSharpR244 thirdFullSharpQ244
      thirdFullSharpA244 thirdFullSharpC244 thirdFullSharpB244 = 28 ∧
    thirdFullPhysicalOrderedSymbol244
      thirdFullSharpQ244 thirdFullSharpP244 thirdFullSharpR244
      thirdFullSharpB244 thirdFullSharpA244 thirdFullSharpC244 = 33 ∧
    thirdFullPhysicalOrderedSymbol244
      thirdFullSharpQ244 thirdFullSharpR244 thirdFullSharpP244
      thirdFullSharpB244 thirdFullSharpC244 thirdFullSharpA244 = -81 ∧
    thirdFullPhysicalOrderedSymbol244
      thirdFullSharpR244 thirdFullSharpP244 thirdFullSharpQ244
      thirdFullSharpC244 thirdFullSharpA244 thirdFullSharpB244 = -60 ∧
    thirdFullPhysicalOrderedSymbol244
      thirdFullSharpR244 thirdFullSharpQ244 thirdFullSharpP244
      thirdFullSharpC244 thirdFullSharpB244 thirdFullSharpA244 = 0 at hValues
  rcases hValues with ⟨h0,hPRQ0,hQPR0,hQRP0,hRPQ0,hRQP0⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [thirdFullSharpPhysicalOrderedAt_twice_corrected244
      _ _ _ _ _ _ hMom, h0]
    norm_num
  · rw [thirdFullSharpPhysicalOrderedAt_twice_corrected244
      _ _ _ _ _ _ hRQP, hRQP0]
    norm_num
  · rw [thirdFullSharpPhysicalOrderedAt_twice_corrected244
      _ _ _ _ _ _ hQPR, hQPR0]
    norm_num
  · rw [thirdFullSharpPhysicalOrderedAt_twice_corrected244
      _ _ _ _ _ _ hRPQ, hRPQ0]
    norm_num
  · rw [thirdFullSharpPhysicalOrderedAt_twice_corrected244
      _ _ _ _ _ _ hQRP, hQRP0]
    norm_num
  · rw [thirdFullSharpPhysicalOrderedAt_twice_corrected244
      _ _ _ _ _ _ hPRQ, hPRQ0]
    norm_num

/-- Exact -192 sum of the six PHYSICAL five-index sharp cores, not only
of an earlier symbolic-orbit model. The six values are not each negative. -/
theorem thirdFullSharpPhysicalSixOrdered_sum_neg192244 :
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpP244 thirdFullSharpQ244 thirdFullSharpR244
      thirdFullSharpA244 thirdFullSharpB244 thirdFullSharpC244 +
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpR244 thirdFullSharpQ244 thirdFullSharpP244
      thirdFullSharpC244 thirdFullSharpB244 thirdFullSharpA244 +
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpQ244 thirdFullSharpP244 thirdFullSharpR244
      thirdFullSharpB244 thirdFullSharpA244 thirdFullSharpC244 +
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpR244 thirdFullSharpP244 thirdFullSharpQ244
      thirdFullSharpC244 thirdFullSharpA244 thirdFullSharpB244 +
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpQ244 thirdFullSharpR244 thirdFullSharpP244
      thirdFullSharpB244 thirdFullSharpC244 thirdFullSharpA244 +
    thirdFullSharpPhysicalOrderedAt244
      thirdFullSharpP244 thirdFullSharpR244 thirdFullSharpQ244
      thirdFullSharpA244 thirdFullSharpC244 thirdFullSharpB244 = -192 := by
  rcases thirdFullSharpPhysicalSixOrdered_values244 with
    ⟨h0,h1,h2,h3,h4,h5⟩
  rw [h0,h1,h2,h3,h4,h5]
  norm_num


/-- The actual cutoff-free sector polynomial evaluated at the Hilbert sharp
center is the matching honest five-index ordered core. The only remaining
hypotheses are the already identified sharp transverse-germ conditions;
no spectral windows or auxiliary finite-order substitutions occur. -/
theorem thirdFullPositiveSectorPhysicalCore_sharpPair_eq_orderedAt244
    (A B C : Freq244) (n : Fin 6)
    (hTrans : ∀ i : Fin 6, (i = 0 ∨ i = 1 ∨ i = 2) →
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullPositiveWindowPolarization244 A B C i) = 0)
    (hNonzero : ∀ i : Fin 6,
      thirdTriadAxisDot244 (thirdFullAxisSixCenter244 i)
        (thirdFullAxisSixCenter244 i) ≠ 0) :
    thirdFullPositiveSectorPhysicalCore244 A B C n
      (thirdFullPositiveCoherentPair244 n) =
      thirdFullSharpPhysicalOrderedAt244
        (thirdFullAxisSixCenter244
          (lowNormalQuarterCoherentLabelPair false n).1)
        (thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n))
        (thirdFullAxisSixCenter244
          (lowNormalQuarterCoherentLabelPair false n).2)
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).1)
        (thirdFullPositiveWindowPolarization244 A B C
          (thirdFullPositiveMiddleLabel244 n))
        (thirdFullPositiveWindowPolarization244 A B C
          (lowNormalQuarterCoherentLabelPair false n).2) := by
  have hp : WithLp.ofLp (thirdFullPositiveCoherentPair244 n).1 =
      thirdFullAxisSixCenter244
        (lowNormalQuarterCoherentLabelPair false n).1 := by
    simp only [thirdFullPositiveCoherentPair244, WithLp.ofLp_toLp]
  have hr : WithLp.ofLp (thirdFullPositiveCoherentPair244 n).2 =
      thirdFullAxisSixCenter244
        (lowNormalQuarterCoherentLabelPair false n).2 := by
    simp only [thirdFullPositiveCoherentPair244, WithLp.ofLp_toLp]
  have hq := thirdFullPositiveSector_center_resonance244 n
  rw [thirdFullPositiveSectorPhysicalCore_center_eq_twice_corrected244
    A B C n (thirdFullPositiveCoherentPair244 n)
      hp hr hq hTrans hNonzero]
  symm
  apply thirdFullSharpPhysicalOrderedAt_twice_corrected244
  intro i
  have hi := congrArg (fun f : Freq244 => f i) hq
  dsimp [thirdFullMiddleFrequency244] at hi
  linarith

end
end PrimeTensor.FirstMonomialTriad
